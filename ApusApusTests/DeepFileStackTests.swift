import Foundation
import Testing
import SwiftParser
import SwiftSyntax

/// Whole-file pipeline on a SMALL stack (TODO.md / Make whole-file parsing crash-free and crawlable).
///
/// On 2026-09-25 the swift-syntax corpus died with "Thread stack size exceeded" inside the recursive
/// Oracle walk on a Swift Testing worker thread. The probe's main thread has 8 MB and never showed it,
/// so this suite reproduces the worker's 512 KB explicitly: each file runs parse → Oracle →
/// DerivationBuilder → converter on its own `Thread` with that stack size. A regression crashes the
/// test process (it cannot be caught), which is the signal. Opt-in like the other source-file suites.
@Suite("Whole files on a 512 KB stack",
       .enabled(if: SourceFileCorpus.enabled, "opt-in and slow: set APUS_SOURCE_FILE_SUITES=1"))
struct DeepFileStackTests {
    /// The files that crashed on 2026-09-25, plus the largest generated sources.
    static let files = [
        "SwiftBasicFormat/BasicFormat.swift",
        "SwiftBasicFormat/Indenter.swift",
        "SwiftSyntaxMacroExpansion/IndentationUtils.swift",
        "SwiftBasicFormat/InferIndentation.swift",
        "SwiftBasicFormat/Syntax+Extensions.swift",
        "SwiftBasicFormat/SyntaxProtocol+Formatted.swift",
        "SwiftSyntax/generated/SyntaxEnum.swift",
        "SwiftSyntax/generated/RenamedChildrenCompatibility.swift",
    ]

    /// Known to overflow the 512 KB stack (TODO.md / iterative Oracle+converter walks). A stack
    /// overflow cannot be caught: it takes down the whole xctest process, so the rest of the plan
    /// reports "Crash: xctest" and ~50 tests never run. Kept OUT of `files` until the walks are
    /// iterative; put it back then — it is the reproducer.
    static let knownStackOverflow = ["SwiftSyntax/generated/raw/RawSyntaxValidation.swift"]

    /// `<checkout>/swift-syntax/Sources`, derived from the configured corpus (which may point at a
    /// subfolder such as `Sources/SwiftParser`).
    static var sourcesRoot: URL? {
        guard var url = SourceFileCorpus.swiftSyntaxSourcesURL else { return nil }
        while url.lastPathComponent != "Sources", url.pathComponents.count > 1 {
            url.deleteLastPathComponent()
        }
        return url.lastPathComponent == "Sources" ? url : nil
    }

    static let stackSize = 512 * 1024

    @Test("full pipeline completes", arguments: files)
    func pipelineCompletes(_ relativePath: String) throws {
        let root = try #require(Self.sourcesRoot, "swift-syntax Sources not found")
        let url = root.appendingPathComponent(relativePath)
        guard FileManager.default.fileExists(atPath: url.path) else { return }   // absent in this checkout
        let text = try String(contentsOf: url, encoding: .utf8)
        let grammar = try loadGrammarFile(named: "Swift")

        final class Outcome: @unchecked Sendable { var built = false; var generated = false }
        let outcome = Outcome()
        let done = DispatchSemaphore(value: 0)
        let thread = Thread {
            let parser = MessageParser(grammar: grammar)
            parser.parse(input: text)
            _ = Oracle(parser: parser, input: text).disambiguate()
            outcome.built = DerivationBuilder(parser: parser, input: text).buildAST() != nil
            var generator = SwiftSyntaxGenerator(parser: parser, input: text)
            outcome.generated = generator.generate() != nil
            done.signal()
        }
        thread.stackSize = Self.stackSize
        thread.start()
        done.wait()

        let reference = Parser.parse(source: text)
        if !reference.hasError {
            #expect(outcome.built, "no derivation tree for \(relativePath)")
            #expect(outcome.generated, "no SwiftSyntax tree for \(relativePath)")
        }
    }
}
