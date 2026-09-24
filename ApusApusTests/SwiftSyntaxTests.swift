//
//  SwiftSyntaxTests.swift
//  AdventTests
//
//  Shared infrastructure for SwiftSyntax comparison tests.
//
//  Compares parse trees produced by the Advent GLL parser (via Swift.apus)
//  with the reference trees from SwiftSyntax's Parser.parse().
//
//  Each domain file (SwiftSyntaxDeclarations.swift, SwiftSyntaxExpressions.swift, etc.)
//  provides a snippet catalog and test suite. Snippets carry provenance metadata
//  linking back to the SwiftSyntax test they were extracted from.
//

import Testing
import Foundation
import SwiftSyntax
@_spi(ExperimentalLanguageFeatures) import SwiftParser

// MARK: - Tags

extension Tag {
    /// Reference-only tests that verify SwiftSyntax itself parses a snippet.
    /// They don't exercise the Advent parser. Keep them in the suite for the
    /// LCNP Phase 0 baseline run; filter them out of the inner-loop scheme.
    @Tag static var swiftSyntaxReference: Self
}


// MARK: - Versioned SwiftSyntax Corpus Suites

@Suite("swift-syntax 603")
struct SwiftSyntax603Tests {}

@Suite("swift-syntax 604")
struct SwiftSyntax604Tests {}

// MARK: - Snippet Type

struct SwiftSnippet: CustomTestStringConvertible, Sendable {
    let label: String
    let source: String
    let origin: String
    let syntaxVersion: String

    /// A genuine GAP: skipped by the accept-side tests, asserting nothing. Shrinking this set is
    /// the work; a snippet carrying one is a known defect, not a decision.
    var gapReason: String?

    /// An asserted DIVERGENCE, not a gap: swift-syntax parses this, the COMPILER rejects it, and so
    /// do we. The accept-side tests skip it (its tree would be meaningless) but
    /// `CompilerRejectTests` asserts Advent still rejects it, so it guards against regression
    /// instead of being silently ignored. The string is the compiler's own diagnostic, captured
    /// with `swiftc -typecheck` at classification time.
    var compilerRejects: String?

    init(label: String, source: String, origin: String, syntaxVersion: String,
         disabledReason: String? = nil, compilerRejects: String? = nil) {
        self.label = label
        self.source = source
        self.origin = origin
        self.syntaxVersion = syntaxVersion
        self.gapReason = disabledReason
        self.compilerRejects = compilerRejects
    }

    var experimentalLanguageFeatureReason: String? {
        guard !swiftSyntaxExperimentalFeatures.isEmpty else { return nil }
        return "requires SwiftSyntax experimental language features"
    }

    /// Accept-side tests skip all disabled kinds — only `gapReason` means "known Advent gap".
    /// Experimental-language-feature snippets are parser probes, not normal Swift corpus rows.
    var disabledReason: String? { gapReason ?? experimentalLanguageFeatureReason ?? compilerRejects }
    var testDescription: String { label }
    var diagnosticID: String { "\(origin)/\(label)" }

    var isSwiftSyntax604: Bool {
        syntaxVersion == "604.0.0-prerelease-2026-06-05"
    }

    var swiftSyntaxExperimentalFeatures: Parser.ExperimentalFeatures {
        guard isSwiftSyntax604 else { return [] }

        var features: Parser.ExperimentalFeatures = []

        if origin == "TypeTests.testLifetimeSpecifier" || source.contains("dependsOn(") {
            features.insert(.nonescapableTypes)
        }
        if origin == "TypeTests.testExpressionCount"
            || origin == "TypeTests.testSugaredExpressionCount"
            || origin == "TypeTests.testNestedExpressionCount"
            || source.contains("InlineArray<")
            || source.contains(" of ") {
            features.insert(.literalExpressions)
        }
        if origin == "ExpressionTests.testKeyPathMethodAndInitializers" {
            features.insert(.keypathWithMethodMembers)
        }
        if origin == "DeclarationTests.testUsing" || source.contains("using") {
            features.insert(.defaultIsolationPerFile)
        }
        if origin.hasPrefix("BorrowExprTests.")
            || origin.hasPrefix("MoveExprTests.")
            || source.contains("_borrow")
            || source.contains("_move") {
            features.insert(.oldOwnershipOperatorSpellings)
        }
        if origin.hasPrefix("MatchingPatternsTests.")
            || source.contains("_mutating")
            || source.contains("_borrowing")
            || source.contains("_consuming")
            || source.contains("inout _") {
            features.insert(.referenceBindings)
        }
        if origin == "DeclarationTests.testCoroutineAccessorsLegacyFormat" {
            features.insert(.coroutineAccessors)
        }
        if origin == "DeclarationTests.testBorrowAndMutateAccessors"
            || source.contains("borrow {")
            || source.contains("mutate {") {
            features.insert(.borrowAndMutateAccessors)
        }

        return features
    }

    var swiftSyntaxReferenceKind: SwiftSyntaxReferenceKind {
        guard isSwiftSyntax604 else { return .sourceFile }

        if origin == "AttributeTests.testImplementsAttributeBaseType" {
            return .attribute
        }
        if origin == "TypeTests.testExpressionCount" {
            return .expression
        }

        return .sourceFile
    }
}

enum SwiftSyntaxReferenceKind {
    case sourceFile
    case attribute
    case expression
}

// MARK: - SwiftSyntax Reference Helper

func swiftSyntaxTree(_ source: String) -> String {
    let parsed = Parser.parse(source: source)
    return dumpSwiftSyntaxNode(Syntax(parsed), indent: 0).text
}

func swiftSyntaxSourceFile(_ snippet: SwiftSnippet) -> SourceFileSyntax {
    let features = snippet.swiftSyntaxExperimentalFeatures
    guard !features.isEmpty else {
        return Parser.parse(source: snippet.source)
    }

    var source = snippet.source
    source.makeContiguousUTF8()
    return source.withUTF8 { buffer in
        Parser.parse(source: buffer, experimentalFeatures: features)
    }
}

func swiftSyntaxReferenceSyntax(_ snippet: SwiftSnippet) -> Syntax {
    let features = snippet.swiftSyntaxExperimentalFeatures

    switch snippet.swiftSyntaxReferenceKind {
    case .sourceFile:
        return Syntax(swiftSyntaxSourceFile(snippet))
    case .attribute:
        var parser = Parser(snippet.source, experimentalFeatures: features)
        return Syntax(AttributeSyntax.parse(from: &parser))
    case .expression:
        var parser = Parser(snippet.source, experimentalFeatures: features)
        return Syntax(ExprSyntax.parse(from: &parser))
    }
}

func swiftSyntaxReferenceHasError(_ snippet: SwiftSnippet) -> Bool {
    swiftSyntaxReferenceSyntax(snippet).hasError
}

/// A rendered node-per-line SwiftSyntax tree, compared for equality by `trees match`.
///
/// This is a wrapper around the `String` rather than the `String` itself for one
/// reason: a failing `#expect(refDump == adventDump, …)` makes Swift Testing
/// capture both operands and print them under the message. As plain `String`s
/// that meant two FULL trees per failure — on top of the trees the Phase suites
/// already interpolate into their own message, so each was printed twice. In a
/// bulk run that dominated everything: ~96k of 128k log lines were tree bodies.
///
/// `CustomStringConvertible` keeps `"\(refDump)"` yielding the whole tree, so the
/// suites that deliberately embed the diff in their message are unaffected.
/// `CustomTestStringConvertible` + `CustomTestReflectable` reduce the framework's
/// automatic capture to a one-line shape summary. Net effect: each tree is printed
/// exactly where a human asked for it, and nowhere else.
///
/// The suites that pass only the snippet ID as their message rely on that
/// automatic capture for the actual diff, so set `APUS_TREE_DUMPS=1` to restore
/// it when narrowing in on one snippet with `-only-testing:`. Same convention as
/// `parseReports` / `APUS_PARSE_REPORTS` for the engine's per-parse reports.
///
/// Use `.text` for string operations (`split`, `contains`, …).
struct TreeDump: Equatable, CustomStringConvertible, CustomTestStringConvertible, CustomTestReflectable {
    static let dumpsEnabled = ProcessInfo.processInfo.environment["APUS_TREE_DUMPS"] == "1"

    let text: String

    var description: String { text }
    var testDescription: String {
        guard !Self.dumpsEnabled else { return "\n" + text }
        return "TreeDump(\(text.count) chars, \(text.lazy.filter { $0 == "\n" }.count) lines)"
    }
    var customTestMirror: Mirror { Mirror(self, children: []) }
}

func swiftSyntaxReferenceDump(_ snippet: SwiftSnippet) -> TreeDump {
    dumpSwiftSyntaxNode(swiftSyntaxReferenceSyntax(snippet), indent: 0)
}

func dumpSwiftSyntaxNode(_ node: Syntax, indent: Int) -> TreeDump {
    TreeDump(text: renderSwiftSyntaxNode(node, indent: indent))
}

private func renderSwiftSyntaxNode(_ node: Syntax, indent: Int) -> String {
    let pad = String(repeating: "  ", count: indent)
    var result = ""

    if let token = node.as(TokenSyntax.self) {
        let text = token.text
        if !text.isEmpty {
            result += "\(pad)\(token.tokenKind.nameForComparison) \"\(text)\"\n"
        }
    } else {
        let typeName = "\(node.syntaxNodeType)"
            .replacingOccurrences(of: "Syntax", with: "")
        result += "\(pad)\(typeName)\n"
        for child in node.children(viewMode: .sourceAccurate) {
            result += renderSwiftSyntaxNode(child, indent: indent + 1)
        }
    }
    return result
}

extension TokenKind {
    var nameForComparison: String {
        switch self {
        case .keyword(let kw):       return "keyword(\(kw))"
        case .identifier:            return "identifier"
        case .integerLiteral:        return "integerLiteral"
        case .floatLiteral:          return "floatLiteral"
        case .stringSegment:         return "stringSegment"
        case .binaryOperator:        return "binaryOperator"
        case .prefixOperator:        return "prefixOperator"
        case .postfixOperator:       return "postfixOperator"
        case .dollarIdentifier:      return "dollarIdentifier"
        case .stringQuote:           return "stringQuote"
        case .multilineStringQuote:  return "multilineStringQuote"
        default:                     return "\(self)"
        }
    }
}

// MARK: - Advent Parse Helpers

struct AdventParseResult {
    let tree: ParseTreeNode?
    let builder: DerivationBuilder
    var isUnambiguous: Bool { builder.diagnostics.isEmpty }
}

/// Phase 0 baseline metrics captured per parsed source.
/// Written one row per unique source into `baseline-phase0.csv` by `metricSink`.
struct BaselineMetrics {
    let sourceLength: Int
    let tokenCount: Int
    let descriptorCount: Int
    let duplicateDescriptorCount: Int
    let suppressedDescriptorCount: Int
    let crfCount: Int
    let yieldCount: Int
    let matched: Bool
    let oraclePruned: Int
}

/// Everything the SwiftSyntax test surfaces care about for a single source.
/// Produced by `runAdventOnce` and stored in `parseCache` so the four facets
/// (`adventAccepts`, `unambiguous`, `treesMatch`, plus baseline) share work.
struct AdventRunSnapshot {
    let result: AdventParseResult?
    let swiftSyntaxTree: SourceFileSyntax?
    let metrics: BaselineMetrics
    /// Fallback sites the AST converter hit. `.unhandled` = construct not implemented
    /// yet (the phase work queue); `.lookupFailed` = a rule we claim to handle didn't
    /// yield its expected child (a bug). Lets `trees differ` be triaged by cause.
    let generatorDiagnostics: [GeneratorDiagnostic]
}

// MARK: - Grammar load
//
// Cached across snippets. The exclude/Schrödinger order-dependence that
// originally forced fresh-loads retired in LCNP Phase D — exclude is now a
// per-end LCNP filter in `testSelect`/`tokenMatch`, and `yields` moved off
// `GrammarNode` into `MessageParser.yields[node.number]`, so the grammar is
// load-time immutable and safely shareable. Cutting the per-snippet
// reload (ApusParser + first/follow fixpoint + verifyLL1 + populateBitSets)
// dominates wall-clock for the small SwiftSyntax snippets (measured 7–9×
// suite speedup).
private let cachedSwiftGrammar: Grammar = {
    do {
        return try loadGrammarFile(named: "Swift")
    } catch {
        fatalError("Could not load Swift grammar for tests: \(error)")
    }
}()

private func loadFreshSwiftGrammar() -> Grammar { cachedSwiftGrammar }

// MARK: - Per-Source Parse Memoization (#2)

private final class ParseCache: @unchecked Sendable {
    private let lock = NSLock()
    private var storage: [String: AdventRunSnapshot] = [:]

    func value(for source: String, populate: () -> AdventRunSnapshot) -> AdventRunSnapshot {
        lock.lock()
        if let cached = storage[source] {
            lock.unlock()
            return cached
        }
        lock.unlock()
        // Populate outside the cache lock; under `withParserIsolation` only one
        // parse runs at a time, so racing populates on the same source are
        // already coalesced by the parser lock above us.
        let snapshot = populate()
        lock.lock()
        if let existing = storage[source] {
            lock.unlock()
            return existing
        }
        storage[source] = snapshot
        lock.unlock()
        return snapshot
    }
}

private let parseCache = ParseCache()

// MARK: - Phase 0 Baseline Metrics Sink (#3)

private final class MetricSink: @unchecked Sendable {
    private let lock = NSLock()
    private let url: URL
    private var initialized = false
    private var handle: FileHandle?

    init() {
        url = testProjectDirectory().appendingPathComponent("baseline-phase0.csv")
    }

    func record(label: String, source: String, metrics m: BaselineMetrics) {
        lock.lock()
        defer { lock.unlock() }
        if !initialized {
            let header = "label,sourceLen,tokens,descriptors,duplicateDescriptors,suppressedDescriptors,crfSize,yieldCount,matched,oraclePruned\n"
            try? header.data(using: .utf8)?.write(to: url)
            handle = try? FileHandle(forWritingTo: url)
            _ = try? handle?.seekToEnd()
            initialized = true
        }
        let row = "\(csvEscape(label)),\(m.sourceLength),\(m.tokenCount),\(m.descriptorCount),\(m.duplicateDescriptorCount),\(m.suppressedDescriptorCount),\(m.crfCount),\(m.yieldCount),\(m.matched),\(m.oraclePruned)\n"
        if let data = row.data(using: .utf8) {
            handle?.write(data)
        }
    }

    private func csvEscape(_ s: String) -> String {
        if s.contains(",") || s.contains("\"") || s.contains("\n") || s.contains("\r") {
            return "\"" + s.replacingOccurrences(of: "\"", with: "\"\"") + "\""
        }
        return s
    }
}

private let metricSink = MetricSink()

// MARK: - One-shot parse + ASTs + metrics

/// Run the full Advent pipeline once for `source`:
/// scan → parse → (if matched) Oracle disambiguate, build derivation tree, and
/// generate the SwiftSyntax AST. Records baseline metrics either way.
///
/// `label` is recorded into the baseline CSV; the SwiftSyntax suites pass the
/// snippet label, ad-hoc callers (e.g. the RegexLookbehind probe) pass a short
/// derived label.
///
/// Each populate loads a fresh Swift grammar (see note on `loadFreshSwiftGrammar`).
/// After the first populate the cache returns the stored snapshot directly, so
/// each unique source pays the grammar-load cost exactly once.
private func runAdventOnce(
    _ source: String,
    label: String,
    referenceKind: SwiftSyntaxReferenceKind = .sourceFile,
    useCache: Bool = true
) -> AdventRunSnapshot {
    // `useCache: false` for WHOLE FILES. The cache key interpolates the entire source, so a
    // 495KB file is hashed in full and then the key AND the snapshot (parse result, BSR, tree)
    // are retained for the lifetime of the run. Across a 6.6MB corpus that is the dominant cost,
    // and nothing is ever re-queried by the same key. `adventAcceptsFile` sidesteps it the same way.
    let build: () -> AdventRunSnapshot = {
        // No `withParserIsolation` here: this path uses the shared, load-time
        // immutable `cachedSwiftGrammar` and builds a fresh `MessageParser` per
        // call. The core parser types carry no static mutable state, and
        // `ebnfDot()` no longer uses process-global scratch, so parses run
        // safely in parallel — the whole point of un-`.serialized`ing the
        // SwiftSyntax suites.
        do {
            let grammar = loadFreshSwiftGrammar()
            let input = source

            let parser = MessageParser(grammar: grammar)
            let root: GrammarNode?
            switch referenceKind {
            case .sourceFile:
                root = nil
            case .attribute:
                root = grammar.nonTerminals["attribute"]
            case .expression:
                root = grammar.nonTerminals["expression"]
            }
            if let root {
                parser.prepareInput(input: input, isSubParser: false)
                parser.runGLL(root: root, start: input.startIndex)
            } else {
                parser.parse(input: input)
            }

            let extent = input.endIndex
            let origin = input.startIndex
            // Accept yields whose end is the input end OR is followed only by trivia —
            // EOS lex at y.j does the trivia skip and matches iff scan reaches `extent`.
            // This lets comment-only sources and trailing-comment sources pass.
            let matched = parser.yield(of: parser.currentParseRoot).contains { y in
                guard y.i == origin else { return false }
                if y.j == extent { return true }
                return !parser.lexer.lex(at: y.j, terminalID: grammar.eosID).isEmpty
            }

            var oraclePruned = 0
            var parseResult: AdventParseResult? = nil
            var swiftSyntax: SourceFileSyntax? = nil
            var generatorDiagnostics: [GeneratorDiagnostic] = []

            if matched {
                oraclePruned = Oracle(parser: parser, input: input).disambiguate()
                let builder = DerivationBuilder(parser: parser, input: input)
                let tree = builder.buildAST()
                if let tree {
                    parseResult = AdventParseResult(tree: tree, builder: builder)
                }
                if parseResult != nil, referenceKind == .sourceFile {
                    var generator = SwiftSyntaxGenerator(parser: parser, input: input)
                    swiftSyntax = generator.generate()
                    generatorDiagnostics = generator.diagnostics
                }
            }

            let metrics = BaselineMetrics(
                sourceLength: source.count,
                tokenCount: parser.commitsByStart.count,
                descriptorCount: parser.descriptorCount,
                duplicateDescriptorCount: parser.duplicateDescriptorCount,
                suppressedDescriptorCount: parser.suppressedDescriptorCount,
                crfCount: parser.crf.count,
                yieldCount: parser.yieldCount,
                matched: matched,
                oraclePruned: oraclePruned
            )
            // Only write the baseline CSV when explicitly requested — under parallel
            // execution the row order is nondeterministic, which would churn this
            // tracked file on every run. Set APUS_BASELINE_CSV=1 to regenerate it.
            if ProcessInfo.processInfo.environment["APUS_BASELINE_CSV"] == "1" {
                metricSink.record(label: label, source: source, metrics: metrics)
            }
            return AdventRunSnapshot(
                result: parseResult,
                swiftSyntaxTree: swiftSyntax,
                metrics: metrics,
                generatorDiagnostics: generatorDiagnostics
            )
        }
    }
    guard useCache else { return build() }
    return parseCache.value(for: "\(referenceKind):\(source)", populate: build)
}

/// Back-compat entry point used by the SwiftSyntax test suites.
/// `throws` is preserved for API stability; the new path never actually throws.
func adventParse(_ source: String) throws -> AdventParseResult? {
    runAdventOnce(source, label: shortLabel(source)).result
}

/// Variant that also records the snippet's external label (e.g. `testTernary#1`)
/// into the baseline CSV. SwiftSyntax suites call this; older callers use
/// `adventParse` and get a derived label.
func adventParse(_ snippet: SwiftSnippet) throws -> AdventParseResult? {
    runAdventOnce(
        snippet.source,
        label: snippet.diagnosticID,
        referenceKind: snippet.swiftSyntaxReferenceKind
    ).result
}

func adventSwiftSyntaxTree(_ source: String) throws -> SourceFileSyntax? {
    runAdventOnce(source, label: shortLabel(source)).swiftSyntaxTree
}

func adventSwiftSyntaxTree(_ snippet: SwiftSnippet) throws -> SourceFileSyntax? {
    runAdventOnce(
        snippet.source,
        label: snippet.diagnosticID,
        referenceKind: snippet.swiftSyntaxReferenceKind
    ).swiftSyntaxTree
}

/// Whole-file tree build that does NOT touch `parseCache` — same reasoning as `adventAcceptsFile`.
func adventTreeForFile(_ text: String) -> SourceFileSyntax? {
    runAdventOnce(text, label: "file", useCache: false).swiftSyntaxTree
}

// MARK: - Source-file suites (opt-in)
//
// The snippet corpora are all small, isolated fragments. Real files are a different input
// distribution — comments, long bodies, deep nesting, trivia — and they surface defects the
// snippets structurally cannot. `GenerateSwiftSyntaxAST.swift` (495KB) is the standing example: it
// parses in ~1.8s and does NOT match, a gap no snippet test had ever shown.
//
// OPT-IN, because they are slow: after removing the pop-time follow gate a 54KB file parses in
// ~1.0s, so Advent's own ~915KB of sources is ~15-20s and swift-syntax's 6.6MB is minutes. The
// default suite stays at ~50s.
//
//   APUS_SOURCE_FILE_SUITES=1                     enable both
//   APUS_SWIFTSYNTAX_SOURCES=/path/to/checkout    where to find swift-syntax's Sources/
//
// swift-syntax lives in an SPM checkout whose path contains a DerivedData hash, so it is supplied
// explicitly rather than guessed — a test should not go rummaging through the user's home.
//
// ACCEPTANCE ONLY. Each file is first required to be valid by swift-syntax's own reckoning
// (`hasError == false`); a file it rejects is a bad fixture, not an Advent defect. Tree comparison
// is deliberately NOT asserted here: at file scale a single converter gap would bury the signal.

struct SourceFile: CustomTestStringConvertible, Sendable {
    let url: URL
    var testDescription: String { url.lastPathComponent }
}

enum SourceFileCorpus {
    static let enabled = ProcessInfo.processInfo.environment["APUS_SOURCE_FILE_SUITES"] == "1"

    /// Advent's own sources: the `.swift` files at the repository root. Deliberately not recursive —
    /// that would pull in `AdventTests` (fixture arrays, megabytes of string literals),
    /// `GeneratedParser` and `TestOutput`, none of which are hand-written project sources.
    static let adventFiles: [SourceFile] = {
        guard enabled else { return [] }
        let root = testProjectDirectory()
        let all = (try? FileManager.default.contentsOfDirectory(at: root, includingPropertiesForKeys: nil)) ?? []
        return all.filter { $0.pathExtension == "swift" }
            .sorted { $0.lastPathComponent < $1.lastPathComponent }
            .map(SourceFile.init)
    }()

    static let swiftSyntaxFiles: [SourceFile] = {
        guard enabled,
              let path = ProcessInfo.processInfo.environment["APUS_SWIFTSYNTAX_SOURCES"]
        else { return [] }
        let base = URL(fileURLWithPath: path)
        guard let walker = FileManager.default.enumerator(at: base, includingPropertiesForKeys: nil)
        else { return [] }
        var out: [SourceFile] = []
        for case let u as URL in walker where u.pathExtension == "swift" { out.append(SourceFile(url: u)) }
        return out.sorted { $0.url.path < $1.url.path }
    }()
}

/// Parse a whole file without touching `parseCache`. The cache is keyed by SOURCE TEXT, so feeding
/// it megabyte strings would hash and retain them for no benefit — each file is parsed once.
func adventAcceptsFile(_ text: String) -> Bool {
    let grammar = loadFreshSwiftGrammar()
    let parser = MessageParser(grammar: grammar)
    parser.parse(input: text)
    let root = parser.currentParseRoot ?? grammar.root
    return parser.yield(of: root).contains { y in
        guard y.i == text.startIndex else { return false }
        if y.j == text.endIndex { return true }
        return !parser.lexer.lex(at: y.j, terminalID: grammar.eosID).isEmpty
    }
}

@Suite("SwiftSyntax - Advent source files")
struct AdventSourceFileTests {
    @Test("Advent accepts", arguments: SourceFileCorpus.adventFiles)
    func accepts(_ file: SourceFile) throws {
        let text = try String(contentsOf: file.url, encoding: .utf8)
        try #require(!Parser.parse(source: text).hasError,
                     "swift-syntax rejects \(file.testDescription) — bad fixture, not an Advent defect")
        #expect(adventAcceptsFile(text),
                "Advent failed to parse: \(file.testDescription) (\(text.utf8.count) bytes)")
    }

    @Test("trees match", arguments: SourceFileCorpus.adventFiles)
    func treesMatch(_ file: SourceFile) throws {
        try expectFileTreeMatches(file)
    }
}

@Suite("SwiftSyntax - SwiftSyntax source files")
struct SwiftSyntaxSourceFileTests {
    @Test("Advent accepts", arguments: SourceFileCorpus.swiftSyntaxFiles)
    func accepts(_ file: SourceFile) throws {
        let text = try String(contentsOf: file.url, encoding: .utf8)
        try #require(!Parser.parse(source: text).hasError,
                     "swift-syntax rejects \(file.testDescription) — bad fixture, not an Advent defect")
        #expect(adventAcceptsFile(text),
                "Advent failed to parse: \(file.testDescription) (\(text.utf8.count) bytes)")
    }

    @Test("trees match", arguments: SourceFileCorpus.swiftSyntaxFiles)
    func treesMatch(_ file: SourceFile) throws {
        try expectFileTreeMatches(file)
    }
}

/// GRAMMAR vs MODEL — the Step 2 gate.
///
/// `KeyPathModel` is exact against swift-syntax (see `KeyPathModelTests`), so it can be used as the
/// oracle for the GRAMMAR, at any depth, without paying for a swift-syntax parse. Every divergence
/// here is a `Swift.apus` defect. This is what drove the Step 2 fixes: the root-absent dot gate,
/// the spaced mark run as a first component, the suppressed-type root, generic arguments on member
/// names, the tight mark-run split, the spaced-`!` component, and the structural postfix island.
///
/// TWO measures of "Advent accepts" exist and they are NOT the same:
///   * yield — a parse yield spans the input. PRE-Oracle, so `@cannotParse`/`@prefer`/`@longest`
///     do not affect it.
///   * tree  — the Oracle ran and a tree was built. This is what `runAdventOnce` does, so it is the
///     criterion the accept/reject suites actually use, and it is what this suite asserts on.
/// The `oraclePruned` figure reports the gap, i.e. how much the Oracle predicates are carrying.
@Suite("SwiftSyntax - key-path grammar vs model")
struct KeyPathGrammarTests {
    /// NO KNOWN RESIDUALS. The sweep is expected to be EXACTLY clean — every divergence is a
    /// defect. Both classes that used to be exempted here are fixed:
    ///   * the `<T>`-root over-acceptance (`\\Foo<T>.?.[0]`), by committing the key-path root to a
    ///     generic clause whenever a `<` follows (`keyPathRootBase`);
    ///   * the `.?`/`.!` postfix under-acceptance (`\\Foo + x.?`), by `postfixDotOperator`.
    /// Deliberately NOT reintroducing an allowance list: it masked a third class once already —
    /// `hasSuffix(".?")` was written for `\\Foo + x.?` and silently swallowed `\\Foo.p<T>.?`.

    static func sweep(items: [String], length: Int) -> (over: [String], under: [String], total: Int, pruned: Int) {
        var over: [String] = [], under: [String] = [], total = 0, pruned = 0
        func rec(_ root: String, _ acc: [String]) {
            if acc.count == length {
                total += 1
                let suffix = acc.joined()
                let src = "let v = " + root + suffix
                let model = KeyPathModel.parsesCleanly(suffix: suffix, rootWasPresent: root != "\\")
                let tree = adventTreeForFile(src) != nil
                if model != tree {
                    if tree { over.append(src) } else { under.append(src) }
                }
                if !model, !tree, adventAcceptsFile(src) { pruned += 1 }
                return
            }
            for it in items { rec(root, acc + [it]) }
        }
        for root in KeyPathModelTests.roots { rec(root, []) }
        return (over, under, total, pruned)
    }

    static func check(_ label: String, items: [String], length: Int) {
        let r = sweep(items: items, length: length)
        print("KP \(label) len=\(length) total=\(r.total) over=\(r.over.count) under=\(r.under.count) oraclePruned=\(r.pruned)")
        for o in r.over.prefix(40) { print("KP   over  : \(o)") }
        for u in r.under.prefix(40) { print("KP   under : \(u)") }
        fflush(stdout)
        #expect(r.over.isEmpty, "\(r.over.count) over-acceptances at \(label) len \(length), e.g. \(r.over.prefix(5))")
        #expect(r.under.isEmpty, "\(r.under.count) under-acceptances at \(label) len \(length), e.g. \(r.under.prefix(5))")
    }

    /// Fixtures for the four TODO items closed on 2026-09-23 (1, 2, 3, 21). Each asserts BOTH
    /// acceptance parity with swift-syntax AND tree equality, because every one of these was a
    /// TREE defect that acceptance testing alone could not see — `try! /re/…` parsed happily as
    /// `/` prefix + `re` + `/` postfix operators, and `var (b, var c)` silently dropped its `var`.
    ///
    /// The regex cases exist because the (now closed) regex-gate TODO required a fixture per change: removing the
    /// literal `"!"` from the regex-opener gates flips regex-vs-division decisions, and `x!/y/`
    /// (division, via `forceMark`) is the case that must NOT flip.
    @Test("TODO 1/2/3/21 regression fixtures", arguments: [
        // 1 — cast / generic-argument tails. The first four are swift RECOVERIES.
        "f(a as? A<B>??x)", "value as! A<B>??x", "value as A<B>??x", "value is A<B>???x",
        "x as? Foo ?? bar", "value as? A<B>", "value as? A<B>?", "value as? A<B> ?? x",
        // 1 — SE-0390 suppressed type straight off the cast keyword
        "value as~Copyable", "value is~Copyable", "value as!~C", "value as?~C", "a~b",
        // 1 — `T.self` in TYPE position: MemberType with a `self` keyword name
        "value as!A<B>?.self", "value as A<B>?.self", "value as? Foo.self",
        // 1 — tight `await` may take call/subscript/member operands, but not operator-start operands.
        "await(f())", "await[x]", "await.foo", "await-x", "await!x", "await>>x",
        // 2 — regex opener gate. `try!` spells a LITERAL `!`; postfix force-unwrap is `forceMark`.
        "try! /re/.wholeMatch(in: s)", "try? /re/.wholeMatch(in: s)", "x!/y/", "x?/y/",
        "#/abc/#", "a > #/x/#", "a>#/x/#", "x!#/a/#", "x?#/a/#", "_#/a/#",
        // 21 — mark-ending dot operators, infix AND postfix
        "a .? b", "a .! b", "a .?? b", "a .?. b", "a.?.b", "x.?", "f(x.?)",
        "\\Foo.?.?[0]", "a ?? b", "a ? b : c", "a ?: b", "a...b", "a..<b", "1...", "x!", "x?",
    ])
    func closedTodoFixtures(_ tail: String) throws {
        let src = "let v = " + tail
        let swiftClean = swiftSyntaxParsesCleanly(src)
        let tree = adventTreeForFile(src)
        #expect((tree != nil) == swiftClean,
                "acceptance differs from swift-syntax for `\(tail)` (swift \(swiftClean ? "clean" : "recovers"))")
        if let tree, swiftClean {
            #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0),
                    "trees differ for `\(tail)`")
        }
    }

    @Test("line-broken implicit member expression fixtures", arguments: [
        "let x = .\nsome(value)?",
        "if case let .\nsome(value)? = Optional(Optional(value)) { _ = value }",
        "do {\nif case let .\nsome(value)? = Optional(Optional(value)) { _ = value }\n}",
        "if case .\nsome = value {}",
    ])
    func lineBrokenImplicitMemberFixtures(_ src: String) throws {
        let swiftClean = swiftSyntaxParsesCleanly(src)
        let tree = adventTreeForFile(src)
        #expect((tree != nil) == swiftClean,
                "acceptance differs from swift-syntax for `\(src)` (swift \(swiftClean ? "clean" : "recovers"))")
        if let tree, swiftClean {
            #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0),
                    "trees differ for `\(src)`")
        }
    }

    @Test("ifconfig leading-dot member fixtures", arguments: [
        "#if FOO && !BAR\n.member\n#endif",
        "#if FOO\n.member()\n#endif",
        "#if FOO\n.member + 12\n#endif",
        "func f() {}\n#if FOO\n.member\n#endif",
        "baseExpr\n#if FOO\n.methodOne() + 12\n#endif",
        "let y = 1\n#if FOO\n.member + 12\n#endif",
    ])
    func ifConfigLeadingDotFixtures(_ src: String) throws {
        let swiftClean = swiftSyntaxParsesCleanly(src)
        let tree = adventTreeForFile(src)
        #expect((tree != nil) == swiftClean,
                "acceptance differs from swift-syntax for `\(src)` (swift \(swiftClean ? "clean" : "recovers"))")
        if let tree, swiftClean {
            #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0),
                    "trees differ for `\(src)`")
        }
    }

    @Test("regex literal tab fixtures", arguments: [
        "let r = /a b/",
        "let r = /a  b/",
        "let r = /a\tb/",
        "let r = /[a\tb]/",
        "let r = /(a\tb)/",
        "let r = /a\\tb/",
    ])
    func regexLiteralTabFixtures(_ src: String) throws {
        let swiftClean = swiftSyntaxParsesCleanly(src)
        let tree = adventTreeForFile(src)
        #expect((tree != nil) == swiftClean,
                "acceptance differs from swift-syntax for `\(src)` (swift \(swiftClean ? "clean" : "recovers"))")
        if let tree, swiftClean {
            #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0),
                    "trees differ for `\(src)`")
        }
    }

    /// 3 — nested value bindings in a tuple binding pattern. swift-syntax ACCEPTS these and models
    /// the inner specifier as a `ValueBindingPattern`; the old TODO item's premise (that swift rejects
    /// them) was wrong. Whole statements, so they cannot share the `let v = …` harness above.
    @Test("TODO 3 nested binding fixtures", arguments: [
        "var (b, var c) = t", "let (a, let b) = t", "var (b, c) = t", "let (a, b) = t",
        "var (b, _) = t", "for (position, var lineIdx, raw) in xs {}",
    ])
    func nestedBindingFixtures(_ src: String) throws {
        let swiftClean = swiftSyntaxParsesCleanly(src)
        let tree = adventTreeForFile(src)
        #expect((tree != nil) == swiftClean,
                "acceptance differs from swift-syntax for `\(src)` (swift \(swiftClean ? "clean" : "recovers"))")
        if let tree, swiftClean {
            #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0),
                    "trees differ for `\(src)`")
        }
    }

    /// TEMP triage for TODO 1-5 (the fuzzer buckets). Minimal reproducers taken from
    /// `AdventFuzzer/runs/2026-09-23T08-46-48Z/artifacts`, not retyped from the summary.
    @Test("TEMP fuzz buckets")
    func fuzzBuckets() throws {
        let cases: [(String, String)] = [
            // 1 — packs / variadic generics (18 underaccepts)
            ("1", "struct Fuzz<each T> { let value: (repeat each T) }"),
            ("1", "func fuzz<each T>(_ value: repeat each T) { _ = (repeat each value) }"),
            ("1", "func fuzz<each T>(_ value: repeat each T) -> (repeat each T) { (repeat each value) }"),
            ("1", "func fuzz<each T>(_ value: repeat each T) { for item in repeat each value { _ = item } }"),
            ("1", "func fuzz<each T: Equatable>(_ value: repeat each T) {}"),
            ("1", "repeat { } while false"),
            // 2 — pound / ifconfig (46 tree diffs)
            ("2", "#if !!FOO\nlet x = 1\n#endif"),
            ("2", "#if !!FOO\nreturn\n#endif"),
            ("2", "#if FOO && !BAR\n.member\n#endif"),
            ("2", "#sourceLocation(file: \"fuzz.swift\", line: 10)"),
            ("2", "#sourceLocation()"),
            ("2", "let fuzzValue = #fileID"),
            // 3 — regex / slash (36 tree diffs)
            ("3", "let s = \"abc\"\n_ = /a b/"),
            ("3", "let s = \"abc\"\ntry? /a b/"),
            ("3", "let s = \"abc\"\nlet r = /a b/.wholeMatch(in: s)"),
            ("3", "let s = \"abc\"\ntry? /x*//"),
            // 4 — enum / switch / optional-case patterns (59 tree diffs)
            ("4", "if case let .some(value)? = Optional(Optional(value)) { _ = value }"),
            ("4", "if case var .some(value)? = Optional(Optional(value)) { _ = value }"),
            ("4", "guard case let .some(value)? = Optional(Optional(value)) else { return }"),
            // 5 — structural overaccepts (19 of the 49; the other 30 are Oracle-pruned)
            ("5", "let await = items\nlet fuzzValue = await??items"),
            ("5", "let parser = await\nlet fuzzValue = parser?.await"),
            ("5", "let await = items\nlet fuzzValue = await!items"),
            ("5", "let fuzzValue = \\.default / value"),
            ("5", "struct Fuzz<T: Self> { var value: T }"),
        ]
        for (bucket, src) in cases {
            let sw = swiftSyntaxParsesCleanly(src)
            let refHasError = Parser.parse(source: src).hasError
            let tree = adventTreeForFile(src)
            let y = adventAcceptsFile(src)
            var tag: String
            if (tree != nil) != !refHasError { tag = (tree != nil) ? "OVER " : "UNDER" }
            else if let tree, !refHasError,
                    dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                    != dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0) { tag = "TREE " }
            else { tag = "ok   " }
            print("F \(bucket) \(tag) yield=\(y ? "y" : "n") tree=\(tree != nil ? "y" : "n") swiftClean=\(sw ? "y" : "n") swiftErr=\(refHasError ? "y" : "n") | \(src.replacingOccurrences(of: "\n", with: " ⏎ "))")
        }
        fflush(stdout)
    }

    /// TEMP: diffs for buckets 2-4, and a decomposition of bucket 5's overaccepts.
    @Test("TEMP bucket detail")
    func bucketDetail() throws {
        let diffs = [
            "#sourceLocation(file: \"fuzz.swift\", line: 10)",
            "let s = \"abc\"\ntry? /x*//",
        ]
        for src in diffs {
            print("D ===== \(src.replacingOccurrences(of: "\n", with: " ⏎ "))")
            let ref = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: src)), indent: 0).text
            guard let tree = adventTreeForFile(src) else { print("D   <<< NO TREE >>>"); continue }
            let got = dumpSwiftSyntaxNode(Syntax(tree), indent: 0).text
            if got == ref { print("D   same"); continue }
            let g = got.split(separator: "\n").map(String.init), r = ref.split(separator: "\n").map(String.init)
            for i in 0..<max(g.count, r.count) {
                let gl = i < g.count ? g[i] : "<none>", rl = i < r.count ? r[i] : "<none>"
                if gl != rl { print("D   * got=\(gl.trimmingCharacters(in: .whitespaces))  ||  ref=\(rl.trimmingCharacters(in: .whitespaces))") }
            }
        }
        // Bucket 5 — isolate which fragment each overaccept actually comes from.
        for src in ["#if FOO\n.member\n#endif", "#if !BAR\n.member\n#endif",
                    "#if FOO && BAR\n.member\n#endif", "#if FOO && !BAR\nlet x = 1\n#endif",
                    "let await = items", "let x = await", "let x = parser?.await",
                    "let await = 1\nlet y = await", "struct Fuzz<T: Self> { var value: T }",
                    "let v = \\.default / value", "let v = \\Foo.Bar.default / value",
                    "let v = \\.default", "let v = a / value", "await f()",
                    "func f() async { await g() }", "let x = try await g()"] {
            let err = Parser.parse(source: src).hasError
            let tree = adventTreeForFile(src)
            let tag = (tree != nil) == !err ? "ok   " : ((tree != nil) ? "OVER " : "UNDER")
            print("E \(tag) tree=\(tree != nil ? "y" : "n") swiftErr=\(err ? "y" : "n") | \(src.replacingOccurrences(of: "\n", with: " ⏎ "))")
        }
        fflush(stdout)
    }

    /// TODO #8 — the identifier audit, done by enumeration rather than by reading the grammar.
    ///
    /// `Swift.apus` splits identifier positions TWO ways (`softIdentifier` = any keyword is a name,
    /// `hardIdentifier` = reserved words excluded). The suspicion under test is that two categories
    /// are too coarse, because swift distinguishes FOUR positions independently. For each candidate
    /// word this prints whether Advent and swift-syntax agree in each position, so the categories
    /// can be defined from data.
    @Test("TEMP identifier audit")
    func identifierAudit() throws {
        let words = [
            // contextual keywords that are also OPERATORS/prefixes in expression position
            "await", "consume", "borrow", "copy", "unsafe", "each", "repeat", "try", "some", "any",
            // declaration modifiers / accessor words
            "isolated", "sending", "nonisolated", "distributed", "dynamic", "final", "lazy",
            "mutating", "nonmutating", "optional", "override", "required", "weak", "unowned",
            "indirect", "convenience", "infix", "prefix", "postfix", "package", "open", "actor",
            "macro", "borrowing", "consuming", "didSet", "willSet", "get", "set", "async",
            "reasync", "yield", "of", "file", "line", "left", "right", "none", "associativity",
            "assignment", "safe", "Type", "Protocol",
            // hard keywords, as controls — these must be rejected everywhere but member position
            "self", "Self", "init", "deinit", "class", "if", "in", "where", "inout", "let", "var",
        ]
        let positions: [(String, (String) -> String)] = [
            ("declName", { "let \($0) = 1" }),
            ("operand",  { "let \($0) = 1\nlet fuzzResult = \($0)" }),
            ("member",   { "let fuzzResult = base.\($0)" }),
            ("label",    { "let fuzzResult = f(\($0): 1)" }),
            ("typeName", { "struct Fuzz { var v: \($0) }" }),
            ("constraint", { "struct Fuzz<T: \($0)> { var v: T }" }),
        ]
        for w in words {
            var row: [String] = []
            for (name, make) in positions {
                let src = make(w)
                let swiftOK = !Parser.parse(source: src).hasError
                let adventOK = adventTreeForFile(src) != nil
                let mark = adventOK == swiftOK ? (swiftOK ? "ok" : "--") : (adventOK ? "OVER" : "UNDER")
                row.append("\(name)=\(mark)")
            }
            print("I \(w.padding(toLength: 14, withPad: " ", startingAt: 0)) \(row.joined(separator: " "))")
        }
        fflush(stdout)
    }

    /// 504 tree builds, ~20s. The only gate that checks the GRAMMAR (not the model) against swift.
    @Test("CORE alphabet x 9 roots matches the model", arguments: [1, 2])
    func core(_ n: Int) throws { Self.check("core", items: KeyPathModelTests.core, length: n) }

    /// ~13k tree builds, ~9min. Opt in with `APUS_KEYPATH_DEEP=1` when changing key-path rules.
    @Test("deep: CORE length 3 and WIDE lengths 1-2", arguments: [("core", 3), ("wide", 1), ("wide", 2)])
    func deep(_ spec: (String, Int)) throws {
        guard ProcessInfo.processInfo.environment["APUS_KEYPATH_DEEP"] == "1" else { return }
        let (label, n) = spec
        Self.check(label, items: label == "core" ? KeyPathModelTests.core : KeyPathModelTests.wide, length: n)
    }
}

/// Validates `KeyPathModel` — the executable port of swift's key-path loop AND of the lexer rules
/// it depends on — against swift-syntax itself.
///
/// This is the METHOD RESET for key paths. Rather than patching the grammar per failing case
/// (which grew it to 40 rules and left residue one sequence-length deeper each time), the language
/// is derived once, executably, so every claim is falsifiable in seconds at any depth.
///
/// EXACT, zero disagreements over ~12.2M sequences:
///   * CORE alphabet x all 9 `keyPathRootBase` forms, lengths 1-6 — 1,235,304.
///   * WIDE alphabet x 9 roots, lengths 1-4 — 11,006,820.
///
/// CORE is the five component FORMS the grammar admits. WIDE adds every spelling variant that was
/// ever in doubt: multi-mark runs, SPACING variants, method components with argument labels,
/// generic arguments, metatypes, labelled subscripts, escaped identifiers, tuple-index members,
/// `::` module selectors, trailing closures on subscripts, operators outside `?!.<>`, and the
/// `as`/`is` keyword casts.
///
/// Everything here was PORTED from swift's source, never inferred; `KeyPathModel.swift` cites the
/// originating function for each rule. Around twenty of those rules were guessed wrong at some
/// point in this investigation — which is the entire argument for the model existing.
@Suite("SwiftSyntax - key-path model")
struct KeyPathModelTests {
    static let core = [".p", "?", "!", ".?", ".!", "[0]", ".[0]"]
    static let wide = core + [
        "??", "?!", "!?", "!!", " ?", " ??", " .p",
        ".m()", ".m(a:)", ".p<T>", ".Type", "[a: b]", ".`class`", ".0",
        // the hedge items: module selectors, trailing closures, operators outside `?!.<>`,
        // the keyword casts, and trailing trivia
        ".Mod::p", "[0]{ }", "[f: 0]", " + x", " ~ x", " == x", " & x", " || x",
        " as T", " is T", ".p ", " ",
    ]
    /// All 8 `keyPathRootBase` forms, plus root-absent.
    static let roots = ["\\Foo", "\\Foo<T>", "\\Foo.Type", "\\(A, B)", "\\[A]", "\\[A: B]",
                        "\\Any", "\\(A)", "\\"]

    static func disagreements(items: [String], length: Int) -> [String] {
        var bad: [String] = []
        func rec(_ root: String, _ acc: [String]) {
            if acc.count == length {
                let suffix = acc.joined()
                let source = "let v = " + root + suffix
                let truth = swiftSyntaxParsesCleanly(source)
                let model = KeyPathModel.parsesCleanly(suffix: suffix, rootWasPresent: root != "\\")
                if truth != model { bad.append(source) }
                return
            }
            for item in items { rec(root, acc + [item]) }
        }
        for root in roots { rec(root, []) }
        return bad
    }

    @Test("CORE alphabet x 9 roots is exact", arguments: [1, 2, 3])
    func coreExact(_ n: Int) throws {
        let bad = Self.disagreements(items: Self.core, length: n)
        #expect(bad.isEmpty, "\(bad.count) disagreements at length \(n), e.g. \(bad.prefix(3))")
    }

    @Test("WIDE alphabet x 9 roots is exact", arguments: [1, 2])
    func wideExact(_ n: Int) throws {
        let bad = Self.disagreements(items: Self.wide, length: n)
        #expect(bad.isEmpty, "\(bad.count) disagreements at length \(n), e.g. \(bad.prefix(3))")
    }

    /// Millions of cases; opt in with `APUS_KEYPATH_DEEP=1` when changing the model.
    @Test("CORE alphabet x 9 roots is exact at depth", arguments: [4, 5, 6])
    func coreExactDeep(_ n: Int) throws {
        guard ProcessInfo.processInfo.environment["APUS_KEYPATH_DEEP"] == "1" else { return }
        let bad = Self.disagreements(items: Self.core, length: n)
        #expect(bad.isEmpty, "\(bad.count) disagreements at length \(n), e.g. \(bad.prefix(3))")
    }

    /// The WIDE alphabet at depth. Same opt-in.
    @Test("WIDE alphabet x 9 roots is exact at depth", arguments: [3, 4])
    func wideExactDeep(_ n: Int) throws {
        guard ProcessInfo.processInfo.environment["APUS_KEYPATH_DEEP"] == "1" else { return }
        let bad = Self.disagreements(items: Self.wide, length: n)
        #expect(bad.isEmpty, "\(bad.count) disagreements at length \(n), e.g. \(bad.prefix(3))")
    }
}

/// Key-path tails — a fuzzer find (2026-09-21), FIXED 2026-09-22.
///
/// swift's key-path loop consumes a run of `?`/`!` marks HOWEVER IT IS SPACED, because branch 2 of
/// `parseKeyPathExpression` tests the operator TOKEN and splits its text into one component per
/// mark. So `\Foo.bar ?? fallback` takes `??` as two components and leaves `fallback` dangling —
/// rejected for THAT reason, not because an infix tail is forbidden. Ordinary infix tails are
/// legal (`+ 1`, `== x`, `&& y`, `as AnyKeyPath`), and so is a lone spaced `?` opening a ternary,
/// which in swift falls out of the LEXER classifying it as infix rather than postfix.
/// Full algorithm: `SwiftSyntax Mapping.md` → "Key-path components: swift's actual algorithm".
@Suite("SwiftSyntax - key-path tails")
struct KeyPathTailTests {
    /// Advent matches swift-syntax on these — acceptance, ambiguity and tree.
    static let agreeing: [String] = [
        // the original fuzzer finds: a spaced `??` is consumed as two components
        #"let a = \.default ?? fallback"#, #"let a = \.foo?.bar ?? fallback"#,
        #"let a = \.foo!.bar ?? fallback"#, #"let a = \Foo.bar ?? fallback"#,
        // other spaced mark runs, in both phases
        #"let a = \Foo.bar ?! x"#, #"let a = \Foo.bar !? x"#, #"let a = \Foo.bar !! x"#,
        #"let a = \Foo.bar ??"#, #"let a = \.foo?.bar !! z"#,
        // legal infix tails, which the mark-run rule must NOT catch
        #"let a = \Foo.bar ? a : b"#, #"let a = \Foo.bar + 1"#, #"let a = \Foo.bar == x"#,
        #"let a = \Foo.bar && y"#, #"let a = \Foo.bar < 3"#, #"let a = \Foo.bar as AnyKeyPath"#,
        #"let a = \.foo / value"#, #"let a = \Foo.bar ? value"#,
        // plain key paths, including their own `?`/`!`/`[]`/dotted components
        #"let a = \Foo.bar"#, #"let a = \.foo"#, #"let a = \.self"#,
        #"let a = \.foo?.bar"#, #"let a = \.foo!.bar"#,
        #"let a = \Foo.bar?"#, #"let a = \Foo.bar!"#, #"let a = \Foo.bar??"#,
        #"let a = \Foo.[0]"#, #"let a = \Foo.bar[0]"#, #"let a = \.foo[0].bar"#,
        #"let a = \Foo.bar.baz"#, #"let a = \Foo.bar.baz.qux"#, #"let a = \.a.b.c"#,
        #"let a = \Foo.Bar.baz"#, #"let a = \[Int].count"#, #"let a = \Foo?.bar"#,
        #"let a = \Foo?.?.bar.?.blah"#, #"let a = \Foo?.?.?.blah"#,
        // swift's key-path loop can stop before a dot-led mark operator after a non-property pivot;
        // the remaining `.?`/`.!` is a binary operator in the enclosing SequenceExpr.
        #"let a = \Foo.?.?[0]"#, #"let a = \Foo.!.?[0]"#,
        #"let a = \Foo[0].?[0]"#, #"let a = \Foo[0].![0]"#,
        #"let a = \Foo.[0].?[0]"#, #"let a = \Foo.[0].![0]"#,
        #"let a = \.?.?[0]"#, #"let a = \.?.![0]"#,
        #"let a = \.!.?[0]"#, #"let a = \.!.![0]"#,
        #"let a = \.[0].?[0]"#, #"let a = \.[0].![0]"#,
        // key paths in argument / subscript position; `??` on the ENCLOSING expression is legal
        #"let a = f(\.name)"#, #"let a = xs.map(\.name)"#, #"let a = x[keyPath: \.foo]"#,
        #"let a = x[keyPath: \.foo] ?? y"#, #"let a = f(\.a, \.b)"#,
        #"let a = cond ? \Foo.bar : \Foo.baz"#, #"let a = [\Foo.bar, \Foo.baz]"#,
        #"let a = (\Foo.bar).hashValue"#,
    ]

    static let rawRejectedRecovery: [String] = [
        #"let a = \Foo ?? fallback"#,
        #"let a = \Foo.bar ?? fallback"#,
        #"let a = \.foo ?? fallback"#,
        #"let a = \Foo.p.?.[0]"#,
    ]

    @Test("agrees with swift-syntax on acceptance", arguments: agreeing)
    func acceptance(_ source: String) throws {
        // STRICT oracle: swift must have parsed CLEANLY, not merely without `hasError` — Advent
        // is a recognizer and should reject exactly where swift would have recovered.
        let expected = swiftSyntaxParsesCleanly(source)
        let actual = try adventParse(source) != nil
        #expect(actual == expected,
                "swift-syntax \(expected ? "accepts" : "rejects") but Advent \(actual ? "accepts" : "rejects"): \(source)")
    }

    @Test("no residual ambiguity", arguments: agreeing)
    func unambiguous(_ source: String) throws {
        guard let result = try adventParse(source) else { return }
        #expect(result.isUnambiguous, "Residual ambiguity: \(source)")
    }

    @Test("trees match", arguments: agreeing)
    func treesMatch(_ source: String) throws {
        guard swiftSyntaxParsesCleanly(source) else { return }
        guard let tree = try adventSwiftSyntaxTree(source) else { return }
        #expect(dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
                == dumpSwiftSyntaxNode(Syntax(Parser.parse(source: source)), indent: 0),
                "Trees differ: \(source)")
    }

    @Test("swift-syntax recovery cases do not raw-match before Oracle", arguments: rawRejectedRecovery)
    func rawRecognizerRejectsRecovery(_ source: String) throws {
        #expect(!swiftSyntaxParsesCleanly(source), "swift-syntax unexpectedly parses cleanly: \(source)")
        let grammar = loadFreshSwiftGrammar()
        let parser = MessageParser(grammar: grammar)
        parser.parse(input: source)
        let root = parser.currentParseRoot ?? grammar.root
        let matched = parser.yield(of: root).contains { y in
            guard y.i == source.startIndex else { return false }
            if y.j == source.endIndex { return true }
            return !parser.lexer.lex(at: y.j, terminalID: grammar.eosID).isEmpty
        }
        #expect(!matched, "Advent raw recognizer matched SwiftSyntax recovery input: \(source)")
    }

}

/// Did swift-syntax parse this CLEANLY, i.e. with no recovery at all?
///
/// STRICTER THAN `!hasError`, deliberately. `hasError` is set only by a MISSING token or a token
/// diagnostic (`SwiftSyntax/Raw/RawSyntax.swift`, `recursiveFlags`); `UnexpectedNodesSyntax` alone
/// does NOT set it. So a tree that recovered by parking tokens in `UnexpectedNodes` reads as a
/// clean accept under `!hasError`, which is too lenient for an acceptance oracle: Advent is a
/// recognizer and should REJECT exactly where swift would have recovered.
func swiftSyntaxParsesCleanly(_ source: String) -> Bool {
    let tree = Parser.parse(source: source)
    if tree.hasError { return false }
    var recovered = false
    func walk(_ node: Syntax) {
        if recovered { return }
        if let unexpected = node.as(UnexpectedNodesSyntax.self), unexpected.count > 0 {
            recovered = true
            return
        }
        for child in node.children(viewMode: .all) { walk(child) }
    }
    walk(Syntax(tree))
    return !recovered
}

/// Whole-file tree equality against swift-syntax, reporting the FIRST differing dump line rather
/// than two multi-megabyte dumps — at file scale the diff itself is the only usable signal.
///
/// Costs nothing by default: both source-file suites are opt-in behind `APUS_SOURCE_FILE_SUITES`,
/// so without it the corpora are empty and these enumerate zero cases.
func expectFileTreeMatches(_ file: SourceFile, sourceLocation: Testing.SourceLocation = #_sourceLocation) throws {
    let text = try String(contentsOf: file.url, encoding: .utf8)
    let reference = Parser.parse(source: text)
    try #require(!reference.hasError,
                 "swift-syntax rejects \(file.testDescription) — bad fixture, not an Advent defect",
                 sourceLocation: sourceLocation)
    guard let tree = adventTreeForFile(text) else {
        Issue.record("Advent produced no tree for \(file.testDescription)", sourceLocation: sourceLocation)
        return
    }
    let advent = dumpSwiftSyntaxNode(Syntax(tree), indent: 0).text
    let expected = dumpSwiftSyntaxNode(Syntax(reference), indent: 0).text
    guard advent != expected else { return }
    let a = advent.split(separator: "\n", omittingEmptySubsequences: false)
    let b = expected.split(separator: "\n", omittingEmptySubsequences: false)
    var line = 0
    while line < min(a.count, b.count), a[line] == b[line] { line += 1 }
    let got = line < a.count ? String(a[line]).trimmingCharacters(in: .whitespaces) : "<end of tree>"
    let exp = line < b.count ? String(b[line]).trimmingCharacters(in: .whitespaces) : "<end of tree>"
    Issue.record("""
        Trees differ for \(file.testDescription) at dump line \(line)
          expected: \(exp)
          actual:   \(got)
        """, sourceLocation: sourceLocation)
}

/// Why the converter could not build a faithful tree for this snippet. Empty does NOT
/// imply the tree matches, but a non-empty list names every place it gave up.
func adventGeneratorDiagnostics(_ snippet: SwiftSnippet) -> [GeneratorDiagnostic] {
    runAdventOnce(
        snippet.source,
        label: snippet.diagnosticID,
        referenceKind: snippet.swiftSyntaxReferenceKind
    ).generatorDiagnostics
}

private func shortLabel(_ source: String) -> String {
    let oneLine = source.replacingOccurrences(of: "\n", with: " ")
    return String(oneLine.prefix(60))
}

// MARK: - Probes

// Focused snippets that exercise the production-body regex lookbehind
// boundaries on plainRegularExpressionLiteral in Swift.apus.
let regexLookbehindSnippets: [SwiftSnippet] = [
    // Division — `--1` blocks regex because the previous token is a value.
    SwiftSnippet(label: "div-int-int",      source: "let x = 1 / 2",            origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "div-ident-ident",  source: "let z = a / b",            origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "div-call-int",     source: "let z = f() / 2",          origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "div-subscript",    source: "let z = arr[0] / 2",       origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "div-chain",        source: "let r = 1 / 2 ; let s = 3 / 4", origin: "RegexLookbehind", syntaxVersion: "603.0.1"),

    // Regex — default allow after expression-starting tokens.
    SwiftSnippet(label: "regex-after-eq",   source: "let r = /abc/",            origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "regex-after-lparen", source: "let r = (/abc/)",        origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "regex-in-array",   source: "let arr = [/abc/]",        origin: "RegexLookbehind", syntaxVersion: "603.0.1"),

    // Compound positive override — eliminates Swift's `preferRegexOverBinaryOperator` hack.
    // NOT newly broken: this row is accepted and always was, but until `treesMatch` was added to
    // this suite (2026-09-17) nothing here compared trees, so the converter gap was invisible.
    SwiftSnippet(label: "regex-after-try-bang",
                 source: #"let m = try! /^x/.wholeMatch(in: "hello")"#,
                 origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "converter tree gap on `try!` + regex + member call; acceptance is fine. Pre-existing, surfaced by this suite's new treesMatch test"),
    SwiftSnippet(label: "regex-after-try-question",
                 source: #"let m = try? /^x/.wholeMatch(in: "hello")"#,
                 origin: "RegexLookbehind", syntaxVersion: "603.0.1"),

    // Ternary — `?` is NOT in the deny list, so the GLL parser finds the ternary parse.
    SwiftSnippet(label: "ternary-with-spaces",
                 source: "let r = b ? /1/ : /2/",
                 origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "ternary-tight",
                 source: "let r = b?/1/:/2/",
                 origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "lookbehind allows regex after '?'; blocked by Swift.apus conditionalOperator's <s> spacing requirement, a separate grammar policy"),

    // INTERIOR SPACES — a KNOWN DEFECT, recorded here so it cannot be forgotten again. The corpus
    // had no fixture with a space inside a `/…/` body, which is why the loss went unseen.
    //
    // `plainRegularExpressionLiteral`'s body is a sequence of TOKENS with trivia skipped between the
    // items, so `regexSpaceAtom` never matches — the space is always consumed as trivia first. The
    // converter's `collectTerminalText` then rebuilds the literal by concatenating COMMITTED
    // terminals, so every interior space is dropped and `/a b/` generates the pattern `ab` — a regex
    // that matches something else entirely, silently. All these rows ACCEPT; they fail `treesMatch`.
    //
    // The fix is to make the body character-tight, which is TODO.md item 13 — attempted 2026-09-17
    // and reverted twice (6 → 45 and 6 → 629 issues); see that item for the two failure modes.
    // `regex-escaped-space` is the control: `\ ` lexes as one `regexEscape` token, so it survives
    // and must keep passing.
    SwiftSnippet(label: "regex-interior-space",       source: "let r = /a b/",     origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior space dropped from the generated pattern (`ab`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-interior-2-spaces",    source: "let r = /a  b/",    origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior spaces dropped from the generated pattern (`ab`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-interior-3-spaces",    source: "let r = /a   b/",   origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior spaces dropped from the generated pattern (`ab`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-interior-space-thrice", source: "let r = /a b c/",  origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior spaces dropped from the generated pattern (`abc`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-interior-space-group", source: "let r = /(a  b)/",  origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior spaces dropped from the generated pattern (`(ab)`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-interior-space-class", source: "let r = /[a b]/",   origin: "RegexLookbehind", syntaxVersion: "603.0.1",
                 disabledReason: "interior space dropped from the generated pattern (`[ab]`) — TODO.md / Keep regex literal text reconstruction faithful"),
    SwiftSnippet(label: "regex-escaped-space",        source: #"let r = /a\ b/"#,  origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "slash-comment-after-operator", source: "let x = true\nlet r = /x*// / value", origin: "RegexLookbehind", syntaxVersion: "603.0.1"),
]

@Suite("Regex Lookbehind (Swift.apus integration)", .serialized)
struct RegexLookbehindIntegration {
    @Test("Advent accepts", arguments: regexLookbehindSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let result = try adventParse(snippet)
        #expect(result != nil, "Advent failed to parse: \(snippet.source)")
    }

    /// Acceptance alone cannot see a corrupted literal: `/a b/` parsed fine while generating the
    /// pattern `ab`. Comparing against swift-syntax is what pins the body text, so this suite is
    /// `trees match`-asserting like the Phase suites — a failure here is a regression, not frontier.
    @Test("trees match", arguments: regexLookbehindSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let reference = Parser.parse(source: snippet.source)
        try #require(!reference.hasError, "fixture is not valid Swift: \(snippet.source)")
        let refDump = dumpSwiftSyntaxNode(Syntax(reference), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            """)
    }
}

// MARK: - Phase 1 tree fidelity
//
// Phase 1 of `SwiftSyntax Mapping.md`: literals and simple `let`/`var`
// declarations. Unlike the extracted SwiftSyntax suites — where `trees match`
// is an aspirational frontier — every row here is expected to match exactly.
// A failure is a regression in `GenerateSwiftSyntaxAST.swift`.
let phase1Snippets: [SwiftSnippet] = [
    // constantDeclaration / variableDeclaration
    SwiftSnippet(label: "let-int",        source: "let x = 42",        origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "var-bool-true",  source: "var b = true",      origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "var-bool-false", source: "var b = false",     origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-nil",        source: "let n = nil",       origin: "Phase1", syntaxVersion: "603.0.1"),

    // integerLiteral in all four radices, plus digit grouping
    SwiftSnippet(label: "let-hex",        source: "let h = 0x1F",      origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-octal",      source: "let o = 0o17",      origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-binary",     source: "let b = 0b1010",    origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-grouped",    source: "let g = 1_000_000", origin: "Phase1", syntaxVersion: "603.0.1"),

    // floatLiteral
    SwiftSnippet(label: "let-float",      source: "let f = 1.5",       origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-exponent",   source: "let e = 1e10",      origin: "Phase1", syntaxVersion: "603.0.1"),

    // stringLiteral
    SwiftSnippet(label: "let-string",     source: #"let s = "hello""#, origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-empty-str",  source: #"let s = """#,      origin: "Phase1", syntaxVersion: "603.0.1"),

    // typeAnnotation / typeIdentifier / optionalType
    SwiftSnippet(label: "let-annotated",  source: "let t: Int = 0",    origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "let-optional",   source: "let n: Int? = nil", origin: "Phase1", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "var-no-init",    source: "var y: Int",        origin: "Phase1", syntaxVersion: "603.0.1"),

    // patternInitializerList with more than one binding
    SwiftSnippet(label: "let-two-bindings", source: "let a = 1, c = 2", origin: "Phase1", syntaxVersion: "603.0.1"),

    // identifier reference on the right-hand side
    SwiftSnippet(label: "let-ident-rhs",  source: "let y = x",         origin: "Phase1", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 1 literals & simple declarations")
struct Phase1TreeTests {

    @Test("Advent accepts", arguments: phase1Snippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase1Snippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none — the converter believed it handled every node)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    /// Phase 1 sources must be built entirely from rules the converter understands.
    /// A `.lookupFailed` anywhere means a rule comment has drifted from `Swift.apus`;
    /// an `.unhandled` means a Phase 1 construct is silently degrading.
    @Test("converter reports no fallbacks", arguments: phase1Snippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Corpus-wide triage of the AST converter's fallback sites. Not a pass/fail gate on
/// tree fidelity — it answers "WHY can't these trees match?" in one run, so phase work
/// is driven by the biggest cause rather than by whichever label was eyeballed last.
///
/// `.lookupFailed` IS asserted: it means a rule the converter claims to handle didn't
/// yield its expected child, which is a bug regardless of which phase we're in.
/// Phase 3 of `SwiftSyntax Mapping.md`, first slice: function declarations.
/// `functionDeclaration` was the single largest cause of tree mismatch (410 of 3313
/// converter fallbacks), so it leads the tree-fidelity work.
let phase3FunctionSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "func-empty",        source: "func f() {}",                    origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-no-body",      source: "func f()",                       origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-return",       source: "func f() -> Int {}",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-one-param",    source: "func f(x: Int) {}",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-two-params",   source: "func f(x: Int, y: Int) {}",      origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-wildcard",     source: "func f(_ x: Int) {}",            origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-two-names",    source: "func f(to x: Int) {}",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-default",      source: "func f(x: Int = 0) {}",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-optional-ret", source: "func f() -> Int? {}",            origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-throws",       source: "func f() throws {}",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-async",        source: "func f() async {}",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-async-throws", source: "func f() async throws -> Int {}", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-rethrows",     source: "func f() rethrows {}",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-body-stmt",    source: "func f() { let x = 1 }",         origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-param-and-body", source: "func f(x: Int) { let y = x }", origin: "Phase3", syntaxVersion: "603.0.1"),
]

/// Phase 4, fourth slice: attributes and generic parameter clauses. Both hang off every
/// declaration, so they pay off across the corpus rather than at one node type.
let phase4AttrSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "attr-func",       source: "@discardableResult func f() -> Int {}", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-struct",     source: "@frozen struct S {}",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-two",        source: "@objc @MainActor class C {}",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-with-modifier", source: "@objc public func f() {}",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-var",        source: "@objc var x = 1",                     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-extension",  source: "@objc extension S {}",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-func",    source: "func f<T>(x: T) {}",                  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-func-2",  source: "func f<T, U>(x: T, y: U) {}",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-bound",   source: "func f<T: Equatable>(x: T) {}",       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-struct",  source: "struct S<T> {}",                      origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-class-bound", source: "class C<T: Equatable> {}",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-enum",    source: "enum E<T> { case a(T) }",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-and-attr", source: "@objc func f<T>(x: T) {}",           origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 attributes & generic parameters")
struct Phase4AttrTests {

    @Test("Advent accepts", arguments: phase4AttrSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4AttrSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4AttrSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, third slice: closures — signatures, capture lists, shorthand vs parenthesised
/// parameters, and trailing-closure calls.
let phase4ClosureSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "closure-empty",     source: "let a = { }",                        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-body",      source: "let a = { f() }",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-shorthand", source: "let a = { x in x }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-shorthand2", source: "let a = { x, y in x }",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-wildcard",  source: "let a = { _ in 1 }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-typed",     source: "let a = { (x: Int) in x }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-typed2",    source: "let a = { (x: Int, y: Int) in x }",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-result",    source: "let a = { (x: Int) -> Int in x }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-noparams-result", source: "let a = { () -> Int in 1 }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-throws",    source: "let a = { () throws -> Int in 1 }",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-async",     source: "let a = { () async -> Int in 1 }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "capture-weak-self", source: "let a = { [weak self] in f() }",     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "capture-unowned",   source: "let a = { [unowned self] in f() }",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "capture-named",     source: "let a = { [x] in x }",               origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "capture-init",      source: "let a = { [x = y] in x }",           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "capture-empty",     source: "let a = { [] in f() }",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "trailing-only",     source: "let a = f { 1 }",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "trailing-with-args", source: "let a = f(1) { 2 }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "trailing-labeled",  source: "let a = f { 1 } g: { 2 }",           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "closure-in-call",   source: "let a = xs.map { $0 }",              origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 closures")
struct Phase4ClosureTests {

    @Test("Advent accepts", arguments: phase4ClosureSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4ClosureSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4ClosureSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, second slice: initializer and operator declarations, and the `->` arrow as an
/// element of a flat operator sequence.
let phase4DeclSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "init-empty",      source: "struct S { init() {} }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-params",     source: "struct S { init(x: Int) {} }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-failable",   source: "struct S { init?(x: Int) {} }",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-iuo",        source: "struct S { init!(x: Int) {} }",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-throws",     source: "struct S { init() throws {} }",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-async",      source: "struct S { init() async {} }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-modifier",   source: "class C { public init() {} }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "init-body",       source: "struct S { init() { x = 1 } }",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-infix",        source: "infix operator +++",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-prefix",       source: "prefix operator +++",                   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-postfix",      source: "postfix operator +++",                  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-precedence",   source: "infix operator +++ : AdditionPrecedence", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "arrow-in-seq",    source: "let a = (Int) -> Bool",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "arrow-throws",    source: "let a = (Int) throws -> Bool",          origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 init/operator declarations")
struct Phase4DeclTests {

    @Test("Advent accepts", arguments: phase4DeclSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4DeclSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4DeclSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4: the type grammar — tuple types, function types, generic argument clauses,
/// dot-qualified member types, and `Any`.
let phase4TypeSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "generic-type",    source: "let a: Array<Int> = []",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-two",     source: "let a: Dictionary<String, Int> = [:]", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-nested",  source: "let a: Array<Array<Int>> = []",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "member-type",     source: "let a: A.B = x",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "member-type-3",   source: "let a: A.B.C = x",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "member-generic",  source: "let a: A.B<Int> = x",           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "any-type",        source: "let a: Any = x",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-type",      source: "let a: (Int, String) = x",      origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-type-label", source: "let a: (x: Int, y: Int) = p",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-type",       source: "let a: () -> Void = f",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-type-args",  source: "let a: (Int, String) -> Bool = f", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-type-throws", source: "let a: () throws -> Int = f",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-type-async", source: "let a: () async -> Int = f",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-type-nested", source: "let a: (Int) -> (Int) -> Int = f", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-expr",    source: "let a = f<Int>",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-call",    source: "let a = f<Int>()",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-member",  source: "let a = x.f<Int>",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "generic-member-call", source: "let a = x.f<Int>()",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "optional-generic", source: "let a: Array<Int>? = nil",     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "func-returns-generic", source: "func f() -> Array<Int> {}", origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 types & generics")
struct Phase4TypeTests {

    @Test("Advent accepts", arguments: phase4TypeSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4TypeSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4TypeSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 3, sixth slice: `if`/`switch` as EXPRESSIONS (swift-syntax models both that way in
/// statement position too), plus `guard`, condition lists, optional binding and match patterns.
let phase3BranchSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "if-simple",      source: "func f() { if c { g() } }",                  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-else",        source: "func f() { if c { g() } else { h() } }",     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-else-if",     source: "func f() { if c { g() } else if d { h() } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-let",         source: "func f() { if let x = y { g() } }",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-var",         source: "func f() { if var x = y { g() } }",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-two-conds",   source: "func f() { if a, b { g() } }",               origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-let-plus",    source: "func f() { if let x = y, x > 0 { g() } }",   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "guard-let",      source: "func f() { guard let x = y else { return } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "guard-expr",     source: "func f() { guard c else { return } }",       origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "switch-default", source: "func f() { switch x { default: g() } }",     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "switch-case",    source: "func f() { switch x { case 1: g()\ndefault: h() } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "switch-bind",    source: "func f() { switch x { case let y: g(y) } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "switch-where",   source: "func f() { switch x { case let y where y > 0: g() \ndefault: h() } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "switch-two-items", source: "func f() { switch x { case 1, 2: g()\ndefault: h() } }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-expression",  source: "let a = if c { 1 } else { 2 }",              origin: "Phase3", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 3 if/switch/guard")
struct Phase3BranchTests {

    @Test("Advent accepts", arguments: phase3BranchSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3BranchSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3BranchSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 3, fifth slice: declaration modifiers — `static`, `final`, access levels and the
/// `private(set)` detail form. These feed every declaration's `DeclModifierList`.
let phase3ModifierSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "static-func",     source: "struct S { static func f() {} }",     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "public-func",     source: "public func f() {}",                  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "private-let",     source: "private let x = 1",                   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "public-struct",   source: "public struct S {}",                  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "final-class",     source: "final class C {}",                    origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "public-final",    source: "public final class C {}",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "final-public",    source: "final public class C {}",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "private-set",     source: "struct S { private(set) var x = 1 }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "static-let",      source: "struct S { static let x = 1 }",       origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "open-class",      source: "open class C {}",                     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "public-ext",      source: "public extension S {}",               origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "indirect-enum",   source: "indirect enum E { case a }",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "mutating-func",   source: "struct S { mutating func f() {} }",   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "two-modifiers",   source: "struct S { public static func f() {} }", origin: "Phase3", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 3 declaration modifiers")
struct Phase3ModifierTests {

    @Test("Advent accepts", arguments: phase3ModifierSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3ModifierSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3ModifierSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 3, fourth slice: enum case declarations — associated values and raw values.
/// swift-syntax uses ONE `EnumCaseDecl` for both styles, matching the merged grammar rule.
let phase3EnumCaseSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "case-one",        source: "enum E { case a }",                   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-list",       source: "enum E { case a, b, c }",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-separate",   source: "enum E { case a\ncase b }",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-assoc-one",  source: "enum E { case a(Int) }",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-assoc-two",  source: "enum E { case a(Int, String) }",      origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-assoc-label", source: "enum E { case a(x: Int) }",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-raw-int",    source: "enum E: Int { case a = 1 }",          origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-raw-string", source: #"enum E: String { case a = "x" }"#,   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-raw-list",   source: "enum E: Int { case a = 1, b = 2 }",   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-assoc-optional", source: "enum E { case a(Int?) }",         origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-mixed-body", source: "enum E { case a\nfunc f() {} }",      origin: "Phase3", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 3 enum case declarations")
struct Phase3EnumCaseTests {

    @Test("Advent accepts", arguments: phase3EnumCaseSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3EnumCaseSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3EnumCaseSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 3, third slice: control-transfer statements, `try`/`await`, collection
/// types and the non-identifier binding patterns.
let phase3StatementSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "return-void",   source: "func f() { return }",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "return-value",  source: "func f() -> Int { return 1 }",  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "return-expr",   source: "func f() -> Int { return 1 + 2 }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "throw-stmt",    source: "func f() throws { throw e }",   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "try-call",      source: "let a = try f()",               origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "try-optional",  source: "let a = try? f()",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "try-forced",    source: "let a = try! f()",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "await-call",    source: "func f() async { let a = await g() }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "try-infix",     source: "let a = try f() + 1",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "array-type",    source: "let a: [Int] = []",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "dict-type",     source: "let a: [String: Int] = [:]",    origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "nested-array-type", source: "let a: [[Int]] = []",       origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "iuo-type",      source: "let a: Int! = nil",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "metatype",      source: "let a = Int.self",              origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "wildcard-bind", source: "let _ = 1",                     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-bind",    source: "let (x, y) = (1, 2)",           origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-bind-wild", source: "let (x, _) = (1, 2)",         origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-bind-nested", source: "let (x, (y, z)) = (1, (2, 3))", origin: "Phase3", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 3 control transfer, try/await, types & patterns")
struct Phase3StatementTests {

    @Test("Advent accepts", arguments: phase3StatementSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3StatementSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3StatementSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 2: collection literals, tuples, implicit members, regex literals.
let phase2LiteralSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "array-empty",     source: "let a = []",             origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "array-one",       source: "let a = [1]",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "array-three",     source: "let a = [1, 2, 3]",      origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "array-nested",    source: "let a = [[1], [2]]",     origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "dict-empty",      source: "let a = [:]",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "dict-one",        source: #"let a = ["k": 1]"#,     origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "dict-two",        source: #"let a = ["k": 1, "j": 2]"#, origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-two",       source: "let a = (1, 2)",         origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-labelled",  source: "let a = (x: 1, y: 2)",   origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-empty",     source: "let a = ()",             origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "implicit-member", source: "let a: E = .some",       origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "super-member",    source: "class C { func f() { super.g() } }", origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "regex",           source: "let a = /abc/",          origin: "Phase2", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 2 collection literals & tuples")
struct Phase2LiteralTests {

    @Test("Advent accepts", arguments: phase2LiteralSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase2LiteralSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase2LiteralSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 2: flat operator sequences. The interesting rows are assignment and the
/// ternary, where Advent's grammar NESTS a whole `expression` on the right but
/// swift-syntax keeps one flat `SequenceExpr` — the converter has to splice.
let phase2InfixSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "add",             source: "let a = 1 + 2",           origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "add-mul",         source: "let a = 1 + 2 * 3",       origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "compare",         source: "let a = x == 0",          origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assign",          source: "x = 1",                   origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assign-expr",     source: "x = 1 + 2",               origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assign-member",   source: "x.y = 1",                 origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "compound-assign", source: "x += 1",                  origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "ternary",         source: "let a = c ? 1 : 2",       origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "ternary-expr",    source: "let a = c ? 1 + 1 : 2",   origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "is-cast",         source: "let a = x is Int",        origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "as-cast",         source: "let a = x as Int",        origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "as-optional",     source: "let a = x as? Int",       origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "long-chain",      source: "let a = 1 + 2 - 3 * 4",   origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-in-infix",   source: "let a = f() + g(1)",      origin: "Phase2", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 2 infix sequences")
struct Phase2InfixTests {

    @Test("Advent accepts", arguments: phase2InfixSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase2InfixSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase2InfixSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 2: postfix expressions — member access, calls, subscripts, force-unwrap and
/// optional chaining. These rules are LEFT-recursive on `postfixExpression`, which maps
/// directly onto swift-syntax's nested base/expression fields.
let phase2PostfixSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "member",          source: "let a = x.y",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "member-chain",    source: "let a = x.y.z",          origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "tuple-element",   source: "let a = x.0",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-noargs",     source: "let a = f()",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-onearg",     source: "let a = f(1)",           origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-twoargs",    source: "let a = f(1, 2)",        origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-labelled",   source: "let a = f(x: 1)",        origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-mixed",      source: "let a = f(1, y: 2)",     origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "method-call",     source: "let a = x.f()",          origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "call-chain",      source: "let a = f()()",          origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "subscript",       source: "let a = x[0]",           origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "subscript-two",   source: "let a = x[0, 1]",        origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "force-unwrap",    source: "let a = x!",             origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "optional-chain",  source: "let a = x?.y",           origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "self-member",     source: "let a = self.x",         origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "paren-expr",      source: "let a = (x)",            origin: "Phase2", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "mixed-postfix",   source: "let a = x.y[0].z!",      origin: "Phase2", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 2 postfix expressions")
struct Phase2PostfixTests {

    @Test("Advent accepts", arguments: phase2PostfixSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase2PostfixSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase2PostfixSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 3, second slice: the nominal type declarations, which share one
/// member-block shape in `Swift.apus`.
let phase3TypeSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "struct-empty",    source: "struct S {}",                     origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "class-empty",     source: "class C {}",                      origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "enum-empty",      source: "enum E {}",                       origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "protocol-empty",  source: "protocol P {}",                   origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "extension-empty", source: "extension S {}",                  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "struct-inherit",  source: "struct S: P {}",                  origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "struct-inherit2", source: "struct S: P, Q {}",               origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "extension-inherit", source: "extension S: P {}",             origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "struct-one-member", source: "struct S { let x = 1 }",        origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "struct-two-members", source: "struct S { let x = 1\nvar y = 2 }", origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "struct-func",     source: "struct S { func f() {} }",        origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "class-nested",    source: "class C { struct S {} }",         origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "protocol-func",   source: "protocol P { func f() }",         origin: "Phase3", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "extension-func",  source: "extension S { func f() {} }",     origin: "Phase3", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 3 nominal type declarations")
struct Phase3TypeTests {

    @Test("Advent accepts", arguments: phase3TypeSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3TypeSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3TypeSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

@Suite("SwiftSyntax - Phase 3 function declarations")
struct Phase3FunctionTests {

    @Test("Advent accepts", arguments: phase3FunctionSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase3FunctionSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase3FunctionSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// `conditionExpression` is a PARALLEL copy of `expression` that exists only to forbid
/// assignment (assignment returns Void, so it is not a condition). EVERY other difference
/// between the two infix families is drift, because swift draws no other distinction:
/// whatever parses as an expression must parse the same way in a condition.
///
/// Each row is the same operator form in both positions. `adventAccepts` asserts parity of
/// acceptance; `unambiguous` asserts the condition form did not pick up an extra reading.
struct InfixParityCase: CustomTestStringConvertible, Sendable {
    let label: String
    let expressionForm: String
    let conditionForm: String
    var testDescription: String { label }
}

let infixParityCases: [InfixParityCase] = [
    .init(label: "amp-spaced",   expressionForm: "let z = a & b",            conditionForm: "if a & b { g() }"),
    .init(label: "amp-tight",    expressionForm: "let z = a&b",              conditionForm: "if a&b { g() }"),
    .init(label: "div-chain",    expressionForm: "let z = a/b/c",            conditionForm: "if a/b/c { g() }"),
    .init(label: "dot-operator", expressionForm: "let z = a...b",            conditionForm: "if a...b { g() }"),
    .init(label: "force-member", expressionForm: "let z = x!.y",             conditionForm: "if x!.y { g() }"),
    .init(label: "ternary-try-then",  expressionForm: "let z = c ? try f() : g()", conditionForm: "if c ? try f() : g() { h() }"),
    // The FALSE branch is the one that matters: `conditionalOperator` holds the then-branch
    // internally, so the extra `tryOperator? awaitOperator?` in `conditionInfixExpression`
    // sits in front of the false branch — where `expression` already supplies its own.
    .init(label: "ternary-try-else",  expressionForm: "let z = c ? f() : try g()", conditionForm: "if c ? f() : try g() { h() }"),
    .init(label: "ternary-await-else", expressionForm: "let z = c ? f() : await g()", conditionForm: "if c ? f() : await g() { h() }"),
    .init(label: "ternary-try-both",  expressionForm: "let z = c ? try f() : try g()", conditionForm: "if c ? try f() : try g() { h() }"),
]

@Suite("Grammar - condition/expression infix parity")
struct ConditionInfixParityTests {

    /// Why the `conditionExpression` duplication CANNOT simply be replaced by
    /// `infixExpression = @excludedFrom(condition) assignmentOperator expression .`
    ///
    /// `ContainmentRule` is pure SPAN containment — it prunes a reading whose span lies inside any
    /// yield of the container nonterminal (`$0.i <= span.i && span.j <= $0.j`). It is not an
    /// ancestor walk and knows nothing about scope boundaries. An assignment inside a CLOSURE that
    /// is itself inside a condition is lexically contained in the `condition` span, so
    /// `@excludedFrom(condition)` would prune it — even though it is perfectly legal Swift.
    ///
    /// The duplication gets this right for free: a closure body re-enters through
    /// `statements → statement → expression`, i.e. the UNRESTRICTED family, so the restriction
    /// naturally stops at the scope boundary. Any factoring proposed in TODO 25 must keep this
    /// case parsing.
    @Test("assignment inside a closure inside a condition is legal")
    func assignmentInClosureInsideCondition() throws {
        let source = "func f() { if xs.contains(where: { c in count = 1; return true }) { g() } }"
        #expect(!Parser.parse(source: source).hasError, "swift-syntax rejected the premise")
        #expect(try adventParse(source) != nil, """
            Advent rejected an assignment nested in a closure inside a condition. If this broke             after replacing the conditionExpression family with @excludedFrom(condition), that is             the span-containment-vs-scope problem, not a grammar bug in this snippet.
            """)
    }

    @Test("condition position accepts whatever expression position accepts", arguments: infixParityCases)
    func acceptanceParity(_ c: InfixParityCase) throws {
        let exprOK = try adventParse(c.expressionForm) != nil
        let condOK = try adventParse(c.conditionForm) != nil
        #expect(exprOK == condOK, """
            '\(c.label)': expression position \(exprOK ? "accepts" : "REJECTS"),             condition position \(condOK ? "accepts" : "REJECTS") — the two infix families             differ by more than the (deliberate) absence of assignment.
              expr: \(c.expressionForm)
              cond: \(c.conditionForm)
            """)
    }

    @Test("condition position stays unambiguous", arguments: infixParityCases)
    func conditionUnambiguous(_ c: InfixParityCase) throws {
        guard let r = try adventParse(c.conditionForm) else { return }   // acceptance covered above
        #expect(r.isUnambiguous, "'\(c.label)' is ambiguous in condition position: \(r.builder.diagnostics)")
    }
}

/// Phase 4, fifteenth slice: coroutine accessors and operator designated types.
let phase4CoroutineSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "coroutine-read",   source: "struct S { var x: Int { _read { yield v } } }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "coroutine-modify", source: "struct S { var x: Int { _modify { yield &v } } }",       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "coroutine-both",   source: "struct S { var x: Int { _read { yield v } _modify { yield &v } } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-designated",    source: "infix operator +++ : AdditionPrecedence, Int",           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "op-trailing-comma", source: "infix operator +++ : AdditionPrecedence,",              origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 coroutine accessors & designated types")
struct Phase4CoroutineTests {

    @Test("Advent accepts", arguments: phase4CoroutineSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4CoroutineSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, fourteenth slice: enum-case patterns, tuple match patterns, suppressed conformances.
let phase4PatternSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "case-enum",        source: "func f() { switch x { case .a: g()\ndefault: h() } }",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-enum-assoc",  source: "func f() { switch x { case .a(let y): g(y)\ndefault: h() } }",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-enum-qualified", source: "func f() { switch x { case E.a: g()\ndefault: h() } }",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-enum-two",    source: "func f() { switch x { case .a(let y, let z): g()\ndefault: h() } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-enum-label",  source: "func f() { switch x { case .a(v: let y): g(y)\ndefault: h() } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-tuple",       source: "func f() { switch x { case (1, 2): g()\ndefault: h() } }",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-tuple-bind",  source: "func f() { switch x { case (let a, let b): g()\ndefault: h() } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "case-optional-tuple", source: "struct Foo {}\nfunc f<T>(value: Optional<T>) { if case (.some(let x), _ as Foo.Type)? = Optional((value, Foo.self)) { _ = x } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "suppressed",       source: "struct S: ~Copyable {}",                                           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "suppressed-plus",  source: "struct S: ~Copyable, P {}",                                        origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 enum-case & tuple patterns")
struct Phase4PatternTests {

    @Test("Advent accepts", arguments: phase4PatternSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4PatternSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, thirteenth slice: precedence groups, macro declarations, postfix operators.
let phase4PrecedenceSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "pg-empty",      source: "precedencegroup P {}",                                   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-higher",     source: "precedencegroup P { higherThan: AdditionPrecedence }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-lower",      source: "precedencegroup P { lowerThan: AdditionPrecedence }",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-two-names",  source: "precedencegroup P { higherThan: A, B }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-assignment", source: "precedencegroup P { assignment: true }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-assoc-left", source: "precedencegroup P { associativity: left }",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-assoc-none", source: "precedencegroup P { associativity: none }",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "pg-multi",      source: "precedencegroup P { associativity: left\nhigherThan: A }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-decl",    source: "macro m() = #externalMacro(module: \"M\", type: \"T\")",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-decl-result", source: "macro m() -> Int = #externalMacro(module: \"M\", type: \"T\")", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-decl-params", source: "macro m(x: Int) = #externalMacro(module: \"M\", type: \"T\")", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "postfix-op",    source: "postfix operator ^^\nlet a = x^^",                       origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 precedence groups, macro decls, postfix operators")
struct Phase4PrecedenceTests {

    @Test("Advent accepts", arguments: phase4PrecedenceSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4PrecedenceSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, twelfth slice: `#if` conditional compilation and extended `#/…/#` regex literals.
let phase4IfConfigSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "if-simple",     source: "#if DEBUG\nlet a = 1\n#endif",                     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-else",       source: "#if DEBUG\nlet a = 1\n#else\nlet a = 2\n#endif",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-elseif",     source: "#if A\nlet a = 1\n#elseif B\nlet a = 2\n#endif",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-not",        source: "#if !DEBUG\nlet a = 1\n#endif",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-and",        source: "#if A && B\nlet a = 1\n#endif",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-or",         source: "#if A || B\nlet a = 1\n#endif",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-paren",      source: "#if (A)\nlet a = 1\n#endif",                       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-bool",       source: "#if true\nlet a = 1\n#endif",                      origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-call",       source: "#if os(macOS)\nlet a = 1\n#endif",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-empty",      source: "#if DEBUG\n#endif",                                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-member-list", source: "struct Fuzz {\nlet a = 1\n#if DEBUG\nlet b = 2\n#endif\n#warning(\"seed\")\n}", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "regex-extended", source: "let a = #/abc/#",                                   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "regex-plain",    source: "let a = /abc/",                                     origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 #if and extended regex")
struct Phase4IfConfigTests {

    @Test("Advent accepts", arguments: phase4IfConfigSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4IfConfigSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, eleventh slice: raw and multiline string literals — pound delimiters are their
/// own tokens in swift-syntax, and the multiline form uses a distinct quote token.
let phase4StringSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "raw-simple",    source: "let a = #\"abc\"#",               origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "raw-double",    source: "let a = ##\"abc\"##",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "raw-quote",     source: "let a = #\"say \\\"hi\\\"\"#", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "raw-empty",     source: "let a = #\"\"#",                  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline",     source: "let a = \"\"\"\nabc\n\"\"\"",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline-indent", source: "let a = \"\"\"\n    abc\n    \"\"\"", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "raw-multiline", source: "let a = #\"\"\"\nabc\n\"\"\"#",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline-2line", source: "let a = \"\"\"\nabc\ndef\n\"\"\"", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline-3line", source: "let a = \"\"\"\nabc\ndef\nghi\n\"\"\"", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline-2line-indent", source: "let a = \"\"\"\n    abc\n    def\n    \"\"\"", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "multiline-blank",  source: "let a = \"\"\"\nabc\n\ndef\n\"\"\"", origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 raw & multiline strings")
struct Phase4StringTests {

    @Test("Advent accepts", arguments: phase4StringSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4StringSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, tenth slice: key-path expressions. The grammar's component rules are a flag
/// machine (property-run vs pivot) that swift-syntax flattens into one component list.
let phase4KeyPathSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "kp-rootless",     source: "let a = \\.foo",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-rooted",       source: "let a = \\Foo.bar",           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-chain",        source: "let a = \\Foo.bar.baz",       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-rootless-chain", source: "let a = \\.foo.bar",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-optional",     source: "let a = \\Foo.bar?",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-force",        source: "let a = \\Foo.bar!",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-subscript",    source: "let a = \\Foo.bar[0]",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-bare-subscript", source: "let a = \\Foo[0]",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-generic-root", source: "let a = \\Array<Int>.count",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-mixed",        source: "let a = \\Foo.bar?.baz",      origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "kp-tuple-index",  source: "let a = \\Foo.0",             origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 key paths")
struct Phase4KeyPathTests {

    @Test("Advent accepts", arguments: phase4KeyPathSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4KeyPathSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4KeyPathSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, ninth slice: imports, actors, associated types and `if case` conditions.
let phase4ImportSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "import-simple",   source: "import Foundation",                     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "import-dotted",   source: "import A.B.C",                          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "import-kind",     source: "import struct Foundation.Data",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "import-func",     source: "import func A.b",                       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "actor-empty",     source: "actor A {}",                            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "actor-member",    source: "actor A { var x = 1 }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "actor-inherit",   source: "actor A: P {}",                         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assoc-type",      source: "protocol P { associatedtype T }",       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assoc-bound",     source: "protocol P { associatedtype T: Equatable }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "assoc-default",   source: "protocol P { associatedtype T = Int }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-case",         source: "func f() { if case .a = x { g() } }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "if-case-let",     source: "func f() { if case let .a(y) = x { g(y) } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "guard-case",      source: "func f() { guard case .a = x else { return } }", origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 imports, actors, associatedtype, if-case")
struct Phase4ImportTests {

    @Test("Advent accepts", arguments: phase4ImportSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4ImportSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4ImportSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, eighth slice: macro expansions, `&` inout expressions, and the ownership
/// prefix operators — each of which has its OWN swift-syntax node, not PrefixOperatorExpr.
let phase4MacroSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "macro-bare",     source: "let a = #line",                     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-args",     source: #"let a = #warning("x")"#,           origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-noargs",   source: "let a = #foo()",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-labelled", source: "let a = #foo(x: 1, y: 2)",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-generic",  source: "let a = #foo<Int>()",               origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "macro-trailing", source: "let a = #foo { 1 }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "inout-arg",      source: "func f() { g(&x) }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "inout-member",   source: "func f() { g(&x.y) }",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "consume",        source: "func f() { let a = consume x }",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "borrow",         source: "func f() { let a = borrow x }",     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "copy",           source: "func f() { let a = copy x }",       origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 macros, inout, ownership operators")
struct Phase4MacroTests {

    @Test("Advent accepts", arguments: phase4MacroSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4MacroSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4MacroSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, seventh slice: loops, do/catch, deinitializers and subscripts.
let phase4LoopSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "for-in",        source: "func f() { for x in xs { g(x) } }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "for-in-where",  source: "func f() { for x in xs where x > 0 { g(x) } }",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "for-case",      source: "func f() { for case let x in xs { g(x) } }",       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "for-wildcard",  source: "func f() { for _ in xs { g() } }",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "while",         source: "func f() { while c { g() } }",                     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "while-let",     source: "func f() { while let x = y { g(x) } }",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "repeat-while",  source: "func f() { repeat { g() } while c }",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "do-plain",      source: "func f() { do { g() } }",                          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "do-catch",      source: "func f() { do { g() } catch { h() } }",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "do-catch-pat",  source: "func f() { do { g() } catch E.a { h() } }",        origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "do-two-catch",  source: "func f() { do { g() } catch E.a { h() } catch { i() } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "deinit",        source: "class C { deinit {} }",                            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "deinit-body",   source: "class C { deinit { g() } }",                       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "subscript",     source: "struct S { subscript(i: Int) -> Int { 0 } }",      origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "subscript-getset", source: "struct S { subscript(i: Int) -> Int { get { 0 } set { } } }", origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 loops, do/catch, deinit, subscript")
struct Phase4LoopTests {

    @Test("Advent accepts", arguments: phase4LoopSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4LoopSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4LoopSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, sixth slice: computed properties and accessor blocks. These bypass
/// `patternInitializerList` in the grammar but are still ONE PatternBinding in swift-syntax.
let phase4AccessorSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "computed-shorthand", source: "struct S { var x: Int { 0 } }",                    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "computed-get",       source: "struct S { var x: Int { get { 0 } } }",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "computed-get-set",   source: "struct S { var x: Int { get { 0 } set { y = newValue } } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "protocol-get",       source: "protocol P { var x: Int { get } }",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "protocol-get-set",   source: "protocol P { var x: Int { get set } }",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "setter-name",        source: "struct S { var x: Int { get { 0 } set(v) { y = v } } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "accessor-modifier",  source: "struct S { var x: Int { mutating get { 0 } } }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "accessor-throws",    source: "protocol P { var x: Int { get throws } }",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "accessor-async",     source: "protocol P { var x: Int { get async } }",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "computed-static",    source: "struct S { static var x: Int { 0 } }",             origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 accessors")
struct Phase4AccessorTests {

    @Test("Advent accepts", arguments: phase4AccessorSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4AccessorSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4AccessorSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// Phase 4, fifth slice: `typealias`, attributed / specifier-prefixed types, and
/// `#available` conditions.
let phase4MiscSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "typealias",        source: "typealias A = Int",                       origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "typealias-generic", source: "typealias A<T> = Array<T>",              origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "typealias-public", source: "public typealias A = Int",                origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "typealias-func",   source: "typealias A = (Int) -> Bool",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "inout-param",      source: "func f(x: inout Int) {}",                 origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "borrowing-param",  source: "func f(x: borrowing Int) {}",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "consuming-param",  source: "func f(x: consuming Int) {}",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "attr-type",        source: "let a: @Sendable () -> Void = f",         origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-cond",       source: "func f() { if #available(macOS 10.15, *) { g() } }",   origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "unavail-cond",     source: "func f() { if #unavailable(macOS 10.15) { g() } }",    origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-cond-two",   source: "func f() { if #available(macOS 10.15, iOS 13.0, *) { g() } }", origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-cond-guard", source: "func f() { guard #available(macOS 10.15, *) else { return } }", origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 typealias, attributed types, #available")
struct Phase4MiscTests {

    @Test("Advent accepts", arguments: phase4MiscSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4MiscSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4MiscSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// `@available` — the one attribute whose arguments now have a real grammar rather than
/// balanced-token soup.
let phase4AvailableSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "avail-star",        source: "@available(*, deprecated) func f() {}",             origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-platform",    source: "@available(macOS 10.15, *) func f() {}",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-two-plat",    source: "@available(macOS 10.15, iOS 13.0, *) func f() {}",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-three-part",  source: "@available(macOS 10.15.1, *) func f() {}",          origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-message",     source: #"@available(*, deprecated, message: "use g") func f() {}"#, origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-renamed",     source: #"@available(*, deprecated, renamed: "g") func f() {}"#,     origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-introduced",  source: "@available(macOS, introduced: 10.15) func f() {}",  origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-unavailable", source: "@available(*, unavailable) func f() {}",            origin: "Phase4", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "avail-on-struct",   source: "@available(macOS 10.15, *) struct S {}",            origin: "Phase4", syntaxVersion: "603.0.1"),
]

@Suite("SwiftSyntax - Phase 4 @available")
struct Phase4AvailableTests {

    @Test("Advent accepts", arguments: phase4AvailableSnippets)
    func adventAccepts(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        #expect(try adventParse(snippet) != nil, "Advent failed to parse: \(snippet.source)")
    }

    @Test("trees match", arguments: phase4AvailableSnippets)
    func treesMatch(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let refDump = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
        guard let adventTree = try adventSwiftSyntaxTree(snippet) else {
            Issue.record("Advent produced no SwiftSyntax tree for: \(snippet.source)")
            return
        }
        let adventDump = dumpSwiftSyntaxNode(Syntax(adventTree), indent: 0)
        let why = adventGeneratorDiagnostics(snippet)
        #expect(refDump == adventDump, """
            Trees differ for '\(snippet.diagnosticID)' — \(snippet.source)
            --- swift-syntax ---
            \(refDump)
            --- advent ---
            \(adventDump)
            --- converter fallbacks ---
            \(why.isEmpty ? "(none)" : why.map(\.description).joined(separator: "\n"))
            """)
    }

    @Test("converter reports no fallbacks", arguments: phase4AvailableSnippets)
    func noConverterFallbacks(_ snippet: SwiftSnippet) throws {
        guard snippet.disabledReason == nil else { return }
        let diagnostics = adventGeneratorDiagnostics(snippet)
        #expect(diagnostics.isEmpty, """
            Converter fell back on '\(snippet.diagnosticID)' — \(snippet.source)
            \(diagnostics.map(\.description).joined(separator: "\n"))
            """)
    }
}

/// `attributeArgumentClause = >s< "(" balancedTokens? ")"` accepts ANY balanced token sequence
/// inside an attribute's parentheses. That is an over-generality question, not just a tree-shape
/// one: these rows are inputs the COMPILER rejects, and the soup lets them through.
///
/// Red rows here are the case for replacing the soup with real argument grammars. `@available`
/// is the interesting one, because the grammar ALREADY has `availabilityArguments` — it is used
/// by `availabilityCondition` (`#available(…)`) and simply not reused by `availableAttribute`.
let attributeSoupSnippets: [SwiftSnippet] = [
    SwiftSnippet(label: "available-garbage",   source: "@available(!!! ??? ***) func f() {}", origin: "AttrSoup", syntaxVersion: "603.0.1"),
    // NOT included: `@available(macOS 10.15)` (no `*`). Probed — swift-syntax ACCEPTS it, so it
    // is not evidence of over-generality here even though the compiler wants the `*`.
    SwiftSnippet(label: "available-nonsense",  source: "@available(1 + 2) func f() {}",       origin: "AttrSoup", syntaxVersion: "603.0.1"),
    SwiftSnippet(label: "objc-garbage",        source: "@objc(+++) func f() {}",              origin: "AttrSoup", syntaxVersion: "603.0.1"),
]

@Suite("Grammar - attribute argument over-generality")
struct AttributeSoupTests {

    @Test("swift-syntax verdict is the premise", .tags(.swiftSyntaxReference), arguments: attributeSoupSnippets)
    func swiftSyntaxRejects(_ snippet: SwiftSnippet) throws {
        #expect(Parser.parse(source: snippet.source).hasError,
                "premise failed — swift-syntax accepts '\(snippet.source)'")
    }

    @Test("Advent rejects too", arguments: attributeSoupSnippets)
    func adventRejects(_ snippet: SwiftSnippet) throws {
        #expect(try adventParse(snippet.source) == nil,
                "attribute token soup accepted invalid input: \(snippet.source)")
    }
}

@Suite("SwiftSyntax - Converter fallback triage")
struct ConverterFallbackTriage {

    static let corpus: [SwiftSnippet] =
        declarationSnippets + expressionSnippets + statementSnippets
        + typeSnippets + patternSnippets + attributeSnippets + translatedSnippets

    @Test("no lookupFailed anywhere in the accept corpus")
    func noLookupFailures() throws {
        var tally: [String: Int] = [:]
        var unhandled: [String: Int] = [:]
        var failures: [String] = []
        var samples: [String: [String]] = [:]

        for snippet in Self.corpus where snippet.disabledReason == nil {
            for d in adventGeneratorDiagnostics(snippet) {
                let key = "\(d.function): \(d.reason)"
                switch d.kind {
                case .lookupFailed:
                    tally[key, default: 0] += 1
                    if failures.count < 20 { failures.append("\(snippet.diagnosticID): \(d)") }
                case .unhandled:
                    unhandled[key, default: 0] += 1
                }
                if samples[key, default: []].count < 6 {
                    samples[key, default: []].append("\(snippet.diagnosticID) «\(d.text.prefix(60))»")
                }
            }
        }

        // How many DIFFERING labels have no diagnostic at all? The fallback tally only accounts
        // for gaps the converter KNOWS about; a snippet can differ while the converter believes
        // it handled every node. Those silent mismatches are invisible in the tally above and are
        // the honest denominator for "what is left".
        var differing = 0, differingSilent = 0, matching = 0
        var silentCauses: [String: Int] = [:]
        var silentSamples: [String: [String]] = [:]
        for snippet in Self.corpus where snippet.disabledReason == nil {
            let ref = dumpSwiftSyntaxNode(Syntax(Parser.parse(source: snippet.source)), indent: 0)
            guard let tree = try? adventSwiftSyntaxTree(snippet) else { continue }
            let mine = dumpSwiftSyntaxNode(Syntax(tree), indent: 0)
            if mine == ref { matching += 1; continue }
            differing += 1
            guard adventGeneratorDiagnostics(snippet).isEmpty else { continue }
            differingSilent += 1
            // Rank the SILENT mismatches by their FIRST divergent line. That converts
            // "260 unknown" into a work queue, the same way `alternateKind` did for the
            // declaration/statement buckets.
            let refLines = ref.text.split(separator: "\n", omittingEmptySubsequences: false)
            let mineLines = mine.text.split(separator: "\n", omittingEmptySubsequences: false)
            var i = 0
            while i < refLines.count, i < mineLines.count, refLines[i] == mineLines[i] { i += 1 }
            let expected = i < refLines.count ? refLines[i].trimmingCharacters(in: .whitespaces) : "<end>"
            let got = i < mineLines.count ? mineLines[i].trimmingCharacters(in: .whitespaces) : "<end>"
            silentCauses["expected \(expected)   got \(got)", default: 0] += 1
            if silentSamples[expected, default: []].count < 2 {
                silentSamples[expected, default: []].append(snippet.diagnosticID)
            }
        }
        _ = silentSamples
        print("=== silent-mismatch causes (first divergent line), top 20 ===")
        for (cause, n) in silentCauses.sorted(by: { $0.value > $1.value }).prefix(20) {
            print(String(format: "%6d  %@", n, cause))
        }
        print("=== label accounting ===")
        print("  matching:                 \(matching)")
        print("  differing WITH diagnostic: \(differing - differingSilent)")
        print("  differing SILENTLY:        \(differingSilent)   <- invisible in the tally below")

        // Printed every run — this is the Phase 2/3/4 work queue, ordered by size.
        print("=== converter .unhandled tally (\(unhandled.values.reduce(0, +)) total) ===")
        for (key, n) in unhandled.sorted(by: { $0.value > $1.value }) {
            print(String(format: "%6d  %@", n, key))
            for s in samples[key] ?? [] { print("          \(s)") }
        }
        print("=== converter .lookupFailed tally (\(tally.values.reduce(0, +)) total) ===")
        for (key, n) in tally.sorted(by: { $0.value > $1.value }) {
            print(String(format: "%6d  %@", n, key))
        }

        #expect(tally.isEmpty, """
            Converter reported \(tally.values.reduce(0, +)) .lookupFailed fallbacks — each one is a
            rule the converter claims to handle that did not yield its expected child.
            \(failures.joined(separator: "\n"))
            """)
    }
}

@Suite("SwiftSyntax Comparison", .serialized)
struct SwiftSyntaxTests {

    @Suite("SwiftSyntax parser probe")
    struct ParserProbe {

        @Test("swift-syntax accepts `let let x = 1` without parser error")
        func doubleLetProbe() {
            #expect(!Parser.parse(source: "let let x = 1").hasError)
        }

        @Test("pattern node shape differs between declaration and switch case")
        func patternNodeShapeProbe() {
            let tupleDecl = Parser.parse(source: "let (x, y) = (1, 2)")
            let tupleDeclTree = dumpSwiftSyntaxNode(Syntax(tupleDecl), indent: 0).text
            #expect(tupleDeclTree.contains("TuplePattern"))
            #expect(!tupleDeclTree.contains("ValueBindingPattern"))

            let switchCase = Parser.parse(source: """
            switch (1, 2) {
            case let (x, y):
                break
            default:
                break
            }
            """)
            let switchCaseTree = dumpSwiftSyntaxNode(Syntax(switchCase), indent: 0).text
            #expect(switchCaseTree.contains("ValueBindingPattern"))
            #expect(switchCaseTree.contains("ExpressionPattern"))
            #expect(switchCaseTree.contains("PatternExpr"))
        }

        /// The operator-terminal family, pinned against swift-syntax. Each row below was a
        /// LATENT regression at some point — the grammar had no coverage for any of them, so
        /// two separate refactors broke them silently. Asserting swift's verdict alongside
        /// Advent's keeps the pair locked together.
        ///
        /// The arrow is position-dependent: `->` is punctuation in an expression (reachable
        /// only via `ArrowExprSyntax`) but a legal NAME in an operator declaration, and is
        /// rejected in a function name. The generic-`<` peel-off is a separate axis — see
        /// `functionNameOperator` / `@preempt(openAngle)` in Swift.apus.
        @Test("operator terminals: arrow position and generic peel-off match swift")
        func operatorTerminalFamilyProbe() throws {
            // `->` as a DECLARED operator name: legal.
            #expect(!Parser.parse(source: "infix operator ->").hasError)
            #expect(try adventParse("infix operator ->") != nil)

            // `->` as a FUNCTION name: "expected identifier in function".
            #expect(Parser.parse(source: "func ->(a: Int, b: Int) {}").hasError)
            #expect(try adventParse("func ->(a: Int, b: Int) {}") == nil)

            // Non-arrow operator function names stay legal, including `!`/`?`-led ones.
            for name in ["+", "??", "!!"] {
                let source = "func \(name)(a: Int, b: Int) {}"
                #expect(!Parser.parse(source: source).hasError, "swift rejected \(source)")
                #expect(try adventParse(source) != nil, "Advent rejected \(source)")
            }

            // A `.`-led operator declaration: no operatorHead, so it needs `dotOperator`.
            #expect(!Parser.parse(source: "prefix operator ..<").hasError)
            #expect(try adventParse("prefix operator ..<") != nil)

            // Generic clause peeled off an operator function name (testTry1/testInvalid28).
            let generic = "func %%%%<T, U>(x: T, y: U) -> Int { return 0 }"
            #expect(!Parser.parse(source: generic).hasError)
            #expect(try adventParse(generic) != nil)
        }

    }
}

// MARK: - Literal-munch edge probes (TODO items 3/4)

@Suite("SwiftSyntax - Literal munch boundaries")
struct LiteralMunchBoundaryTests {
    static let acceptedSnippets: [String] = [
        "#if !!FOO\nlet x = 1\n#endif",
        "let x = y as!~C",
        "let x = y as?~C",
        "let x = y as? Foo ?? bar",
        "try f()",
        "try?f()",
        "try!f()",
    ]

    static let rejectedSnippets: [String] = [
        "try!-f()",
        "try?-f()",
        "f(a as? A<B>??x)",
    ]

    @Test("munch-exempt marks accept where swift-syntax accepts", arguments: acceptedSnippets)
    func acceptedMunchBoundaries(_ source: String) throws {
        #expect(!Parser.parse(source: source).hasError, "swift-syntax rejected the premise: \(source)")
        let result = try adventParse(source)
        #expect(result != nil, "Advent rejected: \(source)")
        #expect(result?.isUnambiguous == true, "Advent left residual ambiguity: \(source)")
    }

    @Test("literal munch still rejects where swift-syntax rejects", arguments: rejectedSnippets)
    func rejectedMunchBoundaries(_ source: String) throws {
        #expect(Parser.parse(source: source).hasError, "swift-syntax accepted the premise: \(source)")
        #expect(try adventParse(source) == nil, "Advent accepted: \(source)")
    }
}

// MARK: - Multiline string segment probe (TODO 30)

/// Ground truth for `StringLiteralSegmentList` shape. Guessing the segmentation rule from tree
/// dumps produced two contradictory hypotheses, so print what swift-syntax ACTUALLY builds:
/// every segment's exact text, escaped, for the fixtures whose segment COUNT we get wrong.
/// Snippets swift-syntax parses but the compiler rejects are disabled for accept/tree tests.
/// They are classification data until split into syntactic versus semantic compiler rejects.
///
/// Many rows are semantic compiler failures that a syntax grammar should accept.
/// This suite prevents the classification bucket from silently disappearing.
@Suite("SwiftSyntax - Compiler-rejected (swift-syntax disagrees)")
struct CompilerRejectTests {

    static let corpus: [SwiftSnippet] =
        (declarationSnippets + expressionSnippets + statementSnippets + typeSnippets
         + patternSnippets + attributeSnippets + translatedSnippets + allRejectSnippets)
        .filter { $0.compilerRejects != nil }

    @Test("compiler-rejected rows are classified")
    func compilerRejectedRowsAreClassified() {
        #expect(!Self.corpus.isEmpty)
    }
}
