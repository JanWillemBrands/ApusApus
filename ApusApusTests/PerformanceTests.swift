//
//  PerformanceTests.swift
//  AdventTests
//
//  Lightweight performance harness in Swift Testing.
//  Configure once in `settings` below; no environment variables required.
//

import Testing
import Foundation

@Suite("Performance Tests", .serialized)
struct PerformanceTests {

    // MARK: - Suite Setup

    /// Centralized defaults for performance runs.
    /// Adjust these values in one place when you want broader/deeper runs.
    private struct Settings {
        let grammars: [String]
        let warmupRuns: Int
        let measuredRuns: Int
        let messageLimitPerGrammar: Int
    }

    private static let settings = Settings(
        grammars: ["Swift"],
        warmupRuns: 0,
        measuredRuns: 1,
        messageLimitPerGrammar: 1
    )

    private struct Totals {
        var descriptorCount = 0
        var duplicateDescriptorCount = 0
        var suppressedDescriptorCount = 0
        var crfCount = 0
        var yieldCount = 0

        mutating func add(from parser: MessageParser) {
            descriptorCount += parser.descriptorCount
            duplicateDescriptorCount += parser.duplicateDescriptorCount
            suppressedDescriptorCount += parser.suppressedDescriptorCount
            crfCount += parser.crf.count
            yieldCount += parser.yieldCount
        }
    }

    private static func grammarURL(named name: String) throws -> URL {
        try resolveGrammarFileURL(named: name)
    }

    private static func loadGrammar(named name: String) throws -> Grammar {
        try withParserIsolation {
            let url = try grammarURL(named: name)
            let parser = try ApusParser(fromFile: url)
            return try parser.parse(explicitStartSymbol: "")
        }
    }

    private static func buildInputs(grammar: Grammar, grammarName: String, limit: Int) throws -> [String] {
        let grammarDir = try grammarURL(named: grammarName).deletingLastPathComponent()
        let projectDir = testProjectDirectory()
        var inputs: [String] = []

        for message in grammar.messages {
            if limit > 0 && inputs.count >= limit { break }
            let input: String
            if message.hasPrefix("#") {
                let fileName = message.dropFirst().trimmingCharacters(in: .whitespacesAndNewlines)
                let candidateURLs: [URL] = [
                    grammarDir.appendingPathComponent(fileName),
                    projectDir.appendingPathComponent(fileName)
                ]
                guard let messageFileURL = candidateURLs.first(where: { FileManager.default.fileExists(atPath: $0.path) }) else {
                    throw TestInfrastructureError.grammarFileNotFound(
                        name: "message file \(fileName)",
                        candidates: candidateURLs.map(\.path)
                    )
                }
                input = try String(contentsOf: messageFileURL, encoding: .utf8)
            } else {
                input = String(message)
            }
            inputs.append(input)
        }

        return inputs
    }

    @Test("Performance harness prints stable metrics")
    func benchmarkSelectedGrammars() throws {
        let warmupRuns = max(0, Self.settings.warmupRuns)
        let measuredRuns = max(1, Self.settings.measuredRuns)
        let messageLimit = max(0, Self.settings.messageLimitPerGrammar)
        let grammars = Self.settings.grammars

        print("perf-harness,warmup=\(warmupRuns),runs=\(measuredRuns),grammars=\(grammars.joined(separator: ","))")
        print("grammar,run,wallSeconds,cpuSeconds,messages,descriptorCount,duplicateDescriptorCount,suppressedDescriptorCount,crfCount,yieldCount")

        for grammarName in grammars {
            let grammar = try Self.loadGrammar(named: grammarName)
            let inputs = try Self.buildInputs(grammar: grammar, grammarName: grammarName, limit: messageLimit)

            #expect(!inputs.isEmpty, "No messages found for grammar '\(grammarName)'. Add ^^^ messages or increase messageLimitPerGrammar.")

            let parser = MessageParser(grammar: grammar)

            if warmupRuns > 0 {
                for _ in 0..<warmupRuns {
                    for input in inputs {
                        withParserIsolation {
                            parser.parse(input: input)
                        }
                    }
                }
            }

            var wallSum = 0.0
            var cpuSum = 0.0

            for run in 1...measuredRuns {
                let wallStart = Date().timeIntervalSinceReferenceDate
                let cpuStart = clock()

                var totals = Totals()
                for input in inputs {
                    withParserIsolation {
                        parser.parse(input: input)
                    }
                    totals.add(from: parser)
                }

                let cpuSeconds = Double(clock() - cpuStart) / Double(CLOCKS_PER_SEC)
                let wallSeconds = Date().timeIntervalSinceReferenceDate - wallStart
                wallSum += wallSeconds
                cpuSum += cpuSeconds

                print("\(grammarName),\(run),\(wallSeconds),\(cpuSeconds),\(inputs.count),\(totals.descriptorCount),\(totals.duplicateDescriptorCount),\(totals.suppressedDescriptorCount),\(totals.crfCount),\(totals.yieldCount)")

                #expect(totals.descriptorCount > 0, "Descriptor count should be > 0 for '\(grammarName)'.")
            }

            print("summary,\(grammarName),avgWall=\(wallSum / Double(measuredRuns)),avgCPU=\(cpuSum / Double(measuredRuns))")
        }
    }

    // MARK: - tortureART Growth Curve

    /// Number of discarded warm-up parses before the timed sweep. The first parse in a
    /// process pays one-off allocation costs, which would otherwise land entirely on the
    /// shortest — and so most sensitive — input.
    private static let tortureWarmupRuns = 3

    /// Times every `^^^` message of 'apus grammars/tortureART.apus' separately, so the
    /// output is a growth curve rather than a single total: the grammar is
    /// `S = "b" | S S | S S S .` against "b", "bb", … "b"×100, which is the standard
    /// worst case for a generalised parser (a cubic number of derivations).
    ///
    /// Prints one CSV row per message, length and seconds, six decimals. The
    /// same sweep is available in the tinyGLL target as `tinyGLL --bench`, with the
    /// same lengths and the same warm-up, so the two curves can be compared row by row.
    ///
    /// Only `MessageParser.parse(input:)` is timed — grammar loading and derivation
    /// extraction are outside the measured region. Numbers are only meaningful from a
    /// Release build with coverage off:
    ///
    ///     xcodebuild test -scheme AdventTests -configuration Release \
    ///         -destination 'platform=macOS' -enableCodeCoverage NO \
    ///         '-only-testing:AdventTests/PerformanceTests/tortureARTGrowthCurve()'
    ///
    /// The assertion is that every message still parses; the timings are diagnostic
    /// output, not a pass/fail threshold, since absolute times are machine-dependent.
    @Test("tortureART growth curve, one timing per message")
    func tortureARTGrowthCurve() throws {
        let grammarName = "tortureART"
        let grammar = try Self.loadGrammar(named: grammarName)

        // The ^^^ blocks carry their trailing newline (and the last one the file's blank
        // final line). Trimming keeps the reported length equal to the number of b's.
        let inputs = try Self.buildInputs(grammar: grammar, grammarName: grammarName, limit: 0)
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }

        #expect(!inputs.isEmpty, "No messages found for grammar '\(grammarName)'. Add ^^^ messages.")

        let parser = MessageParser(grammar: grammar)

        for input in inputs.prefix(Self.tortureWarmupRuns) {
            withParserIsolation { parser.parse(input: input) }
        }

        print("torture-growth,grammar=\(grammarName),messages=\(inputs.count),warmup=\(Self.tortureWarmupRuns)")
        print("length,seconds,accepted")

        for input in inputs {
            let start = DispatchTime.now().uptimeNanoseconds
            withParserIsolation { parser.parse(input: input) }
            let elapsed = DispatchTime.now().uptimeNanoseconds - start

            let accepted = parser.yield(of: parser.currentParseRoot).contains {
                $0.i == input.startIndex && $0.j == input.endIndex
            }
            let seconds = String(format: "%.6f", Double(elapsed) / 1_000_000_000)
            print("\(input.count),\(seconds),\(accepted)")

            #expect(accepted, "tortureART rejected an input of \(input.count) b's.")
        }
    }
}
