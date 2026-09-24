//
//  Benchmark.swift
//  tinyGLL
//
//  Times the interpreter against the parser it generates, over a sweep of input lengths.
//  This was the CLI's --bench mode, which wrote numbers to stdout for pasting into a
//  spreadsheet; the sweep is unchanged, but it now returns a report for the UI to show and
//  a TSV string for the same paste.
//

import Foundation

/// One benchmark run. Sendable so it can cross back from the background task that produced it.
nonisolated struct BenchmarkReport: Sendable {

    struct Row: Identifiable, Sendable {
        var id: Int { length }
        let length: Int
        let interpreted: Double
        /// nil when the compiled column was skipped — see `Benchmark.run`.
        let compiled: Double?
    }

    let rows: [Row]

    /// Input lengths the interpreter failed to accept. Always empty for a correct parser, so
    /// it is the sweep's correctness canary rather than a result.
    let rejected: [Int]

    var interpretedTotal: Double { rows.reduce(0) { $0 + $1.interpreted } }

    var compiledTotal: Double? {
        let times = rows.compactMap(\.compiled)
        return times.count == rows.count ? times.reduce(0, +) : nil
    }

    var speedup: Double? {
        guard let compiledTotal, compiledTotal > 0 else { return nil }
        return interpretedTotal / compiledTotal
    }

    /// The old stdout format: one tab-separated pair of seconds per input, six decimals,
    /// plain numbers so it pastes straight into a spreadsheet.
    var tsv: String {
        rows.map { row in
            if let compiled = row.compiled {
                return String(format: "%.6f\t%.6f", row.interpreted, compiled)
            }
            return String(format: "%.6f", row.interpreted)
        }
        .joined(separator: "\n")
    }
}

nonisolated enum Benchmark {

    /// The tortureART grammar. Built in rather than taken from the explorer's fields: the
    /// sweep needs a family of inputs, not the single one on screen.
    static let syntax = " S = b | S S | S S S ."

    /// 100 matches the number of ^^^ lines in 'apus grammars/tortureART.apus', so the two
    /// runs are comparable line for line.
    static let defaultMaxLength = 100

    /// Parses "b" * n for n in 1...maxLength, both interpreted and compiled.
    ///
    /// The compiled column comes from generating a standalone parser for the same grammar,
    /// building it with swiftc -O and running the whole sweep in one process (see
    /// `compiledTimings`). Both sides therefore do identical work on identical inputs, which
    /// makes the ratio a measurement of codegen alone. If the toolchain is unavailable the
    /// compiled column is simply omitted.
    ///
    /// Only the descriptor loop is timed on either side. Grammar reading, code generation,
    /// compilation and derivation extraction are all excluded, and the numbers are only
    /// meaningful from a release build — a debug build measures Swift's bounds and retain
    /// checks, not the parser.
    ///
    /// `@concurrent` so the sweep runs on the global executor: it blocks for seconds at a
    /// time, including waiting on swiftc, and must not hold the main actor while it does.
    @concurrent
    static func run(maxLength: Int = defaultMaxLength) async throws -> BenchmarkReport {
        let inputs = (1...maxLength).map { String(repeating: "b", count: $0) }

        /// A parser with the grammar already read, so only parseInput() lands in the timing.
        func prepared(length: Int) throws -> Parser {
            let parser = Parser(syntax: syntax, input: String(repeating: "b", count: length))
            try parser.parseGrammar()
            return parser
        }

        // Discarded warm-up: the first parse in a process pays one-off allocation costs, which
        // would otherwise land entirely on the shortest — and so most sensitive — input.
        for _ in 0..<3 {
            try prepared(length: 5).parseInput()
        }

        var interpreted: [Double] = []
        var rejected: [Int] = []

        for n in 1...maxLength {
            let parser = try prepared(length: n)

            let start = DispatchTime.now().uptimeNanoseconds
            try parser.parseInput()
            let elapsed = DispatchTime.now().uptimeNanoseconds - start

            interpreted.append(Double(elapsed) / 1_000_000_000)

            if !parser.parseAccepted { rejected.append(n) }
        }

        // Generated from a parser loaded at the same length the interpreter warmed up on, so
        // the generated parser's own warm-up — which runs on its baked-in input — matches.
        let compiled = try compiledTimings(from: try prepared(length: 5), for: inputs)

        let rows = interpreted.enumerated().map { index, seconds in
            BenchmarkReport.Row(length: index + 1,
                                interpreted: seconds,
                                compiled: compiled.flatMap { index < $0.count ? $0[index] : nil })
        }

        return BenchmarkReport(rows: rows, rejected: rejected)
    }
}
