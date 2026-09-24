//
//  OutputTools.swift
//  ApusApus
//
//  Created by Johannes Brands on 25/12/2024.
//

import Foundation

// Trace toggle. Marked `nonisolated(unsafe)` because:
//   - In release builds the trace function is fully gated out by `#if DEBUG`.
//   - In test/debug builds the parser path that mutates trace is serialized by
//     the test infrastructure's `withParserIsolation` lock.
// Direct global access is intentional; the trace plumbing is performance-critical
// and a TaskLocal would force every call site through a closure.
//nonisolated(unsafe) var trace = false
//nonisolated(unsafe) var traceIndent = 0

/// Per-parse console reporting: the `matched/failed/crf size/descriptors` summary
/// `MessageParser.parse` emits on completion, the `no parse found at …` block it
/// emits on failure (plus `explainNoMatch` / `dumpRecentCommits`), and Oracle's
/// `oracle: removed …` line.
///
/// These were written for the single-message CLI in `main.swift`, where one report
/// per run is exactly what you want. They were never gated, so under the test
/// suites they fire on EVERY parse: a full `xcodebuild test` run emitted ~9k such
/// lines — 4.1k summaries, 2.4k oracle lines, 1.3k `no parse found` blocks and
/// their commit dumps — burying the assertion failures that actually matter.
///
/// Default OFF so bulk runs are quiet; `main.swift` turns it on for the CLI.
/// Set `APUS_PARSE_REPORTS=1` to get it back in a test run without editing code
/// (e.g. when debugging one snippet with `-only-testing:`).
///
/// This is the same convention `ScannerTelemetry.telemetryEnabled` already uses.
nonisolated(unsafe) var parseReports =
    ProcessInfo.processInfo.environment["APUS_PARSE_REPORTS"] == "1"

/// `APUS_TRACE_LEX=1` — on a FAILED parse, dump the multi-lexicalisation fan and the parse state at
/// the furthest position reached (`MessageParser.dumpFailureDiagnostics`).
///
/// The slot-local `explainNoMatch` answers "why did THIS terminal fail here?". This answers the
/// position-oriented question a multi-lexicalising parser needs: what can be lexed here at all, how
/// far does each reading reach, and which reading did the parse actually commit to? Built for the
/// source-file campaign (TODO.md item 2), where the failing inputs are far too large to bisect by
/// construction — `ApusToHTML.swift` cost ten wrong construct guesses before this existed.
///
/// Same convention as `parseReports` and `ScannerTelemetry.telemetryEnabled`; costs nothing unset.
nonisolated(unsafe) var traceLex =
    ProcessInfo.processInfo.environment["APUS_TRACE_LEX"] == "1"

//func trace(_ items: Any..., terminator term: String = "") {
//#if DEBUG
//    if trace {
//        for _ in 0..<traceIndent { print(" ", terminator: "")}
//        items.forEach { print("\($0)", terminator: " ") }
//        for item in items { print("\(item)", terminator: " ") }
//        print(term)
//    }
//#endif
//}

/// Called by the trace macro expansion.
/// The closure defers argument evaluation until the trace flag is checked.
/// In release builds the body is empty; @inline(always) ensures the optimizer eliminates everything.
//@inline(always)
//func _traceImpl(_ items: () -> [Any], terminator factor: String = "") {
//#if DEBUG
//    if trace {
//        for _ in 0..<traceIndent { print(" ", terminator: "") }
//        for item in items() { print("\(item)", terminator: " ") }
//        print(factor)
//    }
//#endif
//}
