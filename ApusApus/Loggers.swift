//
//  Loggers.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.03.29.
//

import Foundation
import OSLog

extension Logger {
    /// Use your bundle ID for the subsystem to ensure unique logs
    /// (not available in macOS console apps)
    private static var subsystem = "com.magenta.apusParser"

    /// Categories help you filter logs in the Xcode console
    static let ui = Logger(subsystem: subsystem, category: "ui")
    static let scan = Logger(subsystem: subsystem, category: "scan")
    static let parse = Logger(subsystem: subsystem, category: "parse")
    static let grammar = Logger(subsystem: subsystem, category: "grammar")
    static let generate = Logger(subsystem: subsystem, category: "generate")
}

// MARK: - Invariant reporting (all build configurations)
//
// `assert` is compiled out under `-O`, and Advent's test scheme ran in Release, so its invariants
// were never checked in the configuration the suites actually used. These replacements run in
// EVERY configuration and never trap: a violation is reported and execution continues along the
// same path the Release build always took. Not trapping matters because one trap kills the whole
// test process, and every remaining test case then reports the same crash.
//
// A violation is reported three ways:
//   * stderr, with the fixed marker `APUS INVARIANT VIOLATED` — for the CLI and the Xcode console,
//     because OSLog is invisible on stdout and redacts interpolations headless (TESTING.md);
//   * OSLog, category `parse`, as an error;
//   * `invariantViolationHandler`, which the test target points at Swift Testing's
//     `Issue.record`, so the test that tripped the invariant goes red. This is the channel test
//     runs rely on: xcodebuild does not forward the test process's stderr to its own output, and
//     `tools/run_tests.sh` counts the recorded issues ("Invariant violated at") from the result
//     bundle.

/// Called on every reported violation. `nil` in the app; set once by the test infrastructure.
nonisolated(unsafe) var invariantViolationHandler: ((_ message: String, _ file: StaticString, _ line: UInt) -> Void)?

private let onceReportedLock = NSLock()
nonisolated(unsafe) private var onceReportedSites = Set<String>()

/// Report a broken invariant. `once: true` is for CONFIGURATION invariants (a property of the
/// grammar, identical on every parse): the first occurrence per process is reported, the rest are
/// suppressed so a single grammar defect does not turn thousands of test cases red.
func reportInvariantViolation(
    _ message: @autoclosure () -> String,
    once: Bool = false,
    file: StaticString = #fileID,
    line: UInt = #line
) {
    if once {
        let site = "\(file):\(line)"
        onceReportedLock.lock()
        let isFirst = onceReportedSites.insert(site).inserted
        onceReportedLock.unlock()
        guard isFirst else { return }
    }
    let text = message()
    let location = "\(file):\(line)"
    FileHandle.standardError.write(Data("APUS INVARIANT VIOLATED at \(location): \(text)\n".utf8))
    Logger.parse.error("invariant violated at \(location, privacy: .public): \(text, privacy: .public)")
    invariantViolationHandler?(text, file, line)
}

/// Replacement for `assert` that is checked in every configuration. The message is only built on
/// failure, so an expensive description costs nothing on the happy path.
func checkInvariant(
    _ condition: @autoclosure () -> Bool,
    _ message: @autoclosure () -> String,
    once: Bool = false,
    file: StaticString = #fileID,
    line: UInt = #line
) {
    if !condition() {
        reportInvariantViolation(message(), once: once, file: file, line: line)
    }
}
