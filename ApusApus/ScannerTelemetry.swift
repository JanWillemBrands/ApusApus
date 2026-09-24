//
//  ScannerTelemetry.swift
//  ApusApus
//

import Foundation

protocol ScannerTelemetry: AnyObject {
    func scannerConfigured(literalPatternCount: Int, regexPatternCount: Int)
    func scanStarted(inputSize: Int, literalPatternCount: Int, regexPatternCount: Int)
    func recordLiteralPhase(elapsed: Double)
    func recordRegexPhase(elapsed: Double)
    func recordRegexCall(kind: String, elapsed: Double, charsScanned: Int, inputSize: Int)
    func recordMatchedToken(tokenDescription: String, image: String)
    func recordNonAdvancingMatch(kind: String, image: String, position: String, candidates: [String])
    func recordProgress(charsScanned: Int, inputSize: Int, tokenCount: Int)
    func recordByteLimitStop(_ scanByteLimit: Int)
    func scanFinished(inputSize: Int, tokenCount: Int)
}

final class NoopScannerTelemetry: ScannerTelemetry {
    func scannerConfigured(literalPatternCount: Int, regexPatternCount: Int) {}
    func scanStarted(inputSize: Int, literalPatternCount: Int, regexPatternCount: Int) {}
    func recordLiteralPhase(elapsed: Double) {}
    func recordRegexPhase(elapsed: Double) {}
    func recordRegexCall(kind: String, elapsed: Double, charsScanned: Int, inputSize: Int) {}
    func recordMatchedToken(tokenDescription: String, image: String) {}
    func recordNonAdvancingMatch(kind: String, image: String, position: String, candidates: [String]) {}
    func recordProgress(charsScanned: Int, inputSize: Int, tokenCount: Int) {}
    func recordByteLimitStop(_ scanByteLimit: Int) {}
    func scanFinished(inputSize: Int, tokenCount: Int) {}
}

#if DEBUG
final class DebugScannerTelemetry: ScannerTelemetry {
    private var patternTime: [String: Double] = [:]
    private var patternCalls: [String: Int] = [:]
    private var literalPhaseTime = 0.0
    private var regexPhaseTime = 0.0
    private var scanStart = 0.0

    // Toggle debug scanner reporting here.
    private let telemetryEnabled = false

    private let timingLogURL = URL(fileURLWithPath: "/tmp/scan_timing.log")
    private let eventLogURL = URL(fileURLWithPath: "/tmp/scan_events.log")

    func scannerConfigured(literalPatternCount: Int, regexPatternCount: Int) {
        guard telemetryEnabled else { return }
        print("  scanner: \(literalPatternCount) literal patterns, \(regexPatternCount) regex patterns")
    }

    func scanStarted(inputSize: Int, literalPatternCount: Int, regexPatternCount: Int) {
        guard telemetryEnabled else { return }
        scanStart = CFAbsoluteTimeGetCurrent()
        appendEvent("SCAN START bytes=\(inputSize) literals=\(literalPatternCount) regex=\(regexPatternCount)")
    }

    func recordLiteralPhase(elapsed: Double) {
        guard telemetryEnabled else { return }
        literalPhaseTime += elapsed
    }

    func recordRegexPhase(elapsed: Double) {
        guard telemetryEnabled else { return }
        regexPhaseTime += elapsed
    }

    func recordRegexCall(kind: String, elapsed: Double, charsScanned: Int, inputSize: Int) {
        guard telemetryEnabled else { return }
        patternTime[kind, default: 0] += elapsed
        patternCalls[kind, default: 0] += 1
        if elapsed > 1.0 {
            print("  SLOW REGEX: '\(kind)' took \(String(format: "%.1f", elapsed))s at byte \(charsScanned)/\(inputSize)")
        }
        if elapsed > 0.25 {
            appendEvent("SLOW REGEX kind=\(kind) elapsed=\(String(format: "%.3f", elapsed))s byte=\(charsScanned)/\(inputSize)")
        }
    }

    func recordMatchedToken(tokenDescription: String, image: String) {}

    func recordNonAdvancingMatch(kind: String, image: String, position: String, candidates: [String]) {
        guard telemetryEnabled else { return }
        appendEvent("NON-ADVANCING kind=\(kind) image=\(image.debugDescription) pos=\(position) candidates=\(candidates.joined(separator: ","))")
    }

    func recordProgress(charsScanned: Int, inputSize: Int, tokenCount: Int) {
        guard telemetryEnabled else { return }
        print("  scan: \(charsScanned)/\(inputSize) bytes, \(tokenCount) tokens")
    }

    func recordByteLimitStop(_ scanByteLimit: Int) {
        guard telemetryEnabled else { return }
        print("  scan stopped at byte limit \(scanByteLimit)")
    }

    func scanFinished(inputSize: Int, tokenCount: Int) {
        guard telemetryEnabled else { return }
        let scanElapsed = CFAbsoluteTimeGetCurrent() - scanStart
        let sortedByTime = patternTime.sorted { $0.value > $1.value }
        var report = "  scan complete: \(inputSize) bytes, \(tokenCount) tokens, \(String(format: "%.3f", scanElapsed))s total\n"
        report += "  phase timing: literals \(String(format: "%.3f", literalPhaseTime))s, regex \(String(format: "%.3f", regexPhaseTime))s\n"
        report += "  regex pattern timing (top 10):\n"
        for (kind, time) in sortedByTime.prefix(10) {
            let calls = patternCalls[kind, default: 0]
            let avg = calls > 0 ? time / Double(calls) : 0
            report += "    \(String(format: "%8.3f", time * 1000))ms total, \(String(format: "%6d", calls)) calls, \(String(format: "%.3f", avg * 1000))ms avg — \(kind)\n"
        }
        print(report)
        appendEvent("SCAN END elapsed=\(String(format: "%.3f", scanElapsed))s tokens=\(tokenCount)")
        appendFile(report, url: timingLogURL)
    }

    private func appendEvent(_ text: String) {
        appendFile(text + "\n", url: eventLogURL)
    }

    private func appendFile(_ text: String, url: URL) {
        guard let data = text.data(using: .utf8) else { return }
        if let handle = try? FileHandle(forWritingTo: url) {
            handle.seekToEndOfFile()
            handle.write(data)
            handle.closeFile()
        } else {
            try? data.write(to: url)
        }
    }
}
#endif

func makeDefaultScannerTelemetry() -> any ScannerTelemetry {
    #if DEBUG
    return DebugScannerTelemetry()
    #else
    return NoopScannerTelemetry()
    #endif
}
