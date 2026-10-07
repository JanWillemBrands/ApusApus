import Darwin
import Foundation

struct RunnerOptions {
    static let defaultArtifactStatuses: Set<String> = [
        "advent-underaccept",
        "advent-overaccept",
        "residual-ambiguity",
        "advent-no-generated-tree",
        "tree-difference",
        "timeout",
        "crash",
        "invalid-probe-output",
        "probe-error"
    ]

    var iterations = 1_000
    var timeoutSeconds = 10.0
    var seed: UInt64 = 0xA0C2021
    var probePath = "SwiftSyntaxFuzzer/.build/advent-fuzz-probe"
    var grammarPath = "grammars/Swift.apus"
    var outputRoot = "SwiftSyntaxFuzzer/runs"
    var seedCorpusPath = "SwiftSyntaxFuzzer/seeds/known-problems.txt"
    var wideCorpusPaths = ["SwiftSyntaxFuzzer/seeds/swift-syntax-corpus.txt", "SwiftSyntaxFuzzer/seeds/real-source.txt"]
    var widePercent = 50
    var frontierPercent = 20
    var interestingCorpusPaths: [String] = []
    var interestingPercent = 15
    var includePassingEvents = true
    var heartbeatEvery = 25
    var maxArtifacts = 10_000
    var maxArtifactMB = 1_024
    var usePersistentProbe = true
    var artifactStatuses: Set<String>? = RunnerOptions.defaultArtifactStatuses
    var maxArtifactsPerStatus: Int? = nil
    var dedupeBySignal = false
    var reduceArtifactBudget = 0
    var retainInterestingPasses = true
    var maxInterestingPasses = 2_000

    static func parse(_ raw: ArraySlice<String>) throws -> RunnerOptions {
        var options = RunnerOptions()
        var iterator = raw.makeIterator()

        while let arg = iterator.next() {
            switch arg {
            case "--iterations":
                options.iterations = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--timeout":
                options.timeoutSeconds = try parseValue(iterator.next(), as: Double.self, name: arg)
            case "--seed":
                options.seed = try parseSeed(iterator.next(), name: arg)
            case "--probe":
                options.probePath = try parseString(iterator.next(), name: arg)
            case "--grammar":
                options.grammarPath = try parseString(iterator.next(), name: arg)
            case "--output":
                options.outputRoot = try parseString(iterator.next(), name: arg)
            case "--seed-corpus":
                options.seedCorpusPath = try parseString(iterator.next(), name: arg)
            case "--wide-corpus":
                options.wideCorpusPaths = try parseString(iterator.next(), name: arg)
                    .split(separator: ",").map(String.init)
            case "--wide-percent":
                options.widePercent = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--frontier-percent":
                options.frontierPercent = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--interesting-corpus":
                options.interestingCorpusPaths = try parsePathList(iterator.next(), name: arg)
            case "--interesting-percent":
                options.interestingPercent = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--heartbeat-every":
                options.heartbeatEvery = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--max-artifacts":
                options.maxArtifacts = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--max-artifact-mb":
                options.maxArtifactMB = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--artifact-statuses":
                options.artifactStatuses = try parseStatusSet(iterator.next(), name: arg)
            case "--all-artifacts":
                options.artifactStatuses = nil
            case "--max-artifacts-per-status":
                options.maxArtifactsPerStatus = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--dedupe-by-signal":
                options.dedupeBySignal = true
            case "--reduce-artifacts":
                options.reduceArtifactBudget = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--interesting-passes":
                options.retainInterestingPasses = true
            case "--no-interesting-passes":
                options.retainInterestingPasses = false
            case "--max-interesting-passes":
                options.maxInterestingPasses = try parseValue(iterator.next(), as: Int.self, name: arg)
            case "--quiet-passes":
                options.includePassingEvents = false
            case "--persistent-probe":
                options.usePersistentProbe = true
            case "--isolated-probe":
                options.usePersistentProbe = false
            case "--help", "-h":
                printHelp()
                exit(0)
            default:
                throw RunnerError("unknown argument: \(arg)")
            }
        }

        return options
    }

    private static func parseString(_ raw: String?, name: String) throws -> String {
        guard let raw else { throw RunnerError("missing value for \(name)") }
        return raw
    }

    private static func parsePathList(_ raw: String?, name: String) throws -> [String] {
        try parseString(raw, name: name)
            .split(separator: ",")
            .map(String.init)
    }

    private static func parseValue<T: LosslessStringConvertible>(_ raw: String?, as type: T.Type, name: String) throws -> T {
        guard let raw, let value = T(raw) else {
            throw RunnerError("invalid value for \(name)")
        }
        return value
    }

    private static func parseStatusSet(_ raw: String?, name: String) throws -> Set<String> {
        let value = try parseString(raw, name: name)
        let statuses = value
            .split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        guard !statuses.isEmpty else {
            throw RunnerError("empty status list for \(name)")
        }
        return Set(statuses)
    }

    private static func parseSeed(_ raw: String?, name: String) throws -> UInt64 {
        guard let raw else { throw RunnerError("missing value for \(name)") }
        if raw.hasPrefix("0x") || raw.hasPrefix("0X") {
            guard let value = UInt64(raw.dropFirst(2), radix: 16) else {
                throw RunnerError("invalid value for \(name)")
            }
            return value
        }
        guard let value = UInt64(raw) else { throw RunnerError("invalid value for \(name)") }
        return value
    }
}

struct RunnerError: Error, CustomStringConvertible {
    let description: String
    init(_ description: String) { self.description = description }
}

struct ProbeOutput: Codable {
    struct Metrics: Codable {
        let sourceLength: Int
        let tokenCount: Int
        let descriptorCount: Int
        let duplicateDescriptorCount: Int
        let suppressedDescriptorCount: Int
        let crfCount: Int
        let yieldCount: Int
        let oraclePruned: Int
        let parseSeconds: Double
    }

    let status: String
    let swiftSyntaxHasError: Bool
    let adventMatched: Bool
    let adventBuiltTree: Bool
    let adventGeneratedSwiftSyntax: Bool
    let compilerChecked: Bool
    let compilerAccepted: Bool?
    let compilerStderr: String?
    let compilerTypecheckChecked: Bool?
    let compilerTypecheckAccepted: Bool?
    let compilerTypecheckStderr: String?
    let residualAmbiguities: [String]
    let grammarCoverage: [String]?
    let generatorDiagnostics: [String]
    let referenceDump: String?
    let adventDump: String?
    let metrics: Metrics?
    let error: String?
}

struct Event: Codable {
    let index: Int
    let seed: UInt64
    let sourceHash: String
    let sourceLength: Int
    let generator: String
    let status: String
    let exitCode: Int32
    let durationSeconds: Double
    let signalHash: String?
    let signalSummary: String?
    let artifact: String?
    let note: String?
}

/// One line of `telemetry.jsonl`: the source of a status-filtered event, without probe output.
struct TelemetryRecord: Codable {
    let index: Int
    let status: String
    let generator: String
    let signalHash: String?
    let sourceHash: String
    let source: String
}

/// One line of `interesting.jsonl`: a passing source retained because it reached new cheap novelty.
struct InterestingRecord: Codable {
    let index: Int
    let generator: String
    let sourceHash: String
    let novelty: [String]
    let metrics: ProbeOutput.Metrics?
    let grammarCoverage: [String]?
    let source: String
}

struct Artifact: Codable {
    let event: Event
    let source: String
    let originalSource: String?
    let reductionProbes: Int?
    let stdout: String
    let stderr: String
    let probe: ProbeOutput?
}

struct ProcessResult {
    let exitCode: Int32
    let timedOut: Bool
    let durationSeconds: Double
    let stdout: String
    let stderr: String
}

struct ProbeRequest: Codable {
    let source: String
    let includeDumps: Bool?
    var skipCompiler: Bool? = nil
}

struct FailureSignal {
    let hash: String
    let summary: String
}

struct SeedEntry {
    let label: String
    let source: String
}

struct SeedCorpus {
    let entries: [SeedEntry]
    let warnings: [String]

    static func load(from url: URL) -> SeedCorpus {
        guard FileManager.default.fileExists(atPath: url.path) else {
            return SeedCorpus(entries: [], warnings: ["not found; seed-corpus lane disabled"])
        }

        do {
            let text = try String(contentsOf: url, encoding: .utf8)
            var entries: [SeedEntry] = []
            var warnings: [String] = []
            var currentLabel: String?
            var currentLines: [String] = []

            func flush() {
                guard let label = currentLabel else { return }
                let source = currentLines.joined(separator: "\n").trimmedForSeedCorpus()
                if source.isEmpty {
                    warnings.append("empty seed block: \(label)")
                } else {
                    entries.append(SeedEntry(label: label, source: source))
                }
                currentLabel = nil
                currentLines = []
            }

            for line in text.components(separatedBy: .newlines) {
                if line.hasPrefix("### ") {
                    flush()
                    currentLabel = String(line.dropFirst(4)).trimmedForSeedCorpus()
                } else if currentLabel != nil {
                    currentLines.append(line)
                }
            }
            flush()
            return SeedCorpus(entries: entries, warnings: warnings)
        } catch {
            return SeedCorpus(entries: [], warnings: ["failed to read: \(error)"])
        }
    }
}

struct InterestingCorpus {
    private struct Line: Codable {
        let generator: String?
        let sourceHash: String?
        let source: String
    }

    let entries: [SeedEntry]
    let warnings: [String]

    static func load(paths: [String]) -> InterestingCorpus {
        var entries: [SeedEntry] = []
        var warnings: [String] = []
        var seenSources = Set<String>()

        for path in paths {
            let url = URL(fileURLWithPath: path)
            guard FileManager.default.fileExists(atPath: url.path) else {
                warnings.append("\(path): not found")
                continue
            }

            do {
                let text = try String(contentsOf: url, encoding: .utf8)
                for (offset, rawLine) in text.split(separator: "\n", omittingEmptySubsequences: true).enumerated() {
                    guard let data = rawLine.data(using: .utf8) else { continue }
                    do {
                        let decoded = try JSONDecoder().decode(Line.self, from: data)
                        let source = decoded.source.trimmedForSeedCorpus()
                        guard !source.isEmpty, seenSources.insert(source).inserted else { continue }
                        let id = decoded.sourceHash ?? stableHash(source)
                        let label = decoded.generator.map { "\($0):\(id)" } ?? "interesting:\(id)"
                        entries.append(SeedEntry(label: label, source: source))
                    } catch {
                        warnings.append("\(path): line \(offset + 1): \(error)")
                    }
                }
            } catch {
                warnings.append("\(path): failed to read: \(error)")
            }
        }

        return InterestingCorpus(entries: entries, warnings: warnings)
    }
}

struct RunState: Codable {
    let runPath: String
    let seed: UInt64
    let requestedIterations: Int
    let nextIndex: Int
    let completed: Int
    let artifactCount: Int
    let artifactBytes: UInt64
    let stopped: Bool
    let counts: [String: Int]
    let updatedAt: String
}

struct Heartbeat: Codable {
    let runPath: String
    let seed: UInt64
    let requestedIterations: Int
    let completed: Int
    let artifacts: Int
    let artifactBytes: UInt64
    let elapsedSeconds: Double
    let probesPerSecond: Double
    let counts: [String: Int]
    let updatedAt: String
}

final class StopFlag: @unchecked Sendable {
    static let shared = StopFlag()
    private let lock = NSLock()
    private var stopped = false

    func requestStop() {
        lock.lock()
        stopped = true
        lock.unlock()
    }

    var isStopped: Bool {
        lock.lock()
        defer { lock.unlock() }
        return stopped
    }
}

final class LineBuffer: @unchecked Sendable {
    private let condition = NSCondition()
    private var lines: [String] = []
    private var textBuffer = ""
    private var closed = false
    private let handle: FileHandle

    init(handle: FileHandle) {
        self.handle = handle
        handle.readabilityHandler = { [weak self] readableHandle in
            let data = readableHandle.availableData
            if data.isEmpty {
                self?.finish()
            } else {
                self?.append(data)
            }
        }
    }

    func nextLine(timeoutSeconds: Double) -> String? {
        let deadline = Date().addingTimeInterval(timeoutSeconds)
        condition.lock()
        defer { condition.unlock() }
        while lines.isEmpty && !closed {
            let remaining = deadline.timeIntervalSinceNow
            if remaining <= 0 {
                return nil
            }
            condition.wait(until: Date().addingTimeInterval(min(remaining, 0.05)))
        }
        if !lines.isEmpty {
            return lines.removeFirst()
        }
        return nil
    }

    var collectedText: String {
        condition.lock()
        defer { condition.unlock() }
        return (lines + (textBuffer.isEmpty ? [] : [textBuffer])).joined(separator: "\n")
    }

    private func append(_ data: Data) {
        guard let chunk = String(data: data, encoding: .utf8) else { return }
        condition.lock()
        textBuffer += chunk
        while let newline = textBuffer.firstIndex(of: "\n") {
            let line = String(textBuffer[..<newline])
            lines.append(line)
            textBuffer.removeSubrange(...newline)
        }
        condition.broadcast()
        condition.unlock()
    }

    private func finish() {
        handle.readabilityHandler = nil
        condition.lock()
        if !textBuffer.isEmpty {
            lines.append(textBuffer)
            textBuffer = ""
        }
        closed = true
        condition.broadcast()
        condition.unlock()
    }
}

private func probeEnvironment() -> [String: String] {
    var environment = [
        "SWIFT_DETERMINISTIC_HASHING": "1",
        "OS_ACTIVITY_MODE": "disable"
    ]
    if let compilerTimeout = ProcessInfo.processInfo.environment["APUS_COMPILER_TIMEOUT_SECONDS"] {
        environment["APUS_COMPILER_TIMEOUT_SECONDS"] = compilerTimeout
    }
    return environment
}

final class PersistentProbe {
    private let process: Process
    private let stdinHandle: FileHandle
    private let stdoutBuffer: LineBuffer
    private let stderrBuffer: LineBuffer
    private let encoder = JSONEncoder()
    private var stopped = false

    init(probeURL: URL, grammarURL: URL) throws {
        process = Process()
        process.executableURL = probeURL
        process.arguments = ["--grammar", grammarURL.path, "--server"]
        process.environment = probeEnvironment()

        let stdinPipe = Pipe()
        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardInput = stdinPipe
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

        try process.run()
        try? stdinPipe.fileHandleForReading.close()
        try? stdoutPipe.fileHandleForWriting.close()
        try? stderrPipe.fileHandleForWriting.close()

        stdinHandle = stdinPipe.fileHandleForWriting
        stdoutBuffer = LineBuffer(handle: stdoutPipe.fileHandleForReading)
        stderrBuffer = LineBuffer(handle: stderrPipe.fileHandleForReading)
    }

    func run(source: String, timeoutSeconds: Double, skipCompiler: Bool = false) throws -> ProcessResult {
        guard process.isRunning else {
            throw RunnerError("persistent probe is not running")
        }

        let start = Date()
        let request = ProbeRequest(source: source, includeDumps: nil, skipCompiler: skipCompiler ? true : nil)
        var data = try encoder.encode(request)
        data.append(0x0A)
        stdinHandle.write(data)

        guard let line = stdoutBuffer.nextLine(timeoutSeconds: timeoutSeconds) else {
            stop(killProcess: true)
            return ProcessResult(
                exitCode: -1,
                timedOut: true,
                durationSeconds: Date().timeIntervalSince(start),
                stdout: "",
                stderr: stderrBuffer.collectedText
            )
        }

        let decoded = try? JSONDecoder().decode(ProbeOutput.self, from: Data(line.utf8))
        return ProcessResult(
            exitCode: decoded?.status == "same" ? 0 : 1,
            timedOut: false,
            durationSeconds: Date().timeIntervalSince(start),
            stdout: line,
            stderr: stderrBuffer.collectedText
        )
    }

    func stop(killProcess: Bool = false) {
        guard !stopped else { return }
        stopped = true
        try? stdinHandle.close()
        if process.isRunning {
            if killProcess {
                kill(pid_t(process.processIdentifier), SIGKILL)
            } else {
                process.terminate()
            }
            process.waitUntilExit()
        }
    }

    deinit {
        stop()
    }
}

private func requestStopFromSignal(_ signalNumber: Int32) {
    StopFlag.shared.requestStop()
}

@main
struct AdventFuzzRunner {
    static func main() {
        do {
            let options = try RunnerOptions.parse(CommandLine.arguments.dropFirst())
            try run(options)
        } catch {
            fputs("advent-fuzz-runner: \(error)\n", stderr)
            exit(2)
        }
    }

    private static func run(_ options: RunnerOptions) throws {
        installSignalHandlers()

        let fileManager = FileManager.default
        let stamp = ISO8601DateFormatter().string(from: Date()).replacingOccurrences(of: ":", with: "-")
        let runURL = URL(fileURLWithPath: options.outputRoot).appendingPathComponent(stamp, isDirectory: true)
        let artifactURL = runURL.appendingPathComponent("artifacts", isDirectory: true)
        try fileManager.createDirectory(at: artifactURL, withIntermediateDirectories: true)

        let eventsURL = runURL.appendingPathComponent("events.jsonl")
        fileManager.createFile(atPath: eventsURL.path, contents: nil)
        let eventsHandle = try FileHandle(forWritingTo: eventsURL)
        defer { try? eventsHandle.close() }

        // Sources of events whose full artifact the status filter skips (compiler-wins telemetry by
        // default), one compact line per distinct signal, so they can be replayed after grammar
        // changes with `tools/replay_fuzz_sources.py`.
        let telemetryURL = runURL.appendingPathComponent("telemetry.jsonl")
        fileManager.createFile(atPath: telemetryURL.path, contents: nil)
        let telemetryHandle = try FileHandle(forWritingTo: telemetryURL)
        defer { try? telemetryHandle.close() }
        var seenTelemetry = Set<String>()

        let interestingURL = runURL.appendingPathComponent("interesting.jsonl")
        fileManager.createFile(atPath: interestingURL.path, contents: nil)
        let interestingHandle = try FileHandle(forWritingTo: interestingURL)
        defer { try? interestingHandle.close() }
        var noveltyTracker = NoveltyTracker()
        var interestingCount = 0
        var seenReduced = Set<String>()
        var reducedDuplicates = 0

        let probeURL = URL(fileURLWithPath: options.probePath)
        guard fileManager.isExecutableFile(atPath: probeURL.path) else {
            throw RunnerError("probe is not executable: \(probeURL.path). Run SwiftSyntaxFuzzer/bin/build.sh first.")
        }

        let grammarURL = URL(fileURLWithPath: options.grammarPath)
        guard fileManager.fileExists(atPath: grammarURL.path) else {
            throw RunnerError("grammar not found: \(grammarURL.path)")
        }

        let seedCorpusURL = URL(fileURLWithPath: options.seedCorpusPath)
        let seedCorpus = SeedCorpus.load(from: seedCorpusURL)
        var rng = SplitMix64(seed: options.seed)
        let wideCorpus = options.wideCorpusPaths.flatMap { SeedCorpus.load(from: URL(fileURLWithPath: $0)).entries }
        let interestingCorpus = InterestingCorpus.load(paths: options.interestingCorpusPaths)
        var generator = SwiftFragmentGenerator(
            seedCorpus: seedCorpus.entries,
            wideCorpus: wideCorpus,
            widePercent: options.widePercent,
            frontierPercent: options.frontierPercent,
            interestingCorpus: interestingCorpus.entries,
            interestingPercent: options.interestingPercent
        )
        print("wide corpus: \(wideCorpus.count) entries, \(options.widePercent)% of inputs")
        print("frontier lanes: \(options.frontierPercent)% of inputs")
        print("interesting corpus: \(interestingCorpus.entries.count) entries, \(interestingCorpus.entries.isEmpty ? 0 : options.interestingPercent)% of inputs")
        var counts: [String: Int] = [:]
        var seenArtifacts = Set<String>()
        var artifactCount = 0
        var artifactCountsByStatus: [String: Int] = [:]
        var artifactBytes: UInt64 = 0
        let artifactByteLimit = UInt64(max(0, options.maxArtifactMB)) * 1_024 * 1_024
        let runStart = Date()
        let heartbeatURL = runURL.appendingPathComponent("heartbeat.json")
        let stateURL = runURL.appendingPathComponent("state.json")
        let summaryURL = runURL.appendingPathComponent("summary.txt")
        let maxConsecutiveHarnessFailures = 5

        print("run: \(runURL.path)")
        print("seed: \(options.seed)")
        print("iterations: \(options.iterations)")
        print("probe mode: \(options.usePersistentProbe ? "persistent" : "isolated")")
        print("seed corpus: \(seedCorpusURL.path) (\(seedCorpus.entries.count) entries)")
        for warning in seedCorpus.warnings {
            print("seed corpus warning: \(warning)")
        }
        for warning in interestingCorpus.warnings {
            print("interesting corpus warning: \(warning)")
        }
        print("artifact cap: \(options.maxArtifacts) files, \(options.maxArtifactMB) MB")
        if let artifactStatuses = options.artifactStatuses {
            print("artifact statuses: \(artifactStatuses.sorted().joined(separator: ","))")
        } else {
            print("artifact statuses: all")
        }
        if let maxArtifactsPerStatus = options.maxArtifactsPerStatus {
            print("artifact cap per status: \(maxArtifactsPerStatus)")
        }
        if options.dedupeBySignal {
            print("artifact dedupe: signal")
        }
        if options.retainInterestingPasses {
            print("interesting passes: \(interestingURL.path) (cap \(options.maxInterestingPasses))")
        } else {
            print("interesting passes: disabled")
        }

        var completed = 0
        var consecutiveHarnessFailures = 0
        var persistentProbe = options.usePersistentProbe ? try PersistentProbe(probeURL: probeURL, grammarURL: grammarURL) : nil
        var reducerProbe: PersistentProbe? = nil
        defer { persistentProbe?.stop() }
        defer { reducerProbe?.stop() }
        for index in 0..<options.iterations {
            if StopFlag.shared.isStopped {
                print("stop requested; finishing after \(completed) completed inputs")
                break
            }

            let generated = generator.next(using: &rng)
            if sourceRequiresDisabledExperimentalFeature(generated.source) {
                let status = "skipped-experimental"
                counts[status, default: 0] += 1
                completed += 1
                if index == 0 || index % max(1, options.heartbeatEvery) == max(1, options.heartbeatEvery) - 1 {
                    print("[\(index + 1)/\(options.iterations)] \(status) \(generated.label) len=\(generated.source.count) artifacts=\(artifactCount) \(countsLine(counts))")
                    try? writeHeartbeat(
                        to: heartbeatURL,
                        runURL: runURL,
                        seed: options.seed,
                        requestedIterations: options.iterations,
                        completed: completed,
                        artifactCount: artifactCount,
                        artifactBytes: artifactBytes,
                        startedAt: runStart,
                        counts: counts
                    )
                    try? writeState(
                        to: stateURL,
                        runURL: runURL,
                        seed: options.seed,
                        requestedIterations: options.iterations,
                        nextIndex: index + 1,
                        completed: completed,
                        artifactCount: artifactCount,
                        artifactBytes: artifactBytes,
                        stopped: StopFlag.shared.isStopped,
                        counts: counts
                    )
                }
                continue
            }
            let started = Date()
            let result: ProcessResult
            do {
                if options.usePersistentProbe && persistentProbe == nil {
                    persistentProbe = try PersistentProbe(probeURL: probeURL, grammarURL: grammarURL)
                }
                if let persistentProbe {
                    result = try persistentProbe.run(source: generated.source, timeoutSeconds: options.timeoutSeconds)
                } else {
                    result = try runProbe(
                        probeURL: probeURL,
                        grammarURL: grammarURL,
                        source: generated.source,
                        timeoutSeconds: options.timeoutSeconds
                    )
                }
            } catch {
                result = ProcessResult(
                    exitCode: -1,
                    timedOut: false,
                    durationSeconds: Date().timeIntervalSince(started),
                    stdout: "",
                    stderr: "runner failed to execute probe: \(error)"
                )
            }
            if options.usePersistentProbe && result.timedOut {
                persistentProbe?.stop(killProcess: true)
                persistentProbe = nil
            }
            let decoded = try? JSONDecoder().decode(ProbeOutput.self, from: Data(result.stdout.utf8))
            let status: String
            if result.timedOut {
                status = "timeout"
            } else if result.exitCode < 0 {
                status = "crash"
            } else {
                status = decoded?.status ?? "invalid-probe-output"
            }
            counts[status, default: 0] += 1
            let failureSignal = makeFailureSignal(
                status: status,
                probe: decoded,
                result: result,
                generator: generated.label
            )
            if isHarnessFailure(status: status, result: result) {
                consecutiveHarnessFailures += 1
            } else {
                consecutiveHarnessFailures = 0
            }

            let sourceHash = stableHash(generated.source)
            let shouldPersist = status != "same"
            let dedupeID = options.dedupeBySignal ? (failureSignal?.hash ?? sourceHash) : sourceHash
            let dedupeKey = "\(status):\(dedupeID)"
            let isDuplicate = shouldPersist && seenArtifacts.contains(dedupeKey)
            let overArtifactCount = artifactCount >= options.maxArtifacts
            let overArtifactBytes = artifactByteLimit > 0 && artifactBytes >= artifactByteLimit
            let statusAllowed = options.artifactStatuses?.contains(status) ?? true
            let overArtifactStatus = options.maxArtifactsPerStatus.map { artifactCountsByStatus[status, default: 0] >= $0 } ?? false
            let canWriteArtifact = shouldPersist && statusAllowed && !isDuplicate && !overArtifactCount && !overArtifactBytes && !overArtifactStatus
            let artifactName = canWriteArtifact ? "\(String(format: "%08d", index))-\(status)-\(sourceHash).json" : nil
            let note: String?
            if shouldPersist && !statusAllowed {
                note = "artifact-status-filter"
            } else if isDuplicate {
                note = "duplicate-artifact"
            } else if shouldPersist && overArtifactCount {
                note = "artifact-count-cap"
            } else if shouldPersist && overArtifactBytes {
                note = "artifact-byte-cap"
            } else if shouldPersist && overArtifactStatus {
                note = "artifact-status-cap"
            } else {
                note = nil
            }
            let event = Event(
                index: index,
                seed: options.seed,
                sourceHash: sourceHash,
                sourceLength: generated.source.count,
                generator: generated.label,
                status: status,
                exitCode: result.exitCode,
                durationSeconds: Date().timeIntervalSince(started),
                signalHash: failureSignal?.hash,
                signalSummary: failureSignal?.summary,
                artifact: artifactName,
                note: note
            )

            if options.includePassingEvents || shouldPersist {
                try? appendJSONLine(event, to: eventsHandle)
            }

            if note == "artifact-status-filter" {
                let telemetryKey = "\(status):\(failureSignal?.hash ?? sourceHash)"
                if seenTelemetry.insert(telemetryKey).inserted {
                    try? appendJSONLine(TelemetryRecord(
                        index: index,
                        status: status,
                        generator: generated.label,
                        signalHash: failureSignal?.hash,
                        sourceHash: sourceHash,
                        source: generated.source
                    ), to: telemetryHandle)
                }
            }

            if options.retainInterestingPasses,
               status == "same",
               interestingCount < options.maxInterestingPasses {
                let novelty = noveltyTracker.record(
                    generator: generated.label,
                    metrics: decoded?.metrics,
                    grammarCoverage: decoded?.grammarCoverage
                )
                if !novelty.isEmpty {
                    try? appendJSONLine(InterestingRecord(
                        index: index,
                        generator: generated.label,
                        sourceHash: sourceHash,
                        novelty: novelty,
                        metrics: decoded?.metrics,
                        grammarCoverage: decoded?.grammarCoverage,
                        source: generated.source
                    ), to: interestingHandle)
                    interestingCount += 1
                }
            }

            if let artifactName {
                var artifactSource = generated.source
                var artifactResult = result
                var artifactProbe = decoded
                var originalSource: String? = nil
                var reductionProbes: Int? = nil
                var skipArtifactWrite = false
                if options.reduceArtifactBudget > 0,
                   let decoded,
                   FailureReducer.reducibleStatuses.contains(status) {
                    let targetKey = FailureReducer.key(decoded)
                    let reducer = FailureReducer(probe: { candidate in
                        do {
                            if reducerProbe == nil {
                                reducerProbe = try PersistentProbe(probeURL: probeURL, grammarURL: grammarURL)
                            }
                            guard let activeReducerProbe = reducerProbe else { return nil }
                            let reducedResult = try activeReducerProbe.run(
                                source: candidate,
                                timeoutSeconds: options.timeoutSeconds
                            )
                            if reducedResult.timedOut {
                                activeReducerProbe.stop(killProcess: true)
                                reducerProbe = nil
                                return nil
                            }
                            return try? JSONDecoder().decode(ProbeOutput.self, from: Data(reducedResult.stdout.utf8))
                        } catch {
                            reducerProbe?.stop(killProcess: true)
                            reducerProbe = nil
                            return nil
                        }
                    }, budget: options.reduceArtifactBudget)
                    let reduced = reducer.reduce(generated.source, key: targetKey)
                    if reduced.source != generated.source {
                        do {
                            if reducerProbe == nil {
                                reducerProbe = try PersistentProbe(probeURL: probeURL, grammarURL: grammarURL)
                            }
                            if let reducerProbe {
                                let finalResult = try reducerProbe.run(
                                    source: reduced.source,
                                    timeoutSeconds: options.timeoutSeconds
                                )
                                if let finalProbe = try? JSONDecoder().decode(ProbeOutput.self, from: Data(finalResult.stdout.utf8)),
                                   FailureReducer.key(finalProbe) == targetKey {
                                    artifactSource = reduced.source
                                    artifactResult = finalResult
                                    artifactProbe = finalProbe
                                    originalSource = generated.source
                                    reductionProbes = reduced.probes + 1
                                }
                            }
                        } catch {
                            reducerProbe?.stop(killProcess: true)
                            reducerProbe = nil
                        }
                    } else if reduced.probes > 0 {
                        reductionProbes = reduced.probes
                    }
                }
                // Many signals shrink to the SAME minimal source (wrapper and prelude variants of one
                // bug). Only the first reduced form of each is written.
                let reducedKey = "\(status):\(stableHash(artifactSource))"
                if originalSource != nil, !seenReduced.insert(reducedKey).inserted {
                    seenArtifacts.insert(dedupeKey)
                    reducedDuplicates += 1
                    skipArtifactWrite = true
                }
                if !skipArtifactWrite {
                    let artifact = Artifact(
                        event: event,
                        source: artifactSource,
                        originalSource: originalSource,
                        reductionProbes: reductionProbes,
                        stdout: artifactResult.stdout,
                        stderr: artifactResult.stderr,
                        probe: artifactProbe
                    )
                    let data = try prettyJSON(artifact)
                    let targetURL = artifactURL.appendingPathComponent(artifactName)
                    if (try? data.write(to: targetURL, options: .atomic)) != nil {
                        seenArtifacts.insert(dedupeKey)
                        artifactCount += 1
                        artifactCountsByStatus[status, default: 0] += 1
                        artifactBytes += UInt64(data.count)
                    }
                }
            }

            completed += 1
            if index == 0 || index % max(1, options.heartbeatEvery) == max(1, options.heartbeatEvery) - 1 || shouldPersist {
                print("[\(index + 1)/\(options.iterations)] \(status) \(generated.label) len=\(generated.source.count) artifacts=\(artifactCount) \(countsLine(counts))")
            }

            if index == 0 || index % max(1, options.heartbeatEvery) == max(1, options.heartbeatEvery) - 1 || shouldPersist {
                try? writeHeartbeat(
                    to: heartbeatURL,
                    runURL: runURL,
                    seed: options.seed,
                    requestedIterations: options.iterations,
                    completed: completed,
                    artifactCount: artifactCount,
                    artifactBytes: artifactBytes,
                    startedAt: runStart,
                    counts: counts
                )
                try? writeState(
                    to: stateURL,
                    runURL: runURL,
                    seed: options.seed,
                    requestedIterations: options.iterations,
                    nextIndex: index + 1,
                    completed: completed,
                    artifactCount: artifactCount,
                    artifactBytes: artifactBytes,
                    stopped: StopFlag.shared.isStopped,
                    counts: counts
                )
            }

            if consecutiveHarnessFailures >= maxConsecutiveHarnessFailures {
                print("harness failure threshold reached after \(consecutiveHarnessFailures) consecutive failures; stopping after \(completed) completed inputs")
                StopFlag.shared.requestStop()
            }
        }

        var summaryLines = counts
            .sorted { $0.key < $1.key }
            .map { "\($0.key): \($0.value)" }
        summaryLines.append("interesting-passes: \(interestingCount)")
        summaryLines.append("reduced-duplicates: \(reducedDuplicates)")
        let summary = summaryLines.joined(separator: "\n")
        try? summary.write(to: summaryURL, atomically: true, encoding: .utf8)
        try? writeHeartbeat(
            to: heartbeatURL,
            runURL: runURL,
            seed: options.seed,
            requestedIterations: options.iterations,
            completed: completed,
            artifactCount: artifactCount,
            artifactBytes: artifactBytes,
            startedAt: runStart,
            counts: counts
        )
        try? writeState(
            to: stateURL,
            runURL: runURL,
            seed: options.seed,
            requestedIterations: options.iterations,
            nextIndex: completed,
            completed: completed,
            artifactCount: artifactCount,
            artifactBytes: artifactBytes,
            stopped: StopFlag.shared.isStopped,
            counts: counts
        )
        print(summary)
    }

    private static func installSignalHandlers() {
        signal(SIGINT, requestStopFromSignal)
        signal(SIGTERM, requestStopFromSignal)
        signal(SIGPIPE, SIG_IGN)
    }

    private static func writeHeartbeat(
        to url: URL,
        runURL: URL,
        seed: UInt64,
        requestedIterations: Int,
        completed: Int,
        artifactCount: Int,
        artifactBytes: UInt64,
        startedAt: Date,
        counts: [String: Int]
    ) throws {
        let elapsed = max(Date().timeIntervalSince(startedAt), 0.001)
        let heartbeat = Heartbeat(
            runPath: runURL.path,
            seed: seed,
            requestedIterations: requestedIterations,
            completed: completed,
            artifacts: artifactCount,
            artifactBytes: artifactBytes,
            elapsedSeconds: elapsed,
            probesPerSecond: Double(completed) / elapsed,
            counts: counts,
            updatedAt: ISO8601DateFormatter().string(from: Date())
        )
        try prettyJSON(heartbeat).write(to: url, options: .atomic)
    }

    private static func writeState(
        to url: URL,
        runURL: URL,
        seed: UInt64,
        requestedIterations: Int,
        nextIndex: Int,
        completed: Int,
        artifactCount: Int,
        artifactBytes: UInt64,
        stopped: Bool,
        counts: [String: Int]
    ) throws {
        let state = RunState(
            runPath: runURL.path,
            seed: seed,
            requestedIterations: requestedIterations,
            nextIndex: nextIndex,
            completed: completed,
            artifactCount: artifactCount,
            artifactBytes: artifactBytes,
            stopped: stopped,
            counts: counts,
            updatedAt: ISO8601DateFormatter().string(from: Date())
        )
        try prettyJSON(state).write(to: url, options: .atomic)
    }

    private static func runProbe(probeURL: URL, grammarURL: URL, source: String, timeoutSeconds: Double) throws -> ProcessResult {
        try autoreleasepool {
            let process = Process()
            process.executableURL = probeURL
            process.arguments = ["--grammar", grammarURL.path]
            process.environment = probeEnvironment()

            let stdinPipe = Pipe()
            let stdoutPipe = Pipe()
            let stderrPipe = Pipe()
            let pipeHandles = [
                stdinPipe.fileHandleForReading,
                stdinPipe.fileHandleForWriting,
                stdoutPipe.fileHandleForReading,
                stdoutPipe.fileHandleForWriting,
                stderrPipe.fileHandleForReading,
                stderrPipe.fileHandleForWriting
            ]
            defer {
                for handle in pipeHandles {
                    try? handle.close()
                }
            }

            process.standardInput = stdinPipe
            process.standardOutput = stdoutPipe
            process.standardError = stderrPipe

            let start = Date()
            try process.run()

            // These are only needed by the child process. Closing the parent-side
            // copies prevents thousands of short probes from exhausting fds.
            try? stdinPipe.fileHandleForReading.close()
            try? stdoutPipe.fileHandleForWriting.close()
            try? stderrPipe.fileHandleForWriting.close()

            stdinPipe.fileHandleForWriting.write(Data(source.utf8))
            try? stdinPipe.fileHandleForWriting.close()

            let deadline = start.addingTimeInterval(timeoutSeconds)
            var timedOut = false
            while process.isRunning {
                if Date() >= deadline {
                    timedOut = true
                    kill(pid_t(process.processIdentifier), SIGKILL)
                    break
                }
                Thread.sleep(forTimeInterval: 0.02)
            }
            process.waitUntilExit()

            let stdoutData = stdoutPipe.fileHandleForReading.readDataToEndOfFile()
            let stderrData = stderrPipe.fileHandleForReading.readDataToEndOfFile()
            try? stdoutPipe.fileHandleForReading.close()
            try? stderrPipe.fileHandleForReading.close()

            let stdout = String(data: stdoutData, encoding: .utf8) ?? ""
            let stderr = String(data: stderrData, encoding: .utf8) ?? ""
            return ProcessResult(
                exitCode: process.terminationStatus,
                timedOut: timedOut,
                durationSeconds: Date().timeIntervalSince(start),
                stdout: stdout,
                stderr: stderr
            )
        }
    }
}

func isHarnessFailure(status: String, result: ProcessResult) -> Bool {
    if result.stderr.contains("runner failed to execute probe") {
        return true
    }
    if status == "invalid-probe-output", result.stdout.isEmpty, result.stderr.isEmpty {
        return true
    }
    return false
}

struct NoveltyTracker {
    private var seen = Set<String>()

    mutating func record(generator: String, metrics: ProbeOutput.Metrics?, grammarCoverage: [String]?) -> [String] {
        var novelty: [String] = []

        insert("generator:\(generator)", into: &novelty)
        for fingerprint in grammarCoverage ?? [] {
            insert("coverage:\(fingerprint)", into: &novelty)
        }
        guard let metrics else { return novelty }

        insertBucket("sourceLength", metrics.sourceLength, into: &novelty)
        insertBucket("tokenCount", metrics.tokenCount, into: &novelty)
        insertBucket("descriptorCount", metrics.descriptorCount, into: &novelty)
        insertBucket("duplicateDescriptorCount", metrics.duplicateDescriptorCount, into: &novelty)
        insertBucket("suppressedDescriptorCount", metrics.suppressedDescriptorCount, into: &novelty)
        insertBucket("crfCount", metrics.crfCount, into: &novelty)
        insertBucket("yieldCount", metrics.yieldCount, into: &novelty)
        insertBucket("oraclePruned", metrics.oraclePruned, into: &novelty)
        insertBucket("parseMillis", Int((metrics.parseSeconds * 1000.0).rounded(.up)), into: &novelty)

        return novelty
    }

    private mutating func insertBucket(_ name: String, _ value: Int, into novelty: inout [String]) {
        insert("\(name):\(bucket(value))", into: &novelty)
    }

    private mutating func insert(_ key: String, into novelty: inout [String]) {
        if seen.insert(key).inserted {
            novelty.append(key)
        }
    }

    private func bucket(_ value: Int) -> String {
        if value <= 0 { return "0" }
        var upper = 1
        while upper < value && upper < Int.max / 2 {
            upper *= 2
        }
        return "\(upper / 2 + 1)-\(upper)"
    }
}

struct GeneratedSource {
    let label: String
    let source: String
}

struct SwiftFragmentGenerator {
    private let seedCorpus: [SeedEntry]

    private let wideCorpus: [SeedEntry]
    private let widePercent: Int
    private let frontierPercent: Int
    private let tokenMutator: TokenMutator
    private let interestingCorpus: [SeedEntry]
    private let interestingPercent: Int

    init(
        seedCorpus: [SeedEntry] = [],
        wideCorpus: [SeedEntry] = [],
        widePercent: Int = 0,
        frontierPercent: Int = 0,
        interestingCorpus: [SeedEntry] = [],
        interestingPercent: Int = 0
    ) {
        self.seedCorpus = seedCorpus
        self.wideCorpus = wideCorpus
        self.widePercent = wideCorpus.isEmpty ? 0 : widePercent
        self.frontierPercent = max(0, frontierPercent)
        self.tokenMutator = TokenMutator(corpus: wideCorpus)
        self.interestingCorpus = interestingCorpus
        self.interestingPercent = interestingCorpus.isEmpty ? 0 : interestingPercent
    }

    /// Wide lane: a real-code seed (sometimes two), mutated at 1–3 token boundaries (80%), in one
    /// of `fuzzContexts`.
    private func wideSource(using rng: inout SplitMix64) -> GeneratedSource {
        let entry = wideCorpus.random(using: &rng)
        var source = entry.source
        var label = entry.label
        if rng.nextInt(upperBound: 5) == 0 {
            let second = wideCorpus.random(using: &rng)
            source += "\n" + second.source
            label += "+" + second.label
        }
        var edits = "raw"
        if rng.nextInt(upperBound: 5) != 0 {
            (source, edits) = tokenMutator.mutate(source, using: &rng)
        }
        let context = fuzzContexts.random(using: &rng)
        return GeneratedSource(label: "wide:\(context.name):\(edits):\(label)", source: context.wrap(source))
    }

    private let identifiers = [
        "a", "b", "c", "x", "y", "value", "parser", "result", "items", "Element",
        "operator", "default", "async", "await", "inout", "import", "repeat", "some",
        "any", "borrowing", "consuming", "isolated"
    ]
    private let types = [
        "Int", "String", "Bool", "T", "Self", "[Int]", "[String: Int]", "(Int, String)",
        "Array<Array<Foo>>", "some P", "any P", "Foo.Bar", "Foo.Bar?", "UInt8!", "~Copyable",
        "(any P)?", "(some P).Type", "borrowing T", "consuming T", "isolated any Actor",
        "sending T", "repeat each T", "(repeat each T)", "Foo<Bar<Baz>>.Type",
        "@escaping @Sendable () async throws -> Int", "Dictionary<String, [Foo.Bar?]>"
    ]
    private let expressions = [
        "a ? b : c ? d : e",
        "A as? B + C -> D is E as! F ? G = 42 : H",
        "Swift.Array<Array<Foo>>()",
        "children.filter(\\.type.defaultInitialization.isEmpty)",
        "\\.type.defaultInitialization?.name",
        "\\Foo.Bar.default",
        "x?.foo!.bar",
        "f { $0 } g: { 2 }",
        "f(a: value, default: result)",
        "/abc/.wholeMatch(in: s)",
        "#/abc/#.wholeMatch(in: s)",
        "\"\\(value) /abc/ \\(try? f())\"",
        "try f()",
        "try(f())",
        "try[0]",
        "try.f()",
        "try! f()",
        "try? f()",
        "try!-f()",
        "try?-f()",
        "x as!~C",
        "x as?~C",
        "x as? Foo ?? bar",
        "f(a as? A<B>??x)",
        "a < b > (c)",
        "Foo<Bar<Baz>>.self",
        "consume value",
        "copy value",
        "value as? (any P)? ?? fallback",
        "value[keyPath: \\.foo!.bar]",
        "items.map { $0 }.filter { _ in true }",
        "f { value }\n.member",
        "#selector(Foo.bar)",
        "#keyPath(Foo.bar)",
        "#Predicate<Foo> { $0.bar == 1 }",
        "a..<b as Range<Int>",
        "a...b ? c : d"
    ]
    private let statements = [
        "let x = 1",
        "let y: Int? = nil",
        "if let x = x { return x }",
        "if let (a, b) = pair { _ = a; _ = b }",
        "guard case .some(let x) = value else { return }",
        "for var item in items { _ = item }",
        "for (a, var b, c) in triples { _ = a; _ = b; _ = c }",
        "var (b, var c) = pair",
        "switch value { case .import(_, let s): break default: break }",
        "defer { _ = value }",
        "do throws(FuzzError) { throw FuzzError.value } catch { return }",
        "if let x = value as? T, case _? = Optional(x) { _ = x }",
        "repeat { break } while value != nil",
        "for await item in stream { _ = item }",
        "#if compiler(>=6.0)\nlet x = value\n#else\nlet x = value\n#endif"
    ]
    private let attributes = [
        "@objc", "@MainActor", "@discardableResult", "@available(*, deprecated)", "@_spi(Private)",
        "@preconcurrency", "@backDeployed(before: macOS 14)", "@_documentation(visibility: private)",
        "@attached(member)", "@freestanding(expression)"
    ]
    private let castOperators = ["as", "as?", "as!", "is"]
    private let postfixTails = ["(f())", "[0]", ".f()", "?.f()", "!.f()", ".default", ".inout"]
    private let operatorContinuations = ["-f()", "~C", "& value", "?? fallback", "?.member", "!.member"]
    private let regexBodies = ["abc", "a b", "a  b", "a\\ b", "x*/", "[a-z]+", "(?<name>a)"]
    private let callLabels = ["default", "operator", "repeat", "async", "await", "inout"]

    mutating func next(using rng: inout SplitMix64) -> GeneratedSource {
        if interestingPercent > 0, rng.nextInt(upperBound: 100) < interestingPercent {
            return interestingCorpusSource(using: &rng)
        }
        if frontierPercent > 0, rng.nextInt(upperBound: 100) < frontierPercent {
            return recentFrontierSource(using: &rng)
        }
        if widePercent > 0, rng.nextInt(upperBound: 100) < widePercent {
            return wideSource(using: &rng)
        }
        let curatedLaneCount = 60
        let choice = rng.nextInt(upperBound: seedCorpus.isEmpty ? curatedLaneCount : curatedLaneCount + 4)
        switch choice {
        case 0:
            let expr = mutate(expressions.random(using: &rng), using: &rng)
            return GeneratedSource(label: "expr-let", source: "let fuzzValue = \(expr)")
        case 1:
            let type = mutate(types.random(using: &rng), using: &rng)
            return GeneratedSource(label: "type-let", source: "let fuzzValue: \(type) = placeholder()")
        case 2:
            let stmt = mutate(statements.random(using: &rng), using: &rng)
            return GeneratedSource(label: "func-body", source: functionBody(stmt))
        case 3:
            let attr = attributes.random(using: &rng)
            return GeneratedSource(label: "attribute-decl", source: "\(attr) func fuzz<T: P>(x: T) async throws -> T { x }")
        case 4:
            return GeneratedSource(label: "operator-boundary", source: operatorBoundary(using: &rng))
        case 5:
            let expr = expressions.random(using: &rng)
            return GeneratedSource(label: "closure-call", source: "let fuzzValue = f(\(expr)) { value in\nvalue\n}")
        case 6:
            let type = types.random(using: &rng)
            return GeneratedSource(label: "generic-decl", source: "struct Fuzz<T: \(type)> { var value: T }")
        case 7:
            return GeneratedSource(label: "pattern-switch", source: "switch value {\ncase (.declarationModifier(.open), _)?: break\ncase .import(_, let s): break\ndefault: break\n}")
        case 8:
            let expr = mutate(expressions.random(using: &rng), using: &rng)
            return GeneratedSource(label: "nested-template", source: "struct Fuzz<T> {\nfunc run(_ x: T) {\nlet value = \(expr)\n_ = value\n}\n}")
        case 9:
            return GeneratedSource(label: "try-boundary", source: "let fuzzValue = \(tryBoundary(using: &rng))")
        case 10:
            return GeneratedSource(label: "cast-boundary", source: "let fuzzValue = \(castBoundary(using: &rng))")
        case 11:
            return GeneratedSource(label: "regex-boundary", source: regexBoundary(using: &rng))
        case 12:
            return GeneratedSource(label: "ifconfig-boundary", source: ifConfigBoundary(using: &rng))
        case 13:
            return GeneratedSource(label: "member-keyword", source: memberKeyword(using: &rng))
        case 14:
            return GeneratedSource(label: "binding-pattern", source: functionBody(bindingPattern(using: &rng)))
        case 15:
            return GeneratedSource(label: "extension-type", source: extensionType(using: &rng))
        case 16:
            return GeneratedSource(label: "generic-where", source: genericWhere(using: &rng))
        case 17:
            return GeneratedSource(label: "keypath-boundary", source: "let fuzzValue = \(keyPathBoundary(using: &rng))")
        case 18:
            return GeneratedSource(label: "interpolation-boundary", source: interpolationBoundary(using: &rng))
        case 19:
            return GeneratedSource(label: "closure-label", source: closureLabel(using: &rng))
        case 20:
            return GeneratedSource(label: "trailing-closure-boundary", source: trailingClosureBoundary(using: &rng))
        case 21:
            return GeneratedSource(label: "condition-boundary", source: functionBody(conditionBoundary(using: &rng)))
        case 22:
            return GeneratedSource(label: "attribute-boundary", source: attributeBoundary(using: &rng))
        case 23:
            return GeneratedSource(label: "pack-boundary", source: packBoundary(using: &rng))
        case 24:
            return GeneratedSource(label: "delimiter-recovery-boundary", source: delimiterRecoveryBoundary(using: &rng))
        case 25:
            return GeneratedSource(label: "accessor-effect-boundary", source: accessorEffectBoundary(using: &rng))
        case 26:
            return GeneratedSource(label: "ownership-modifier-boundary", source: ownershipModifierBoundary(using: &rng))
        case 27:
            return GeneratedSource(label: "macro-pound-boundary", source: macroPoundBoundary(using: &rng))
        case 28:
            return GeneratedSource(label: "collection-type-boundary", source: collectionTypeBoundary(using: &rng))
        case 29:
            return GeneratedSource(label: "declaration-modifier-stack", source: declarationModifierStack(using: &rng))
        case 30:
            return GeneratedSource(label: "enum-case-pattern-boundary", source: enumCasePatternBoundary(using: &rng))
        case 31:
            return GeneratedSource(label: "subscript-call-boundary", source: subscriptCallBoundary(using: &rng))
        case 32:
            return GeneratedSource(label: "effectful-function-type", source: effectfulFunctionType(using: &rng))
        case 33:
            let pieces = (0..<max(1, rng.nextInt(upperBound: 6) + 1)).map { _ in statements.random(using: &rng) }
            return GeneratedSource(label: "statement-list", source: functionBody(pieces.joined(separator: "\n")))
        case 34:
            return GeneratedSource(label: "member-list-boundary", source: memberListBoundary(using: &rng))
        case 35:
            return GeneratedSource(label: "protocol-requirement-boundary", source: protocolRequirementBoundary(using: &rng))
        case 36:
            return GeneratedSource(label: "operator-decl-boundary", source: operatorDeclBoundary(using: &rng))
        case 37:
            return GeneratedSource(label: "init-subscript-boundary", source: initSubscriptBoundary(using: &rng))
        case 38:
            return GeneratedSource(label: "nested-ifconfig-boundary", source: nestedIfConfigBoundary(using: &rng))
        case 39:
            return GeneratedSource(label: "regex-trivia-boundary", source: regexTriviaBoundary(using: &rng))
        case 40:
            return GeneratedSource(label: "cast-try-operator-cluster", source: castTryOperatorCluster(using: &rng))
        case 41:
            return GeneratedSource(label: "pattern-matrix-boundary", source: functionBody(patternMatrixBoundary(using: &rng)))
        case 42:
            return GeneratedSource(label: "ifconfig-member-context-boundary", source: ifConfigMemberContextBoundary(using: &rng))
        case 43:
            return GeneratedSource(label: "keypath-component-matrix", source: "let fuzzValue = \(keyPathComponentMatrix(using: &rng))")
        case 44:
            return GeneratedSource(label: "regex-slash-operator-boundary", source: regexSlashOperatorBoundary(using: &rng))
        case 45:
            return GeneratedSource(label: "member-list-wide-boundary", source: memberListWideBoundary(using: &rng))
        case 46:
            return GeneratedSource(label: "type-composition-boundary", source: typeCompositionBoundary(using: &rng))
        case 47:
            return GeneratedSource(label: "contextual-keyword-boundary", source: contextualKeywordBoundary(using: &rng))
        case 48:
            return GeneratedSource(label: "import-attribute-boundary", source: importAttributeBoundary(using: &rng))
        case 49:
            return GeneratedSource(label: "closure-result-boundary", source: closureResultBoundary(using: &rng))
        case 50:
            return GeneratedSource(label: "statement-control-boundary", source: functionBody(statementControlBoundary(using: &rng)))
        case 51:
            return GeneratedSource(label: "macro-attribute-directive-boundary", source: macroAttributeDirectiveBoundary(using: &rng))
        case 52:
            return GeneratedSource(label: "attribute-ifconfig-elseif-list", source: attributeIfConfigElseifList(using: &rng))
        case 53:
            return GeneratedSource(label: "multiline-interpolation-boundary", source: multilineInterpolationBoundary(using: &rng))
        case 54:
            return GeneratedSource(label: "grammarish-member-list", source: grammarishMemberList(using: &rng))
        case 55:
            return GeneratedSource(label: "tspl-divergence-specialized-attribute", source: tsplDivergenceSpecializedAttribute(using: &rng))
        case 56:
            return GeneratedSource(label: "tspl-divergence-protocol-body", source: tsplDivergenceProtocolBody(using: &rng))
        case 57:
            return GeneratedSource(label: "tspl-divergence-accessor-commitment", source: tsplDivergenceAccessorCommitment(using: &rng))
        case 58:
            return GeneratedSource(label: "tspl-divergence-type-shape", source: tsplDivergenceTypeShape(using: &rng))
        case 59:
            return GeneratedSource(label: "tspl-divergence-pattern-shape", source: tsplDivergencePatternShape(using: &rng))
        case 60:
            return seedCorpusSource(using: &rng, mutated: false)
        case 61:
            return seedCorpusSource(using: &rng, mutated: true)
        case 62:
            return wrappedSeedCorpusSource(using: &rng)
        case 63:
            return structuralSeedSplice(using: &rng)
        default:
            return seedCorpusCrossover(using: &rng)
        }
    }

    private func recentFrontierSource(using rng: inout SplitMix64) -> GeneratedSource {
        switch rng.nextInt(upperBound: 6) {
        case 0:
            return GeneratedSource(label: "frontier:interpolation-delimiter", source: interpolationDelimiterFrontier(using: &rng))
        case 1:
            return GeneratedSource(label: "frontier:condition-trailing-closure-scope", source: functionBody(conditionTrailingClosureFrontier(using: &rng)))
        case 2:
            return GeneratedSource(label: "frontier:parser-mode-scope", source: parserModeScopeFrontier(using: &rng))
        case 3:
            return GeneratedSource(label: "frontier:statement-member-context", source: statementMemberContextFrontier(using: &rng))
        case 4:
            return GeneratedSource(label: "frontier:generic-member-type-shape", source: genericMemberTypeFrontier(using: &rng))
        default:
            return GeneratedSource(label: "frontier:protocol-accessor-shape", source: protocolAccessorFrontier(using: &rng))
        }
    }

    private func functionBody(_ body: String) -> String {
        """
        struct Foo { var bar: Int = 0 }
        protocol P {}
        enum FuzzError: Error { case value }
        enum Token { case `import`(Int, String); case declarationModifier(Modifier); case other }
        enum Modifier { case open }
        func f<T>(_ value: T) -> T { value }
        func placeholder<T>() -> T { fatalError() }
        func fuzz<T>(items: [T], triples: [(T, T, T)], value: Optional<T>, pair: (T, T)) {
        let stream = AsyncStream<T> { continuation in continuation.finish() }
        \(body)
        }
        """
    }

    private func interpolationDelimiterFrontier(using rng: inout SplitMix64) -> String {
        let hole = [
            "A.B<C>.d",
            "DistributedReception.Key<ServiceActor>.aggressiveNodeReplacementService",
            "Foo<Bar<Baz>>.Qux.value",
            "Foo.Bar<Baz>.self",
            "items.map { $0 }.filter { _ in true }"
        ].random(using: &rng)
        let trailer = ["", ".count", " + \"tail\"", "\nlet other = fuzzValue"].random(using: &rng)
        let prelude = """
        struct A { struct B<T> { static var d: Int { 1 } } }
        struct C {}
        struct Foo { struct Bar<T> { struct Qux { static var value: Int { 1 } } } }
        struct Baz {}
        enum DistributedReception { struct Key<T> { static var aggressiveNodeReplacementService: Int { 1 } } }
        struct ServiceActor {}
        let items = [1]
        """
        switch rng.nextInt(upperBound: 4) {
        case 0:
            return "\(prelude)\nlet fuzzValue = \"prefix \\(\(hole)) suffix\"\(trailer)"
        case 1:
            return "\(prelude)\nlet fuzzValue = #\"prefix \\#(\(hole)) suffix\"#\(trailer)"
        case 2:
            return """
            \(prelude)
            let fuzzValue = \"\"\"
            prefix \\(\(hole))
            suffix
            \"\"\"\(trailer)
            """
        default:
            return "\(prelude)\nlet fuzzValue = \"\\(\(hole)) \\(try? f(1))\""
        }
    }

    private func conditionTrailingClosureFrontier(using rng: inout SplitMix64) -> String {
        [
            """
            while g(x: {
              d.h {
              }
            }) {}
            """,
            """
            guard a.allSatisfy({ x in
              b.allSatisfy {
                $0 == x
              }
            }) else { return }
            """,
            """
            if a.contains(where: { x in b.contains {
              $0 == x
            } }) { continue }
            """,
            """
            if g(x: value) {
            } else if h(y: {
              d.h {
              }
            }) {
            }
            """,
            """
            repeat {
              _ = value
            } while g(x: {
              d.h {
              }
            })
            """
        ].random(using: &rng)
    }

    private func parserModeScopeFrontier(using rng: inout SplitMix64) -> String {
        [
            """
            @available(*, deprecated, message: "plain")
            func fuzz() {}
            """,
            """
            @available(*, deprecated, message: #"raw"#)
            func fuzz() {}
            """,
            """
            struct Fuzz {
              init() {
                init
                init(value)
              }
            }
            """,
            """
            func fuzz() {
              if let self = Optional(Self.self) { _ = self }
              if let value = Optional(1) { _ = value }
            }
            """,
            """
            func fuzz() {
              let value = Foo()
              let result = value
              #if A
              .bar
              #else
              .bar
              #endif
            }
            """
        ].random(using: &rng)
    }

    private func statementMemberContextFrontier(using rng: inout SplitMix64) -> String {
        [
            """
            struct Fuzz {
              #if A
              @available(*, deprecated)
              var value: Int { 1 }
              #elseif B
              subscript(index: Int) -> Int { index }
              #else
              typealias Value = Int
              #endif
            }
            """,
            """
            enum Fuzz {
              #if A
              case value(Int)
              #elseif B
              case other
              #endif
            }
            """,
            """
            let base = Foo()
            let fuzzValue = base
            #if A
            .bar
            #else
            .bar
            #endif
            """,
            """
            func fuzz() {
              #if A
              let value = 1
              #elseif B
              return
              #else
              let other = 2
              #endif
            }
            """
        ].random(using: &rng)
    }

    private func genericMemberTypeFrontier(using rng: inout SplitMix64) -> String {
        let type = [
            "P.Type?",
            "P.Protocol!",
            "Foo.Bar<Baz>.Qux.Type",
            "(any P & Sendable).Type?",
            "Array<(repeat each T)>",
            "Dictionary<String, Foo.Bar<Baz>.Qux?>"
        ].random(using: &rng)
        let expression = [
            "Foo.Bar<Baz>.Qux.value",
            "Foo.Bar<Baz>.self",
            "A.B<C>.d",
            "(Foo.Bar<Baz>.Qux.self).self"
        ].random(using: &rng)
        return """
        protocol P {}
        struct A { struct B<T> { static var d: Int { 1 } } }
        struct C {}
        struct Foo { struct Bar<T> { struct Qux { static var value: Int { 1 } } } }
        struct Baz {}
        struct Fuzz<each T> {
          let typeValue: \(type) = placeholder()
          let exprValue = \(expression)
        }
        """
    }

    private func protocolAccessorFrontier(using rng: inout SplitMix64) -> String {
        let member = [
            "var value: Int { get async throws }",
            "subscript<T>(dynamicMember keyPath: KeyPath<Self, T>) -> T { get }",
            "associatedtype Element: Sequence where Element.Element == Int",
            "static func make() -> Self",
            "init(value: Int)",
            "struct Nested { var value: Int }",
            "enum NestedEnum { case value(Int) }"
        ].random(using: &rng)
        return """
        protocol FuzzProtocol {
          associatedtype Value
          \(member)
        }
        """
    }

    private func operatorBoundary(using rng: inout SplitMix64) -> String {
        let lhs = identifiers.random(using: &rng)
        let rhs = identifiers.random(using: &rng)
        let op = ["?", "!", "??", "?.", "!.", "?-", "!~", ">>", "> >", "..<", "...", "&"].random(using: &rng)
        return "let \(lhs) = \(rhs)\nlet fuzzValue = \(lhs)\(op)\(rhs)"
    }

    private func tryBoundary(using rng: inout SplitMix64) -> String {
        let tail = postfixTails.random(using: &rng)
        let marker = ["try", "try?", "try!"].random(using: &rng)
        let gap = ["", " ", "\n"].random(using: &rng)
        if marker == "try", rng.nextBool() {
            return "try\(tail)"
        }
        if marker != "try", rng.nextBool() {
            return "\(marker)\(operatorContinuations.random(using: &rng))"
        }
        return "\(marker)\(gap)f()"
    }

    private func castBoundary(using rng: inout SplitMix64) -> String {
        let cast = castOperators.random(using: &rng)
        let rhs = ["Foo", "Foo.Bar", "Foo.Bar?", "~Copyable", "any P", "A<B>", "A<B>?"].random(using: &rng)
        let continuation = ["", " ?? fallback", "?", "!", "??x", ".self"].random(using: &rng)
        return "value \(cast)\(rng.nextBool() ? "" : " ")\(rhs)\(continuation)"
    }

    private func regexBoundary(using rng: inout SplitMix64) -> String {
        let body = regexBodies.random(using: &rng)
        let prefix = ["let r = ", "_ = ", "try! ", "try? ", "x ? "].random(using: &rng)
        let opener = rng.nextBool() ? "/" : "#/"
        let closer = opener == "/" ? "/" : "/#"
        let suffix = ["", ".wholeMatch(in: s)", " / value", " + value"].random(using: &rng)
        return "let x = true\nlet value = 1\nlet s = \"abc\"\n\(prefix)\(opener)\(body)\(closer)\(suffix)"
    }

    private func ifConfigBoundary(using rng: inout SplitMix64) -> String {
        let condition = ["!!FOO", "!FOO", "FOO && !BAR", "canImport(A, _version: >=2.2)", "os(macOS)"].random(using: &rng)
        let body = ["let x = 1", ".member", "return", "@available(*, deprecated)"].random(using: &rng)
        return "#if \(condition)\n\(body)\n#endif"
    }

    private func memberKeyword(using rng: inout SplitMix64) -> String {
        let member = ["default", "inout", "import", "var", "let", "operator", "async", "await"].random(using: &rng)
        let base = ["value", "Foo()", "Token.other", "Self.self"].random(using: &rng)
        return "let fuzzValue = \(base).\(member)"
    }

    private func bindingPattern(using rng: inout SplitMix64) -> String {
        [
            "if let (a, b) = pair { _ = a; _ = b }",
            "guard let (a, b) = Optional(pair) else { return }",
            "if var (a, b) = Optional(pair) { _ = a; _ = b }",
            "for (a, var b, c) in triples { _ = a; _ = b; _ = c }",
            "var (b, var c) = pair"
        ].random(using: &rng)
    }

    private func extensionType(using rng: inout SplitMix64) -> String {
        let type = ["[Int]", "[String: Int]", "UInt8?", "Foo.Bar?", "UInt8!"].random(using: &rng)
        return "struct Foo { struct Bar {} }\nextension \(type) {\nfunc fuzz() {}\n}"
    }

    private func genericWhere(using rng: inout SplitMix64) -> String {
        let relation = [
            "T.Element == Foo.Bar",
            "T.Element: P",
            "T: Sequence",
            "T == Array<Foo.Bar?>",
            "T: ~Copyable"
        ].random(using: &rng)
        let punctuation = ["", "?", "!", ".self"].random(using: &rng)
        return "struct Foo { struct Bar {} }\nprotocol P {}\nstruct Fuzz<T> where \(relation)\(punctuation) {\nlet value: T\n}"
    }

    private func keyPathBoundary(using rng: inout SplitMix64) -> String {
        let base = ["\\Foo.bar", "\\Foo.Bar.default", "\\.default", "\\.foo?.bar", "\\.foo!.bar"].random(using: &rng)
        let suffix = ["", " as KeyPath<Foo, Int>", " ?? fallback", ".self", " / value"].random(using: &rng)
        return "\(base)\(suffix)"
    }

    private func interpolationBoundary(using rng: inout SplitMix64) -> String {
        let hole = ["value", "try? f()", "x as? Foo ?? fallback", "/abc/", "#/abc/#"].random(using: &rng)
        let tail = ["", " + \"tail\"", ".count", " / value"].random(using: &rng)
        return "let value = 1\nlet fallback = 2\nlet fuzzValue = \"prefix \\(\(hole)) suffix\"\(tail)"
    }

    private func closureLabel(using rng: inout SplitMix64) -> String {
        let label = callLabels.random(using: &rng)
        let first = ["f(value)", "f(a: value)", "f { value }", "f(value) { value }"].random(using: &rng)
        let trailing = ["\(label): { value }", "\(label): { _ in value }", "\(label): \\Foo.bar"].random(using: &rng)
        return "let value = 1\nlet fuzzValue = \(first) \(trailing)"
    }

    private func trailingClosureBoundary(using rng: inout SplitMix64) -> String {
        let callee = ["f", "Foo.bar", "value.map", "parser.parse"].random(using: &rng)
        let argument = ["", "value", "value,", "a: value", "a: value,"].random(using: &rng)
        let firstClosure = ["{ value }", "{ _ in value }", "{ $0 }"].random(using: &rng)
        let secondLabel = callLabels.random(using: &rng)
        let secondClosure = ["\(secondLabel): { value }", "\(secondLabel): { _ in value }"].random(using: &rng)
        let tail = ["", "\nlet y = value", ".member", "? value : result"].random(using: &rng)
        return "let value = 1\nlet result = 2\nlet fuzzValue = \(callee)(\(argument)) \(firstClosure) \(secondClosure)\(tail)"
    }

    private func conditionBoundary(using rng: inout SplitMix64) -> String {
        [
            "if case .some(let x) = value, x == x { _ = x }",
            "if let x = value, case .some(let y) = Optional(x) { _ = y }",
            "guard let x = value, x is T else { return }",
            "while let x = value, case .some = Optional(x) { break }",
            "if #available(macOS 14, *), let x = value { _ = x }",
            "if let x = value as? T ?? nil { _ = x }",
            "if value is T.Type, let x = value { _ = x }"
        ].random(using: &rng)
    }

    private func attributeBoundary(using rng: inout SplitMix64) -> String {
        let availability = [
            "@available(*, deprecated)",
            "@available(macOS 14, *)",
            "@available(macOS, introduced: 10.15, deprecated: 14.0, message: \"use f\")"
        ].random(using: &rng)
        let attribute = [availability, "@MainActor", "@objc", "@_spi(Private)", "@discardableResult"].random(using: &rng)
        let target = [
            "func fuzz() {}",
            "var value: Int { 1 }",
            "typealias Value = Int",
            "case value",
            ".member",
            "let fuzzValue = 1"
        ].random(using: &rng)
        let wrapper = rng.nextInt(upperBound: 4)
        switch wrapper {
        case 0:
            return "\(attribute)\n\(target)"
        case 1:
            return "struct Fuzz {\n\(attribute)\n\(target)\n}"
        case 2:
            return "#if os(macOS)\n\(attribute)\n\(target)\n#endif"
        default:
            return "extension Foo {\n\(attribute)\n\(target)\n}"
        }
    }

    private func packBoundary(using rng: inout SplitMix64) -> String {
        [
            "func fuzz<each T>(_ value: repeat each T) -> (repeat each T) { (repeat each value) }",
            "func fuzz<each T>(_ value: repeat each T) { _ = (repeat each value) }",
            "struct Fuzz<each T> { let value: (repeat each T) }",
            "func fuzz<each T, U>(_: repeat each T) where repeat each T: P {}",
            "func fuzz<each T>(_ value: repeat each T) { for item in repeat each value { _ = item } }",
            "let fuzzValue = (repeat each value)"
        ].random(using: &rng)
    }

    private func delimiterRecoveryBoundary(using rng: inout SplitMix64) -> String {
        [
            "let fuzzValue = f(value",
            "let fuzzValue = f(value, { value }",
            "let fuzzValue = [value, result",
            "let fuzzValue = (value, result",
            "if let x = value { _ = x",
            "struct Fuzz<T where T: P { let value: T }",
            "func fuzz<T: P(_ value: T) { _ = value }",
            "let fuzzValue: Array<Foo.Bar = placeholder()",
            "#if FOO\nlet x = 1"
        ].random(using: &rng)
    }

    private func accessorEffectBoundary(using rng: inout SplitMix64) -> String {
        [
            "struct Fuzz {\nvar value: Int {\n_read { yield 1 }\n_modify { var x = 1; yield &x }\n}\n}",
            "struct Fuzz {\nvar value: Int {\nget async throws { 1 }\n}\n}",
            "struct Fuzz {\nsubscript(index: Int) -> Int {\n_read { yield index }\n_modify { var x = index; yield &x }\n}\n}",
            "struct Fuzz {\nvar value: Int {\nborrowing get { 1 }\nconsuming set { _ = newValue }\n}\n}",
            "struct Fuzz {\nstatic subscript<T>(dynamicMember keyPath: KeyPath<Foo, T>) -> T { placeholder() }\n}"
        ].random(using: &rng)
    }

    private func ownershipModifierBoundary(using rng: inout SplitMix64) -> String {
        [
            "func fuzz(_ value: borrowing Foo) { _ = value }",
            "func fuzz(_ value: consuming Foo) { _ = value }",
            "func fuzz(_ value: inout sending Foo) { _ = value }",
            "func fuzz<T: ~Copyable>(_ value: consuming T) {}",
            "struct Fuzz<T: ~Copyable> { consuming func take() {} }",
            "let fuzzValue = consume value",
            "let fuzzValue = copy value"
        ].random(using: &rng)
    }

    private func macroPoundBoundary(using rng: inout SplitMix64) -> String {
        [
            "#if hasFeature(VariadicGenerics)\nfunc fuzz<each T>(_ value: repeat each T) {}\n#endif",
            "#if swift(>=6.0)\nlet fuzzValue = #fileID\n#else\nlet fuzzValue = #file\n#endif",
            "#warning(\"fuzz\")\nlet fuzzValue = 1",
            "#sourceLocation(file: \"fuzz.swift\", line: 10)\nlet fuzzValue = 1\n#sourceLocation()",
            "let fuzzValue = #function",
            "let fuzzValue = #Predicate<Foo> { $0.bar == 1 }",
            "@Observable\nclass Fuzz { var value = 1 }"
        ].random(using: &rng)
    }

    private func collectionTypeBoundary(using rng: inout SplitMix64) -> String {
        let type = [
            "[Foo.Bar?]",
            "[String: [Foo.Bar?]]",
            "[(label: Int, value: Foo.Bar)]",
            "Dictionary<String, Array<Foo.Bar?>>",
            "Array<Dictionary<String, Foo.Bar?>>",
            "[(any P) -> (some P)]"
        ].random(using: &rng)
        let suffix = ["", "?", "!", ".Type", ".self"].random(using: &rng)
        return "struct Foo { struct Bar {} }\nprotocol P {}\nlet fuzzValue: \(type)\(suffix) = placeholder()"
    }

    private func declarationModifierStack(using rng: inout SplitMix64) -> String {
        [
            "public private(set) var value: Int = 1",
            "package final class Fuzz {}",
            "nonisolated(unsafe) var value: Int { 1 }",
            "isolated(any) func fuzz() {}",
            "open override class func fuzz() {}",
            "@preconcurrency import Foundation",
            "@_exported import Swift"
        ].random(using: &rng)
    }

    private func enumCasePatternBoundary(using rng: inout SplitMix64) -> String {
        [
            "enum Fuzz { case `default`(Int), `operator`(String), value }\nswitch Fuzz.default(1) { case .default(let value): break case .operator(_): break case .value: break }",
            "if case .some(.some(let value)) = Optional(Optional(value)) { _ = value }",
            "guard case let .some(value)? = Optional(Optional(value)) else { return }",
            "switch value { case is Foo.Type: break case let x as Foo: _ = x default: break }",
            "switch value { case _ as (any P)?: break default: break }"
        ].random(using: &rng)
    }

    private func subscriptCallBoundary(using rng: inout SplitMix64) -> String {
        [
            "let fuzzValue = value[0](1)",
            "let fuzzValue = value[0] { value }",
            "let fuzzValue = value[keyPath: \\.foo?.bar]",
            "let fuzzValue = Foo.Bar.self[dynamicMember: \\Foo.bar]",
            "let fuzzValue = items[items.startIndex...].map { $0 }",
            "let fuzzValue = value?.foo[0]?.bar(default: value)"
        ].random(using: &rng)
    }

    private func effectfulFunctionType(using rng: inout SplitMix64) -> String {
        let type = [
            "() async throws -> Int",
            "@Sendable () async throws(FuzzError) -> Int",
            "(borrowing Foo) -> consuming Foo",
            "isolated any Actor",
            "sending @escaping () -> Void",
            "@escaping @Sendable (repeat each T) async -> (repeat each T)"
        ].random(using: &rng)
        return "enum FuzzError: Error { case value }\nstruct Foo {}\nlet fuzzValue: \(type) = placeholder()"
    }

    private func memberListBoundary(using rng: inout SplitMix64) -> String {
        let separator = ["\n", ";\n", "\n\n"].random(using: &rng)
        let memberPool = [
            "@available(*, deprecated)\nvar value: Int = 1",
            "subscript(index: Int) -> Int { get { index } set { _ = newValue } }",
            "init?(value: Int) { self.value = value }",
            "static func `operator`<T>(_ value: T) -> T { value }",
            "#if os(macOS)\nlet platform = 1\n#else\nlet platform = 2\n#endif",
            "enum Nested { case `default`, value(Int) }"
        ]
        let members = (0..<max(2, rng.nextInt(upperBound: 5) + 2)).map { _ in
            memberPool.random(using: &rng)
        }
        let body = members.joined(separator: separator)
        return "struct Fuzz {\nvar value: Int = 0\n\(body)\n}"
    }

    private func protocolRequirementBoundary(using rng: inout SplitMix64) -> String {
        [
            "protocol Fuzz {\nassociatedtype Element: Sequence where Element.Element == Int\nvar value: Element { get async throws }\nsubscript<T>(dynamicMember keyPath: KeyPath<Element, T>) -> T { get }\n}",
            "protocol Fuzz<each T> {\nassociatedtype Value\nfunc call(_: repeat each T) async throws -> Value\n}",
            "protocol Fuzz: AnyObject where Self.Value == Int {\nassociatedtype Value\ninit(value: Value)\nstatic func make() -> Self\n}",
            "protocol Fuzz {\n@available(*, deprecated)\nfunc value<T>(for keyPath: KeyPath<Self, T>) -> T\n}"
        ].random(using: &rng)
    }

    private func operatorDeclBoundary(using rng: inout SplitMix64) -> String {
        [
            "infix operator ?=: AssignmentPrecedence\nfunc ?=<T>(lhs: inout T, rhs: T?) { if let rhs { lhs = rhs } }",
            "prefix operator !!\nprefix func !!(value: Bool) -> Bool { !value }",
            "postfix operator •\npostfix func •(value: Int) -> Int { value }",
            "precedencegroup FuzzPrecedence { associativity: right higherThan: AdditionPrecedence }\ninfix operator <~>: FuzzPrecedence\nfunc <~><T>(lhs: T, rhs: T) -> T { lhs }"
        ].random(using: &rng)
    }

    private func initSubscriptBoundary(using rng: inout SplitMix64) -> String {
        [
            "struct Fuzz {\nlet value: Int\ninit?(_ value: Int) async throws { self.value = value }\n}",
            "struct Fuzz {\nsubscript<T>(keyPath path: KeyPath<Foo, T>? = nil) -> T { get async { placeholder() } }\n}",
            "class Fuzz {\nrequired convenience init<T>(_ value: T) where T: P { self.init() }\ninit() {}\n}",
            "struct Fuzz {\nsubscript(dynamicMember member: String) -> Int { _read { yield 1 } _modify { var x = 1; yield &x } }\n}"
        ].random(using: &rng)
    }

    private func nestedIfConfigBoundary(using rng: inout SplitMix64) -> String {
        let inner = [
            "#sourceLocation(file: \"nested.swift\", line: 2)\nlet fuzzValue = #line\n#sourceLocation()",
            "@available(*, deprecated)\nfunc fuzz() {}",
            "func fuzz<each T>(_ value: repeat each T) { _ = (repeat each value) }",
            "let regex = /a  b/.wholeMatch(in: s)"
        ].random(using: &rng)
        let outer = ["compiler(>=6.0)", "hasFeature(VariadicGenerics)", "os(macOS)", "!!FOO"].random(using: &rng)
        let alternate = ["#error(\"fuzz\")", "let fallback = #fileID", "case value"].random(using: &rng)
        return "#if \(outer)\n#if canImport(Foundation)\n\(inner)\n#else\n\(alternate)\n#endif\n#endif"
    }

    private func regexTriviaBoundary(using rng: inout SplitMix64) -> String {
        let body = ["a b", "a  b", "a\tb", #"a\/ b"#, #"(?<name>a)  b"#].random(using: &rng)
        let prefix = ["let r = ", "_ = ", "let fuzzValue = try? ", "let fuzzValue = x ? "].random(using: &rng)
        let suffix = ["", ".wholeMatch(in: s)", " / value", " ? value : fallback"].random(using: &rng)
        return "let x = true\nlet value = 1\nlet fallback = 2\nlet s = \"abc\"\n\(prefix)/\(body)/\(suffix)"
    }

    private func castTryOperatorCluster(using rng: inout SplitMix64) -> String {
        [
            "let fuzzValue = try? f(a as? A<B>??x) ?? fallback",
            "let fuzzValue = value as!A<B>???x",
            "let fuzzValue = try.\nf()",
            "let fuzzValue = try! value as? Foo ?? fallback",
            "let fuzzValue = a < b > (c) ? value as? Foo : value as! Foo",
            "let parser = await\nlet fuzzValue = parser?.await"
        ].random(using: &rng)
    }

    private func patternMatrixBoundary(using rng: inout SplitMix64) -> String {
        [
            "switch value { case let .some(x)??: _ = x case .none: break default: break }",
            "if case (.some(let x), _ as Foo.Type)? = Optional((value, Foo.self)) { _ = x }",
            "guard case let Token.import(_, s)? = Optional(Token.import(1, \"x\")) else { return }",
            "switch value { case let x as (any P)?: _ = x case is Foo.Type: break default: break }",
            "for case let .some(value)? in [Optional(Optional(value))] { _ = value }"
        ].random(using: &rng)
    }

    private func ifConfigMemberContextBoundary(using rng: inout SplitMix64) -> String {
        let condition = ["FOO", "!FOO", "compiler(>=6.0)", "canImport(Foundation)", "os(macOS)"].random(using: &rng)
        let leadingDot = [".member", ".method()", ".default"].random(using: &rng)
        let declaration = [
            "var value: Int = 1",
            "@available(*, deprecated)\nfunc value() -> Int { 1 }",
            "subscript(index: Int) -> Int { index }",
            "case value(Int)"
        ].random(using: &rng)
        let shape = rng.nextInt(upperBound: 5)
        switch shape {
        case 0:
            return "#if \(condition)\n\(leadingDot)\n#else\n.member\n#endif"
        case 1:
            return "let base = Foo()\nlet fuzzValue = base\n#if \(condition)\n\(leadingDot)\n#else\n.other\n#endif"
        case 2:
            return "struct Fuzz {\n#if \(condition)\n\(declaration)\n#else\nvar other: Int = 2\n#endif\n}"
        case 3:
            return "enum Fuzz {\n#if \(condition)\ncase value(Int)\n#else\ncase other\n#endif\n}"
        default:
            return "func fuzz() {\n#if \(condition)\nlet value = 1\n#else\nreturn\n#endif\n}"
        }
    }

    private func keyPathComponentMatrix(using rng: inout SplitMix64) -> String {
        let base = ["\\Foo", "\\Foo.Bar", "\\", "\\."].random(using: &rng)
        let component = [
            ".default",
            ".foo?.bar",
            ".foo!.bar",
            ".foo?[0]",
            ".foo![keyPath: \\.bar]",
            ".self",
            ".Type",
            ".[dynamicMember: \\.bar]"
        ].random(using: &rng)
        let tail = ["", ".self", " as Any", " ?? fallback", " / value"].random(using: &rng)
        return "\(base)\(component)\(tail)"
    }

    private func regexSlashOperatorBoundary(using rng: inout SplitMix64) -> String {
        let body = ["abc", "a b", "a  b", #"a\/b"#, #"[a b]"#, #"(a b)"#, #"(?<name>a)  b"#].random(using: &rng)
        let slashExpr = ["/\(body)/", "#/\(body)/#"].random(using: &rng)
        let shape = [
            "let x = true\nlet value = 1\nlet s = \"abc\"\nlet fuzzValue = x ? \(slashExpr).wholeMatch(in: s) : value / value",
            "let value = 1\nlet s = \"abc\"\nlet fuzzValue = try? \(slashExpr).wholeMatch(in: s) ?? nil",
            "let value = 1\nlet fuzzValue = value /\n\(slashExpr)",
            "let s = \"abc\"\nlet regex = \(slashExpr)\nlet fuzzValue = regex.wholeMatch(in: s)",
            "let value = 1\nlet fuzzValue = value /* comment */ / value"
        ]
        return shape.random(using: &rng)
    }

    private func memberListWideBoundary(using rng: inout SplitMix64) -> String {
        let separator = ["\n", ";\n", "\n\n", "\n#if os(macOS)\nvar gated = 1\n#endif\n"].random(using: &rng)
        let container = ["struct", "class", "actor", "extension", "protocol", "enum"].random(using: &rng)
        let members = [
            "@MainActor\nvar value: Int { 1 }",
            "static subscript<T>(dynamicMember keyPath: KeyPath<Foo, T>) -> T { placeholder() }",
            "init?<T>(_ value: T) where T: P {}",
            "func call(_ value: borrowing Foo) async throws -> consuming Foo { value }",
            "typealias Element = Array<Foo.Bar?>",
            "#if compiler(>=6.0)\nvar platform = 1\n#else\nvar platform = 2\n#endif",
            "case value(Int), `default`"
        ]
        let body = (0..<max(2, rng.nextInt(upperBound: 5) + 2)).map { _ in members.random(using: &rng) }.joined(separator: separator)
        switch container {
        case "class":
            return "class Fuzz {\n\(body)\n}"
        case "actor":
            return "actor Fuzz {\n\(body)\n}"
        case "extension":
            return "struct Foo { struct Bar {} }\nextension Foo {\n\(body)\n}"
        case "protocol":
            return "protocol Fuzz {\nassociatedtype Value\n\(body)\n}"
        case "enum":
            return "enum Fuzz {\n\(body)\n}"
        default:
            return "struct Fuzz {\n\(body)\n}"
        }
    }

    private func typeCompositionBoundary(using rng: inout SplitMix64) -> String {
        let type = [
            "(some P & Sendable)?",
            "(any P & AnyObject).Type",
            "((Int, String) async throws(FuzzError) -> Foo.Bar?)?",
            "Array<(repeat each T)>",
            "Dictionary<String, (borrowing Foo) -> consuming Foo>",
            "sending @escaping @Sendable () async -> Void",
            "isolated (any Actor)?",
            "Foo<Bar<Baz>.Qux>.Type"
        ].random(using: &rng)
        return "protocol P {}\nstruct Foo { struct Bar {} }\nstruct Bar<T> { struct Baz { struct Qux {} } }\nenum FuzzError: Error { case value }\nlet fuzzValue: \(type) = placeholder()"
    }

    private func contextualKeywordBoundary(using rng: inout SplitMix64) -> String {
        let word = ["await", "async", "consume", "copy", "isolated", "borrowing", "consuming", "sending", "operator", "default"].random(using: &rng)
        let shape = [
            "let \(word) = 1\nlet fuzzValue = \(word)",
            "struct Fuzz { var \(word): Int = 1 }\nlet fuzzValue = Fuzz().\(word)",
            "func fuzz(\(word): Int) { _ = \(word) }",
            "enum Fuzz { case `\(word)`(Int) }\nlet fuzzValue = Fuzz.`\(word)`(1)",
            "let fuzzValue = value.\(word)"
        ]
        return shape.random(using: &rng)
    }

    private func importAttributeBoundary(using rng: inout SplitMix64) -> String {
        [
            "@preconcurrency @_exported import Foundation",
            "@_implementationOnly import Foundation",
            "import struct Foundation.Date",
            "import enum Foundation.ComparisonResult",
            "import func Darwin.sqrt",
            "import operator Swift.+",
            "#if canImport(Foundation)\n@preconcurrency import Foundation\n#else\nimport Swift\n#endif"
        ].random(using: &rng)
    }

    private func closureResultBoundary(using rng: inout SplitMix64) -> String {
        [
            "func fuzz(@ArrayBuilder _ body: () -> [Int]) {}\nfuzz {\n1\n#if FOO\n2\n#endif\n}",
            "let fuzzValue = items.map { item in\n#if FOO\nitem\n#else\nitem\n#endif\n}.filter { _ in true }",
            "let fuzzValue = f(value) { value } async: { result }",
            "let fuzzValue = { () async throws -> Int in\ntry await f()\n}()",
            "let fuzzValue = f { value }\n#if FOO\n.member\n#endif"
        ].random(using: &rng)
    }

    private func statementControlBoundary(using rng: inout SplitMix64) -> String {
        [
            "do throws(FuzzError) { throw FuzzError.value } catch FuzzError.value { return } catch { return }",
            "if #available(macOS 14, *), case let .some(x)? = Optional(value) { _ = x } else { return }",
            "switch value { case let x where x is T: _ = x default: break }",
            "for try await item in stream { _ = item }",
            "while let value = value, value is T { break }",
            "#if FOO\nfallthrough\n#else\nbreak\n#endif"
        ].random(using: &rng)
    }

    private func macroAttributeDirectiveBoundary(using rng: inout SplitMix64) -> String {
        [
            "@attached(member, names: named(value))\nmacro Fuzz() = #externalMacro(module: \"M\", type: \"F\")",
            "@freestanding(expression)\nmacro fuzz<T>(_ value: T) -> T = #externalMacro(module: \"M\", type: \"F\")",
            "#if hasAttribute(Observable)\n@Observable\nclass Fuzz { var value = 1 }\n#endif",
            "#if hasFeature(StrictConcurrency)\n@preconcurrency import Foundation\n#endif",
            "#sourceLocation(file: \"generated.swift\", line: 42)\n@available(*, deprecated)\nfunc fuzz() {}\n#sourceLocation()"
        ].random(using: &rng)
    }

    private func attributeIfConfigElseifList(using rng: inout SplitMix64) -> String {
        let attributePool = [
            "@available(*)",
            "@available(*, deprecated)",
            "@MainActor",
            "@discardableResult",
            "@_spi(Private)"
        ]
        let target = ["func fuzz() {}", "var value: Int { 1 }", "struct Fuzz {}", "enum Fuzz { case value }"].random(using: &rng)
        return """
        #if A
        \(attributePool.random(using: &rng))
        #elseif B
        \(attributePool.random(using: &rng))
        #elseif C
        \(attributePool.random(using: &rng))
        #else
        \(attributePool.random(using: &rng))
        #endif
        \(target)
        """
    }

    private func multilineInterpolationBoundary(using rng: inout SplitMix64) -> String {
        let hole = ["value", "try? f(value)", "value as? Foo ?? fallback", "/a  b/", "items.map { $0 }"].random(using: &rng)
        let indent = ["", "    ", "\t"].random(using: &rng)
        let trailer = ["", ".count", "\nlet other = fuzzValue"].random(using: &rng)
        return """
        struct Foo { var bar: Int = 0 }
        let value = 1
        let fallback = 2
        let items = [value]
        let fuzzValue = \"\"\"
        \(indent)prefix \\(\(hole))
        \(indent)suffix
        \(indent)\"\"\"\(trailer)
        """
    }

    private func grammarishMemberList(using rng: inout SplitMix64) -> String {
        let ifMember = """
        #if A
        @available(*, deprecated)
        func a() {}
        #elseif B
        var b: Int { 1 }
        #else
        subscript(index: Int) -> Int { index }
        #endif
        """
        let members = [
            "case value(Int)",
            "@MainActor\nfunc call<T>(_ value: T) async throws -> T { value }",
            "typealias Element = Array<Foo.Bar?>",
            "init?<T>(_ value: T) where T: P {}",
            ifMember
        ]
        let body = (0..<max(2, rng.nextInt(upperBound: 5) + 2)).map { _ in members.random(using: &rng) }.joined(separator: ["\n", ";\n"].random(using: &rng))
        return ["enum", "struct", "class", "actor", "protocol"].random(using: &rng) == "enum"
            ? "enum Fuzz {\n\(body)\n}"
            : "struct Foo { struct Bar {} }\nprotocol P {}\nstruct Fuzz {\n\(body)\n}"
    }

    private func tsplDivergenceSpecializedAttribute(using rng: inout SplitMix64) -> String {
        [
            "@_dynamicReplacement(for: Foo.bar(_:))\nfunc fuzz(_ value: Int) -> Int { value }",
            "@_implements(P, value)\nvar fuzzValue: Int { 1 }",
            "@_documentation(metadata: \"fuzz\", visibility: internal)\nfunc fuzz() {}",
            "@_originallyDefinedIn(module: \"FuzzKit\", macOS 10.15, iOS 13)\nstruct Fuzz {}",
            "@_specialize(exported: true, kind: full, availability: macOS, introduced: 14.0; where T == Int)\nfunc fuzz<T>(_ value: T) -> T { value }",
            "@differentiable(reverse, wrt: (x, y where T: FloatingPoint))\nfunc fuzz<T: FloatingPoint>(_ x: T, _ y: T) -> T { x }",
            "@derivative(of: Foo.Bar.+, wrt: (0, 1))\nfunc fuzz(_ x: Double, _ y: Double) -> Double { x }",
            "@attached(member, names: named(init), named(subscript(_:)), overloaded)\nmacro Fuzz() = #externalMacro(module: \"M\", type: \"F\")"
        ].random(using: &rng)
    }

    private func tsplDivergenceProtocolBody(using rng: inout SplitMix64) -> String {
        let members = [
            "var value: Int = 1",
            "var computed: Int { 1 }",
            "static subscript(dynamicMember member: String) -> Int { get }",
            "enum Nested { case value(Int) }",
            "struct Nested { var value: Int }",
            "deinit { }",
            "func bodyful() { _ = Self.self }",
            "@available(*, deprecated)\nvar annotated: Int { get async throws }"
        ]
        let body = (0..<max(2, rng.nextInt(upperBound: 4) + 2)).map { _ in
            members.random(using: &rng)
        }.joined(separator: "\n")
        return """
        protocol FuzzProtocol {
        associatedtype Value
        \(body)
        }
        """
    }

    private func tsplDivergenceAccessorCommitment(using rng: inout SplitMix64) -> String {
        [
            "struct Fuzz {\nvar value: Int {\nget\nset(value)\n}\n}",
            "struct Fuzz {\nvar value: Int {\nget { 1 }\nset { _ = newValue }\n}\n}",
            "struct Fuzz {\nvar value: Int = 0 {\nwillSet(value) { _ = value }\ndidSet { _ = oldValue }\n}\n}",
            "struct Fuzz {\nvar value: Int {\n_read { yield 1 }\n_modify { var x = 1; yield &x }\n}\n}",
            "struct Fuzz {\nvar value: Int {\nget async throws { 1 }\nset { _ = newValue }\n}\n}",
            "struct Fuzz {\nvar value: Int {\n@available(*, deprecated) get { 1 }\nnonmutating set { _ = newValue }\n}\n}",
            "struct Fuzz {\nsubscript(index: Int) -> Int {\nget { index }\nset(value) { _ = value }\n}\n}"
        ].random(using: &rng)
    }

    private func tsplDivergenceTypeShape(using rng: inout SplitMix64) -> String {
        let type = [
            "any P",
            "(any P & Sendable).Type",
            "some P",
            "(some P).Type",
            "repeat each T",
            "(repeat each T) -> Void",
            "@Sendable (borrowing Foo, consuming Foo) async throws(FuzzError) -> sending Foo",
            "nonisolated(nonsending) () async -> Void",
            "isolated any Actor",
            "~Copyable",
            "Foo.Bar?.Type"
        ].random(using: &rng)
        let wrapper = [
            "protocol P {}\nstruct Foo { struct Bar {} }\nenum FuzzError: Error { case value }\nlet fuzzValue: \(type) = placeholder()",
            "protocol P {}\nstruct Foo { struct Bar {} }\nstruct Fuzz<each T> { let value: \(type) }",
            "protocol P {}\nstruct Foo { struct Bar {} }\nfunc fuzz<each T>(_ value: \(type)) {}",
            "protocol P {}\nstruct Foo { struct Bar {} }\nextension \(type) { func fuzz() {} }"
        ]
        return wrapper.random(using: &rng)
    }

    private func tsplDivergencePatternShape(using rng: inout SplitMix64) -> String {
        [
            "switch value { case let .some(.some(x))?: _ = x default: break }",
            "switch value { case Token.default(let value): _ = value case .operator(let name): _ = name default: break }",
            "if case let Token.import(_, name) = token { _ = name }",
            "if case var (a, b)? = Optional(pair) { _ = a; _ = b }",
            "guard case let .some(value as (any P)) = Optional(value) else { return }",
            "switch value { case is (any P).Type: break case let x as Foo.Bar?: _ = x default: break }",
            "for case let .some(value)? in [Optional(Optional(value))] { _ = value }"
        ].random(using: &rng)
    }

    private func structuralSeedSplice(using rng: inout SplitMix64) -> GeneratedSource {
        let entry = seedCorpus.random(using: &rng)
        let mutated = mutateSeed(entry.source, using: &rng)
        let wrapper = [
            "struct Fuzz {\n#if A\n\(mutated)\n#elseif B\nvar sentinel: Int = 1\n#endif\n}",
            "#if A\n\(mutated)\n#elseif B\n.member\n#else\nlet sentinel = 1\n#endif",
            "func fuzz() {\n#if A\n\(mutated)\n#elseif B\nreturn\n#endif\n}",
            "@available(*, deprecated)\n\(mutated)"
        ].random(using: &rng)
        return GeneratedSource(label: "seed-corpus-structural-splice:\(entry.label)", source: wrapper)
    }

    private func seedCorpusSource(using rng: inout SplitMix64, mutated: Bool) -> GeneratedSource {
        let entry = seedCorpus.random(using: &rng)
        let source = mutated ? mutateSeed(entry.source, using: &rng) : entry.source
        let mode = mutated ? "mutated" : "raw"
        return GeneratedSource(label: "seed-corpus-\(mode):\(entry.label)", source: source)
    }

    private func interestingCorpusSource(using rng: inout SplitMix64) -> GeneratedSource {
        let entry = interestingCorpus.random(using: &rng)
        switch rng.nextInt(upperBound: 5) {
        case 0:
            return GeneratedSource(label: "interesting-corpus-raw:\(entry.label)", source: entry.source)
        case 1:
            return GeneratedSource(label: "interesting-corpus-mutated:\(entry.label)", source: mutateSeed(entry.source, using: &rng))
        case 2:
            let context = fuzzContexts.random(using: &rng)
            return GeneratedSource(
                label: "interesting-corpus-wide:\(context.name):\(entry.label)",
                source: context.wrap(mutateSeed(entry.source, using: &rng))
            )
        case 3 where interestingCorpus.count > 1:
            let second = interestingCorpus.random(using: &rng)
            return GeneratedSource(
                label: "interesting-corpus-crossover:\(entry.label)+\(second.label)",
                source: "\(mutateSeed(entry.source, using: &rng))\n\(mutateSeed(second.source, using: &rng))"
            )
        default:
            return GeneratedSource(
                label: "interesting-corpus-ifconfig:\(entry.label)",
                source: "#if A\n\(entry.source)\n#elseif B\n\(mutateSeed(entry.source, using: &rng))\n#endif"
            )
        }
    }

    private func wrappedSeedCorpusSource(using rng: inout SplitMix64) -> GeneratedSource {
        let entry = seedCorpus.random(using: &rng)
        let wrappers: [(String) -> String] = [
            { (source: String) in "func fuzz() {\n\(source)\n}" },
            { (source: String) in "struct Fuzz {\n\(source)\n}" },
            { (source: String) in "#if os(macOS)\n\(source)\n#endif" },
            { (source: String) in "do {\n\(source)\n}" }
        ]
        return GeneratedSource(
            label: "seed-corpus-wrapped:\(entry.label)",
            source: wrappers.random(using: &rng)(mutateSeed(entry.source, using: &rng))
        )
    }

    private func seedCorpusCrossover(using rng: inout SplitMix64) -> GeneratedSource {
        let first = seedCorpus.random(using: &rng)
        let second = seedCorpus.random(using: &rng)
        let source = "\(mutateSeed(first.source, using: &rng))\n\(mutateSeed(second.source, using: &rng))"
        return GeneratedSource(label: "seed-corpus-crossover:\(first.label)+\(second.label)", source: source)
    }

    private func mutateSeed(_ source: String, using rng: inout SplitMix64) -> String {
        var result = mutate(source, using: &rng)
        let mutationCount = rng.nextInt(upperBound: 5)
        for _ in 0..<mutationCount {
            switch rng.nextInt(upperBound: 10) {
            case 0:
                result = result.replacingOccurrences(of: "(", with: rng.nextBool() ? "(\n" : "(")
            case 1:
                result = result.replacingOccurrences(of: "{", with: rng.nextBool() ? "{\n" : "{")
            case 2:
                result = result.replacingOccurrences(of: ",", with: rng.nextBool() ? ",\n" : ", ")
            case 3:
                result = result.replacingOccurrences(of: "->", with: rng.nextBool() ? "\n->" : "->")
            case 4:
                result = result.replacingOccurrences(of: ":", with: rng.nextBool() ? " :" : ":")
            case 5:
                result += rng.nextBool() ? "\n#if FOO\nlet fuzzSentinel = 1\n#endif" : "\n#warning(\"seed\")"
            case 6:
                result = result.replacingOccurrences(of: "some", with: rng.nextBool() ? "any" : "some")
            case 7:
                result = result.replacingOccurrences(of: "any", with: rng.nextBool() ? "some" : "any")
            case 8:
                result = result.replacingOccurrences(of: "async", with: rng.nextBool() ? "async throws" : "async")
            default:
                result = result.replacingOccurrences(of: "where", with: rng.nextBool() ? "\nwhere" : "where")
            }
        }
        return result
    }

    private func mutate(_ source: String, using rng: inout SplitMix64) -> String {
        var result = source
        let mutationCount = rng.nextInt(upperBound: 6)
        for _ in 0..<mutationCount {
            switch rng.nextInt(upperBound: 15) {
            case 0:
                result = result.replacingOccurrences(of: ">", with: rng.nextBool() ? ">>" : "> >")
            case 1:
                result = result.replacingOccurrences(of: "?", with: rng.nextBool() ? "? " : "?")
            case 2:
                result = result.replacingOccurrences(of: "!", with: rng.nextBool() ? "! " : "!")
            case 3:
                result = result.replacingOccurrences(of: ".", with: rng.nextBool() ? ".\n" : ".")
            case 4:
                result += rng.nextBool() ? " // fuzz\n" : "\n"
            case 5:
                result = "(\(result))"
            case 6:
                result = result.replacingOccurrences(of: "as?", with: rng.nextBool() ? "as? " : "as?")
            case 7:
                result = result.replacingOccurrences(of: "try ", with: rng.nextBool() ? "try" : "try\n")
            case 8:
                result = result.replacingOccurrences(of: "/", with: rng.nextBool() ? "#/" : "/")
            case 9:
                result = result.replacingOccurrences(of: "let", with: rng.nextBool() ? "var" : "let")
            case 10:
                result = result.replacingOccurrences(of: "Foo", with: rng.nextBool() ? "Foo.Bar" : "Foo")
            case 11:
                result = result.replacingOccurrences(of: "\\.", with: rng.nextBool() ? "\\Foo." : "\\.")
            case 12:
                result = result.replacingOccurrences(of: "where", with: rng.nextBool() ? "\nwhere" : "where")
            case 13:
                result = result.replacingOccurrences(of: "{ value }", with: rng.nextBool() ? "{ value }()" : "{ value }")
            default:
                result = result.replacingOccurrences(of: "try", with: ["try", "try?", "try!"].random(using: &rng))
            }
        }
        return result
    }
}

struct SplitMix64 {
    private var state: UInt64

    init(seed: UInt64) {
        state = seed
    }

    mutating func next() -> UInt64 {
        state &+= 0x9E3779B97F4A7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58476D1CE4E5B9
        z = (z ^ (z >> 27)) &* 0x94D049BB133111EB
        return z ^ (z >> 31)
    }

    mutating func nextInt(upperBound: Int) -> Int {
        Int(next() % UInt64(upperBound))
    }

    mutating func nextBool() -> Bool {
        next() & 1 == 0
    }
}

extension Array {
    func random(using rng: inout SplitMix64) -> Element {
        self[rng.nextInt(upperBound: count)]
    }
}

extension String {
    func trimmedForSeedCorpus() -> String {
        trimmingCharacters(in: .whitespacesAndNewlines)
    }
}

func appendJSONLine<T: Encodable>(_ value: T, to handle: FileHandle) throws {
    let encoder = JSONEncoder()
    encoder.outputFormatting = [.sortedKeys]
    let data = try encoder.encode(value)
    handle.write(data)
    handle.write(Data("\n".utf8))
}

func prettyJSON<T: Encodable>(_ value: T) throws -> Data {
    let encoder = JSONEncoder()
    encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
    return try encoder.encode(value)
}

func makeFailureSignal(
    status: String,
    probe: ProbeOutput?,
    result: ProcessResult,
    generator: String
) -> FailureSignal? {
    guard status != "same" else { return nil }

    let rawSummary: String
    switch status {
    case "tree-difference":
        rawSummary = "tree-difference|\(dumpDifferenceSignal(reference: probe?.referenceDump, advent: probe?.adventDump))"
    case "advent-overaccept":
        rawSummary = [
            "advent-overaccept",
            "compiler=\(probe?.compilerAccepted?.description ?? "unknown")",
            "swiftSyntaxHasError=\(probe?.swiftSyntaxHasError.description ?? "unknown")",
            dumpShapeSignal(probe?.referenceDump)
        ].joined(separator: "|")
    case "advent-underaccept":
        rawSummary = [
            "advent-underaccept",
            "compiler=\(probe?.compilerAccepted?.description ?? "unknown")",
            "swiftSyntaxHasError=\(probe?.swiftSyntaxHasError.description ?? "unknown")",
            dumpShapeSignal(probe?.referenceDump)
        ].joined(separator: "|")
    case "reference-disagreement":
        rawSummary = [
            "reference-disagreement",
            "compiler=\(probe?.compilerAccepted?.description ?? "unknown")",
            "swiftSyntaxHasError=\(probe?.swiftSyntaxHasError.description ?? "unknown")",
            dumpShapeSignal(probe?.referenceDump)
        ].joined(separator: "|")
    case "residual-ambiguity":
        rawSummary = "\(status)|\(firstUsefulLine(probe?.residualAmbiguities.first ?? ""))"
    case "advent-no-generated-tree":
        rawSummary = "\(status)|\(firstUsefulLine(probe?.generatorDiagnostics.joined(separator: "\n")))|\(dumpShapeSignal(probe?.referenceDump))"
    case "timeout":
        rawSummary = "\(status)|generator=\(generator)"
    case "crash", "invalid-probe-output", "probe-error":
        rawSummary = "\(status)|\(firstUsefulLine(probe?.error ?? result.stderr))"
    default:
        rawSummary = "\(status)|\(firstUsefulLine(probe?.error ?? result.stderr))|\(dumpShapeSignal(probe?.referenceDump))"
    }

    return FailureSignal(
        hash: stableHash(rawSummary),
        summary: abbreviate(rawSummary, maxLength: 240)
    )
}

func dumpDifferenceSignal(reference: String?, advent: String?) -> String {
    let referenceLines = normalizedDumpLines(reference)
    let adventLines = normalizedDumpLines(advent)
    let count = max(referenceLines.count, adventLines.count)
    for index in 0..<count {
        let referenceLine = index < referenceLines.count ? referenceLines[index] : "<missing>"
        let adventLine = index < adventLines.count ? adventLines[index] : "<missing>"
        if referenceLine != adventLine {
            return "line=\(index)|ref=\(referenceLine)|advent=\(adventLine)"
        }
    }
    return "no-normalized-difference|refLines=\(referenceLines.count)|adventLines=\(adventLines.count)"
}

func dumpShapeSignal(_ dump: String?) -> String {
    let lines = normalizedDumpLines(dump)
    if lines.isEmpty { return "shape=<none>" }
    return "shape=" + lines.prefix(40).joined(separator: "/")
}

func normalizedDumpLines(_ dump: String?) -> [String] {
    guard let dump else { return [] }
    return dump
        .split(separator: "\n", omittingEmptySubsequences: true)
        .map { normalizeDumpLine(String($0)) }
        .filter { !$0.isEmpty }
}

func normalizeDumpLine(_ raw: String) -> String {
    let trimmed = raw.trimmingCharacters(in: .whitespaces)
    guard !trimmed.isEmpty else { return "" }

    let withoutTokenText: Substring
    if let quoteIndex = trimmed.firstIndex(of: "\"") {
        withoutTokenText = trimmed[..<quoteIndex]
    } else {
        withoutTokenText = Substring(trimmed)
    }

    var result = ""
    var index = withoutTokenText.startIndex
    while index < withoutTokenText.endIndex {
        let character = withoutTokenText[index]
        if character == "(" {
            result += "()"
            index = withoutTokenText.index(after: index)
            var depth = 1
            while index < withoutTokenText.endIndex && depth > 0 {
                if withoutTokenText[index] == "(" {
                    depth += 1
                } else if withoutTokenText[index] == ")" {
                    depth -= 1
                }
                index = withoutTokenText.index(after: index)
            }
        } else {
            result.append(character)
            index = withoutTokenText.index(after: index)
        }
    }

    return result.trimmingCharacters(in: .whitespaces)
}

func firstUsefulLine(_ text: String?) -> String {
    guard let text else { return "<none>" }
    for line in text.split(separator: "\n", omittingEmptySubsequences: true) {
        let trimmed = line.trimmingCharacters(in: .whitespaces)
        if !trimmed.isEmpty {
            return abbreviate(trimmed, maxLength: 160)
        }
    }
    return "<none>"
}

func abbreviate(_ text: String, maxLength: Int) -> String {
    guard text.count > maxLength else { return text }
    let end = text.index(text.startIndex, offsetBy: maxLength)
    return String(text[..<end])
}

func stableHash(_ string: String) -> String {
    var hash: UInt64 = 0xcbf29ce484222325
    for byte in string.utf8 {
        hash ^= UInt64(byte)
        hash &*= 0x100000001b3
    }
    return String(format: "%016llx", hash)
}

func sourceRequiresDisabledExperimentalFeature(_ source: String) -> Bool {
    if source.contains("dependsOn(") { return true }
    if source.contains("InlineArray<") { return true }
    if source.contains("borrow {") || source.contains("mutate {") { return true }
    if source.contains("_borrow") || source.contains("_move") { return true }
    if source.contains("_mutating") || source.contains("_borrowing") || source.contains("_consuming") {
        return true
    }
    return source.split(whereSeparator: \.isNewline).contains { line in
        let trimmed = line.drop(while: { $0.isWhitespace })
        return trimmed == "using" || trimmed.hasPrefix("using ")
    }
}

func countsLine(_ counts: [String: Int]) -> String {
    counts.sorted { $0.key < $1.key }
        .map { "\($0.key)=\($0.value)" }
        .joined(separator: " ")
}

func printHelp() {
    print("""
    Usage: advent-fuzz-runner [options]

    Options:
      --iterations N       Number of generated inputs to probe (default: 1000)
      --timeout SECONDS    Per-input probe timeout (default: 10)
      --seed N             Deterministic fuzzer seed, decimal or 0x... (default: 0xA0C2021)
      --probe PATH         Probe executable (default: SwiftSyntaxFuzzer/.build/advent-fuzz-probe)
      --grammar PATH       Swift.apus path (default: grammars/Swift.apus)
      --output PATH        Run output directory (default: SwiftSyntaxFuzzer/runs)
      --seed-corpus PATH   Labeled seed corpus (default: SwiftSyntaxFuzzer/seeds/known-problems.txt)
      --wide-corpus PATHS  Comma-separated real-code seed files for the wide lanes (default: seeds/swift-syntax-corpus.txt,seeds/real-source.txt; "" disables)
      --wide-percent N     Share of inputs from the wide lanes (default: 50)
      --frontier-percent N Share of inputs from recent high-signal frontier lanes (default: 20)
      --interesting-corpus PATHS
                           Comma-separated interesting.jsonl files to feed back as a coverage corpus
      --interesting-percent N
                           Share of inputs from the interesting corpus when provided (default: 15)
      --heartbeat-every N  Write heartbeat/state every N inputs (default: 25)
      --max-artifacts N    Stop writing new artifact files after N unique artifacts (default: 10000)
      --max-artifact-mb N  Stop writing new artifact files after N MB (default: 1024)
      --artifact-statuses LIST
                           Comma-separated statuses to persist as full artifacts; counts/events still include all statuses
      --all-artifacts      Persist full artifacts for every non-same status
      --max-artifacts-per-status N
                           Stop writing new artifact files after N unique artifacts for any single status
      --dedupe-by-signal   Dedupe artifact writes by failure-shape signal instead of exact source hash
      --reduce-artifacts N Try up to N probe calls to shrink each newly-written reducible artifact
      --interesting-passes Retain passing inputs that add cheap novelty (default)
      --no-interesting-passes
                           Disable interesting passing-input retention
      --max-interesting-passes N
                           Cap interesting passing inputs written to interesting.jsonl (default: 2000)
      --quiet-passes       Only write non-same events to events.jsonl
      --persistent-probe   Reuse one probe process and cached grammar (default)
      --isolated-probe     Launch a fresh probe process per input
    """)
}
