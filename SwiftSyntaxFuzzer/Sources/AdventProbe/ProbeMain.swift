import Darwin
import Foundation
@_spi(ExperimentalLanguageFeatures) import SwiftSyntax
@_spi(ExperimentalLanguageFeatures) import SwiftParser

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
    let compilerTypecheckChecked: Bool
    let compilerTypecheckAccepted: Bool?
    let compilerTypecheckStderr: String?
    let residualAmbiguities: [String]
    let grammarCoverage: [String]
    /// Where the parse got stuck, for grouping rejects by CAUSE without reducing each file:
    /// the furthest input offset any descriptor reached, the source around it, and what the
    /// grammar expected there. Only meaningful when Advent built no tree.
    let failureOffset: Int?
    let failureLine: Int?
    let failureContext: String?
    let failureExpected: [String]
    let generatorDiagnostics: [String]
    let referenceDump: String?
    let adventDump: String?
    let metrics: Metrics?
    let error: String?
}

private struct ProbeRequest: Codable {
    let source: String
    let includeDumps: Bool?
    /// Compatibility with older runners. Compiler-first classification ignores this; reducers must
    /// preserve the compiler parse result.
    let skipCompiler: Bool?
}

@main
struct AdventProbe {
    static func main() {
        do {
            let arguments = try Arguments.parse(CommandLine.arguments.dropFirst())
            if arguments.serverMode {
                try runServer(arguments: arguments)
                exit(0)
            }

            let sourceData = FileHandle.standardInput.readDataToEndOfFile()
            guard let source = String(data: sourceData, encoding: .utf8) else {
                try write(ProbeOutput(
                    status: "invalid-utf8",
                    swiftSyntaxHasError: true,
                    adventMatched: false,
                    adventBuiltTree: false,
                    adventGeneratedSwiftSyntax: false,
                    compilerChecked: false,
                    compilerAccepted: nil,
                    compilerStderr: nil,
                    compilerTypecheckChecked: false,
                    compilerTypecheckAccepted: nil,
                    compilerTypecheckStderr: nil,
                    residualAmbiguities: [],
                    grammarCoverage: [],
                    failureOffset: nil, failureLine: nil, failureContext: nil, failureExpected: [],
                    generatorDiagnostics: [],
                    referenceDump: nil,
                    adventDump: nil,
                    metrics: nil,
                    error: "stdin was not valid UTF-8"
                ))
                exit(2)
            }

            let grammar = try loadGrammar(from: arguments.grammarURL)
            let output = try run(source: source, grammar: grammar, includeDumps: arguments.includeDumps)
            try write(output)
            exit(output.status == "same" ? 0 : 1)
        } catch {
            let output = ProbeOutput(
                status: "probe-error",
                swiftSyntaxHasError: true,
                adventMatched: false,
                adventBuiltTree: false,
                adventGeneratedSwiftSyntax: false,
                compilerChecked: false,
                compilerAccepted: nil,
                compilerStderr: nil,
                compilerTypecheckChecked: false,
                compilerTypecheckAccepted: nil,
                compilerTypecheckStderr: nil,
                residualAmbiguities: [],
                grammarCoverage: [],
                failureOffset: nil, failureLine: nil, failureContext: nil, failureExpected: [],
                generatorDiagnostics: [],
                referenceDump: nil,
                adventDump: nil,
                metrics: nil,
                error: String(describing: error)
            )
            try? write(output)
            exit(2)
        }
    }

    private static func runServer(arguments: Arguments) throws {
        let grammar = try loadGrammar(from: arguments.grammarURL)
        let decoder = JSONDecoder()

        while let line = readLine() {
            do {
                guard let data = line.data(using: .utf8) else {
                    try write(errorOutput(status: "invalid-utf8", error: "request line was not valid UTF-8"))
                    continue
                }
                let request = try decoder.decode(ProbeRequest.self, from: data)
                let output = try run(
                    source: request.source,
                    grammar: grammar,
                    includeDumps: request.includeDumps ?? arguments.includeDumps,
                    skipCompiler: request.skipCompiler ?? false
                )
                try write(output)
            } catch {
                try write(errorOutput(status: "probe-error", error: String(describing: error)))
            }
        }
    }

    private static func loadGrammar(from grammarURL: URL) throws -> Grammar {
        let grammarParser = try ApusParser(fromFile: grammarURL)
        return try grammarParser.parse(explicitStartSymbol: "")
    }

    private static func run(source: String, grammar: Grammar, includeDumps: Bool, skipCompiler: Bool = false) throws -> ProbeOutput {
        parseReports = false

        let referenceFeatures = swiftSyntaxExperimentalFeatures(for: source)
        let reference: SourceFileSyntax
        if referenceFeatures.isEmpty {
            reference = Parser.parse(source: source)
        } else {
            var contiguousSource = source
            contiguousSource.makeContiguousUTF8()
            reference = contiguousSource.withUTF8 { buffer in
                Parser.parse(source: buffer, experimentalFeatures: referenceFeatures)
            }
        }
        let referenceHasError = Syntax(reference).hasError
        let referenceDump = renderSwiftSyntaxNode(Syntax(reference), indent: 0)

        let parser = MessageParser(grammar: grammar)

        let start = Date()
        parser.parse(input: source)
        let parseSeconds = Date().timeIntervalSince(start)

        let origin = source.startIndex
        let extent = source.endIndex
        let matched = parser.yield(of: parser.currentParseRoot).contains { y in
            guard y.i == origin else { return false }
            if y.j == extent { return true }
            return !parser.lexer.lex(at: y.j, terminalID: grammar.eosID).isEmpty
        }

        var oraclePruned = 0
        var builtTree = false
        var generatedTree = false
        var ambiguityDiagnostics: [String] = []
        var grammarCoverage: [String] = []
        var generatorDiagnostics: [String] = []
        var adventDump: String? = nil

        if matched {
            oraclePruned = Oracle(parser: parser, input: source).disambiguate()
            let builder = DerivationBuilder(parser: parser, input: source)
            if builder.buildAST() != nil {
                builtTree = true
            }
            ambiguityDiagnostics = builder.diagnostics.map(\.fingerprint)
            grammarCoverage = builder.coverage

            var generator = SwiftSyntaxGenerator(parser: parser, input: source)
            if let tree = generator.generate() {
                generatedTree = true
                adventDump = renderSwiftSyntaxNode(Syntax(tree), indent: 0)
            }
            generatorDiagnostics = generator.diagnostics.map(\.description)
        }

        // Match the AdventTests acceptance criterion: a raw root yield is only a candidate.
        // Oracle pruning and DerivationBuilder must still leave a complete tree before Advent
        // counts as accepting the input. Keep `adventMatched` in the output as raw telemetry.
        let adventAccepted = builtTree

        // Failure site for reject clustering (crawl triage). `furthestMismatchIndex` is the
        // furthest position any descriptor reached; the grammar slot there says what it wanted.
        // The context is the source around it with newlines escaped, so a cluster key is one line.
        var failureSite: (offset: Int, line: Int, context: String, expected: [String])? = nil
        if !adventAccepted {
            let index = parser.furthestMismatchIndex
            let offset = source.distance(from: source.startIndex, to: index)
            let line = source[source.startIndex..<index].reduce(1) { $1.isNewline ? $0 + 1 : $0 }
            let from = source.index(index, offsetBy: -30, limitedBy: source.startIndex) ?? source.startIndex
            let to = source.index(index, offsetBy: 30, limitedBy: source.endIndex) ?? source.endIndex
            let context = source[from..<index] + "<HERE>" + source[index..<to]
            failureSite = (offset, line,
                           context.replacingOccurrences(of: "\n", with: "⏎"),
                           parser.furthestMismatchExpected.sorted())
        }

        let compilerResult = runCompilerParse(source: source)
        let compilerTypecheckResult: CompilerResult? = nil
        let swiftSyntaxAccepted = !referenceHasError
        let referencesAgree = compilerResult.accepted == swiftSyntaxAccepted
        let status: String
        if !referencesAgree {
            status = "reference-disagreement"
        } else if compilerResult.accepted {
            if !adventAccepted {
                status = "advent-underaccept"
            } else if !ambiguityDiagnostics.isEmpty {
                status = "residual-ambiguity"
            } else if adventAccepted, adventDump == nil {
                status = "advent-no-generated-tree"
            } else if !referenceHasError, let adventDump, adventDump != referenceDump {
                status = "tree-difference"
            } else {
                status = "same"
            }
        } else {
            status = adventAccepted ? "advent-overaccept" : "same"
        }

        let metrics = ProbeOutput.Metrics(
            sourceLength: source.count,
            tokenCount: parser.commitsByStart.count,
            descriptorCount: parser.descriptorCount,
            duplicateDescriptorCount: parser.duplicateDescriptorCount,
            suppressedDescriptorCount: parser.suppressedDescriptorCount,
            crfCount: parser.crf.count,
            yieldCount: parser.yieldCount,
            oraclePruned: oraclePruned,
            parseSeconds: parseSeconds
        )

        return ProbeOutput(
            status: status,
            swiftSyntaxHasError: referenceHasError,
            adventMatched: matched,
            adventBuiltTree: builtTree,
            adventGeneratedSwiftSyntax: generatedTree,
            compilerChecked: true,
            compilerAccepted: compilerResult.accepted,
            compilerStderr: compilerResult.stderr.isEmpty == false ? compilerResult.stderr : nil,
            compilerTypecheckChecked: false,
            compilerTypecheckAccepted: compilerTypecheckResult?.accepted,
            compilerTypecheckStderr: compilerTypecheckResult?.stderr.isEmpty == false ? compilerTypecheckResult?.stderr : nil,
            residualAmbiguities: ambiguityDiagnostics,
            grammarCoverage: grammarCoverage,
            failureOffset: failureSite?.offset,
            failureLine: failureSite?.line,
            failureContext: failureSite?.context,
            failureExpected: failureSite?.expected ?? [],
            generatorDiagnostics: generatorDiagnostics,
            referenceDump: includeDumps || status != "same" ? referenceDump : nil,
            adventDump: includeDumps || status != "same" ? adventDump : nil,
            metrics: metrics,
            error: nil
        )
    }

    private static func swiftSyntaxExperimentalFeatures(for source: String) -> Parser.ExperimentalFeatures {
        var features: Parser.ExperimentalFeatures = []

        if source.contains("read {") || source.contains("modify {") {
            features.insert(.coroutineAccessors)
        }
        if source.contains("borrow {") || source.contains("mutate {") {
            features.insert(.borrowAndMutateAccessors)
        }

        return features
    }

    private struct CompilerResult {
        let accepted: Bool
        let stderr: String
    }

    private static func runCompilerParse(source: String) -> CompilerResult {
        runCompiler(source: source, arguments: ["swiftc", "-swift-version", "6", "-parse"], description: "compiler parse")
    }

    private static func runCompilerTypecheck(source: String) -> CompilerResult {
        let prelude = """
        protocol P {}
        protocol Q {}
        struct Foo { struct Bar {} }
        struct Bar {}
        struct Baz {}
        func placeholder<T>() -> T { fatalError() }
        func f<T>(_ value: T) -> T { value }
        func f<T>(_ value: T, g: () -> Int) -> T { value }
        let a = 1
        let b = 2
        let c = 3
        let d = 4
        let e = 5
        let s = "abc"
        let x: Foo? = nil
        let y: Foo? = nil
        let value: Optional<Int> = nil
        let items = [1, 2, 3]
        let children: [Foo] = []

        """
        return runCompiler(source: prelude + source, arguments: ["swiftc", "-swift-version", "6", "-typecheck"], description: "compiler typecheck")
    }

    private static func runCompiler(source: String, arguments: [String], description: String) -> CompilerResult {
        let fileManager = FileManager.default
        let tempURL = URL(fileURLWithPath: NSTemporaryDirectory())
            .appendingPathComponent("advent-fuzzer-\(UUID().uuidString).swift")
        do {
            try source.write(to: tempURL, atomically: true, encoding: .utf8)
            defer { try? fileManager.removeItem(at: tempURL) }

            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/usr/bin/xcrun")
            process.arguments = arguments + [tempURL.path]
            process.environment = ["OS_ACTIVITY_MODE": "disable"]
            let stderrPipe = Pipe()
            process.standardOutput = Pipe()
            process.standardError = stderrPipe
            try process.run()
            process.waitUntilExit()
            let stderr = String(data: stderrPipe.fileHandleForReading.readDataToEndOfFile(), encoding: .utf8) ?? ""
            return CompilerResult(accepted: process.terminationStatus == 0, stderr: stderr)
        } catch {
            return CompilerResult(accepted: false, stderr: "\(description) probe failed: \(error)")
        }
    }

    private static func renderSwiftSyntaxNode(_ node: Syntax, indent: Int) -> String {
        let pad = String(repeating: "  ", count: indent)
        var result = ""

        if let token = node.as(TokenSyntax.self) {
            let text = token.text
            if !text.isEmpty {
                result += "\(pad)\(token.tokenKind) \"\(text)\"\n"
            }
        } else {
            let typeName = "\(node.syntaxNodeType)".replacingOccurrences(of: "Syntax", with: "")
            result += "\(pad)\(typeName)\n"
            for child in node.children(viewMode: .sourceAccurate) {
                result += renderSwiftSyntaxNode(child, indent: indent + 1)
            }
        }

        return result
    }

    private static func write(_ output: ProbeOutput) throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.sortedKeys]
        let data = try encoder.encode(output)
        FileHandle.standardOutput.write(data)
        FileHandle.standardOutput.write(Data("\n".utf8))
    }

    private static func errorOutput(status: String, error: String) -> ProbeOutput {
        ProbeOutput(
            status: status,
            swiftSyntaxHasError: true,
            adventMatched: false,
            adventBuiltTree: false,
            adventGeneratedSwiftSyntax: false,
            compilerChecked: false,
            compilerAccepted: nil,
            compilerStderr: nil,
            compilerTypecheckChecked: false,
            compilerTypecheckAccepted: nil,
            compilerTypecheckStderr: nil,
            residualAmbiguities: [],
            grammarCoverage: [],
            failureOffset: nil, failureLine: nil, failureContext: nil, failureExpected: [],
            generatorDiagnostics: [],
            referenceDump: nil,
            adventDump: nil,
            metrics: nil,
            error: error
        )
    }
}

private struct Arguments {
    let grammarURL: URL
    let includeDumps: Bool
    let serverMode: Bool

    static func parse(_ raw: ArraySlice<String>) throws -> Arguments {
        var grammarPath: String?
        var includeDumps = false
        var serverMode = false
        var iterator = raw.makeIterator()

        while let arg = iterator.next() {
            switch arg {
            case "--grammar":
                grammarPath = iterator.next()
            case "--include-dumps":
                includeDumps = true
            case "--server":
                serverMode = true
            default:
                throw ProbeArgumentError("unknown argument: \(arg)")
            }
        }

        guard let grammarPath else {
            throw ProbeArgumentError("missing --grammar <path>")
        }

        return Arguments(
            grammarURL: URL(fileURLWithPath: grammarPath),
            includeDumps: includeDumps,
            serverMode: serverMode
        )
    }
}

private struct ProbeArgumentError: Error, CustomStringConvertible {
    let description: String
    init(_ description: String) { self.description = description }
}
