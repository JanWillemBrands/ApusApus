import Foundation

/// Small, feedback-guided source generator that walks the grammar graph produced by `ApusParser`.
/// It intentionally keeps no derivation corpus: feedback is only an in-memory hit count per
/// alternate, and every generated sample is rendered directly to source text.
final class GrammarDirectedGenerator {
    private let grammar: Grammar
    private var emittedAlternateHits: [Int: Int] = [:]
    private var acceptedAlternateHits: [Int: Int] = [:]
    private var acceptedAlternativePairs = Set<AlternativePair>()
    private let maximumNodes: Int
    private let maximumSearchSteps: Int
    private let reachableAlternativeCount: Int
    private var attemptedAlternatives = Set<Int>()
    private var emittedAlternatives = Set<Int>()
    private var generatedSamples = 0
    private var generationAttempts = 0
    private var fallbackSamples = 0
    private var emittedNodeTotal = 0
    private var minimumEmittedNodes = Int.max
    private var maximumEmittedNodes = 0
    private var nodeBudgetExhaustions = 0
    private var recursionCutoffs = 0
    private var searchBudgetExhaustions = 0
    private var searchStepsRemaining = 0

    init(grammarURL: URL, maximumNodes: Int = 240, maximumSearchSteps: Int = 20_000) throws {
        grammar = try ApusParser(fromFile: grammarURL).parse()
        self.maximumNodes = maximumNodes
        self.maximumSearchSteps = maximumSearchSteps
        reachableAlternativeCount = Self.countReachableAlternatives(from: grammar.root)
    }

    func next(using rng: inout SplitMix64) -> GeneratedSource {
        for _ in 0..<24 {
            generationAttempts += 1
            searchStepsRemaining = maximumSearchSteps
            var state = GenerationState(nodesRemaining: maximumNodes)
            if expand(grammar.root, state: &state, rng: &rng), !state.source.isEmpty {
                generatedSamples += 1
                let emittedNodes = maximumNodes - state.nodesRemaining
                emittedNodeTotal += emittedNodes
                minimumEmittedNodes = min(minimumEmittedNodes, emittedNodes)
                maximumEmittedNodes = max(maximumEmittedNodes, emittedNodes)
                emittedAlternatives.formUnion(state.chosenAlternatives)
                for alternate in Set(state.chosenAlternatives) {
                    emittedAlternateHits[alternate, default: 0] += 1
                }
                return GeneratedSource(
                    label: "grammar-directed:nodes=\(emittedNodes)",
                    source: state.source,
                    grammarAlternatives: state.chosenAlternatives
                )
            }
        }
        fallbackSamples += 1
        return GeneratedSource(label: "grammar-directed:fallback", source: "let fuzzValue = 0")
    }

    func observeAccepted(_ generated: GeneratedSource) {
        let alternatives = Set(generated.grammarAlternatives)
        for alternate in alternatives {
            acceptedAlternateHits[alternate, default: 0] += 1
        }
        let sorted = alternatives.sorted()
        for firstIndex in sorted.indices {
            for second in sorted[sorted.index(after: firstIndex)...] {
                acceptedAlternativePairs.insert(AlternativePair(sorted[firstIndex], second))
            }
        }
    }

    func statisticsLines() -> [String] {
        let coverage = reachableAlternativeCount == 0
            ? 0
            : 100 * Double(emittedAlternatives.count) / Double(reachableAlternativeCount)
        let attemptedCoverage = reachableAlternativeCount == 0
            ? 0
            : 100 * Double(attemptedAlternatives.count) / Double(reachableAlternativeCount)
        let averageNodes = generatedSamples == 0 ? 0 : Double(emittedNodeTotal) / Double(generatedSamples)
        let minimumNodes = generatedSamples == 0 ? 0 : minimumEmittedNodes
        return [
            "grammar-reachable-alternatives: \(reachableAlternativeCount)",
            "grammar-attempted-alternatives: \(attemptedAlternatives.count) (\(String(format: "%.2f", attemptedCoverage))%)",
            "grammar-emitted-alternatives: \(emittedAlternatives.count) (\(String(format: "%.2f", coverage))%)",
            "grammar-compiler-accepted-alternatives: \(acceptedAlternateHits.count)",
            "grammar-compiler-accepted-alternative-pairs: \(acceptedAlternativePairs.count)",
            "grammar-generated-samples: \(generatedSamples)",
            "grammar-generation-attempts: \(generationAttempts)",
            "grammar-fallback-samples: \(fallbackSamples)",
            "grammar-emitted-nodes: min=\(minimumNodes) average=\(String(format: "%.1f", averageNodes)) max=\(maximumEmittedNodes)",
            "grammar-node-budget-exhaustions: \(nodeBudgetExhaustions)",
            "grammar-recursion-cutoffs: \(recursionCutoffs)",
            "grammar-search-budget-exhaustions: \(searchBudgetExhaustions)",
        ]
    }

    private struct AlternativePair: Hashable {
        let first: Int
        let second: Int

        init(_ first: Int, _ second: Int) {
            self.first = first
            self.second = second
        }
    }

    private struct GenerationState {
        var source = ""
        var nodesRemaining: Int
        var activeNonterminals: [ObjectIdentifier: Int] = [:]
        var chosenAlternatives: [Int] = []
        var joinNextToken = false

        mutating func append(_ text: String) {
            guard !text.isEmpty else { return }
            if !joinNextToken,
               let last = source.unicodeScalars.last, let first = text.unicodeScalars.first,
               Self.wordLike(last), Self.wordLike(first) {
                source.append(" ")
            }
            joinNextToken = false
            source.append(text)
        }

        private static func wordLike(_ scalar: Unicode.Scalar) -> Bool {
            scalar == "_" || scalar == "$" || CharacterSet.alphanumerics.contains(scalar)
        }
    }

    private func expand(
        _ node: GrammarNode,
        state: inout GenerationState,
        rng: inout SplitMix64
    ) -> Bool {
        guard searchStepsRemaining > 0 else {
            searchBudgetExhaustions += 1
            return false
        }
        searchStepsRemaining -= 1
        guard state.nodesRemaining > 0 else {
            nodeBudgetExhaustions += 1
            return false
        }
        state.nodesRemaining -= 1

        switch node.kind {
        case .EOS, .EPS, .END:
            return true
        case .T, .TI, .C:
            state.append(sampleTerminal(named: node.name, using: &rng))
            return true
        case .B:
            appendBoundary(node.name, to: &state)
            return true
        case .ALT:
            return expandSequence(node, state: &state, rng: &rng)
        case .N:
            let definition = node.isLHS ? node : (node.alt ?? grammar.nonTerminals[node.name])
            guard let definition else { return false }
            let identity = ObjectIdentifier(definition)
            let active = state.activeNonterminals[identity, default: 0]
            guard active < 3 else {
                recursionCutoffs += 1
                return definition.isNullable
            }
            state.activeNonterminals[identity] = active + 1
            defer {
                if active == 0 { state.activeNonterminals.removeValue(forKey: identity) }
                else { state.activeNonterminals[identity] = active }
            }
            return expandAlternatives(of: definition, state: &state, rng: &rng)
        case .DO:
            return expandAlternatives(of: node, state: &state, rng: &rng)
        case .OPT:
            if rng.nextInt(upperBound: 100) < 38 { return true }
            return expandAlternatives(of: node, state: &state, rng: &rng)
        case .KLN:
            let repetitions = rng.nextInt(upperBound: 4)
            for _ in 0..<repetitions {
                guard expandAlternatives(of: node, state: &state, rng: &rng) else { return false }
            }
            return true
        case .POS:
            let repetitions = 1 + rng.nextInt(upperBound: 3)
            for _ in 0..<repetitions {
                guard expandAlternatives(of: node, state: &state, rng: &rng) else { return false }
            }
            return true
        }
    }

    private func expandSequence(
        _ alternate: GrammarNode,
        state: inout GenerationState,
        rng: inout SplitMix64
    ) -> Bool {
        for symbol in alternate.bodySymbols {
            guard expand(symbol, state: &state, rng: &rng) else { return false }
        }
        return true
    }

    private func expandAlternatives(
        of node: GrammarNode,
        state: inout GenerationState,
        rng: inout SplitMix64
    ) -> Bool {
        var alternatives: [GrammarNode] = []
        var alternate = node.alt
        while let current = alternate {
            alternatives.append(current)
            alternate = current.alt
        }
        guard !alternatives.isEmpty else { return node.isNullable }

        // Recover from a failed descendant by trying siblings, but charge all work to a global
        // per-root-attempt search budget. Candidate derivation state rolls back; search work does
        // not, preventing the exponential unbounded search of the first implementation.
        var remaining = alternatives
        while !remaining.isEmpty, searchStepsRemaining > 0 {
            let chosen = chooseInverseHit(from: remaining, using: &rng)
            remaining.removeAll { $0 === chosen }
            attemptedAlternatives.insert(chosen.number)
            var candidate = state
            if expand(chosen, state: &candidate, rng: &rng) {
                candidate.chosenAlternatives.append(chosen.number)
                state = candidate
                return true
            }
        }
        return false
    }

    private func chooseInverseHit(from alternatives: [GrammarNode], using rng: inout SplitMix64) -> GrammarNode {
        let weights = alternatives.map { max(1, 32 / (emittedAlternateHits[$0.number, default: 0] + 1)) }
        var ticket = rng.nextInt(upperBound: weights.reduce(0, +))
        for (index, weight) in weights.enumerated() {
            if ticket < weight { return alternatives[index] }
            ticket -= weight
        }
        return alternatives[alternatives.count - 1]
    }

    private static func countReachableAlternatives(from root: GrammarNode) -> Int {
        var visited = Set<ObjectIdentifier>()
        var alternatives = Set<ObjectIdentifier>()
        var stack = [root]
        while let node = stack.popLast() {
            let identity = ObjectIdentifier(node)
            guard visited.insert(identity).inserted else { continue }
            if node.kind == .ALT { alternatives.insert(identity) }
            if let alternate = node.alt { stack.append(alternate) }
            stack.append(contentsOf: node.bodySymbols)
        }
        return alternatives.count
    }

    private func appendBoundary(_ name: String, to state: inout GenerationState) {
        switch name {
        case "<n>":
            if !state.source.hasSuffix("\n") { state.source.append("\n") }
        case "<s>":
            if let last = state.source.last, !last.isWhitespace { state.source.append(" ") }
        case ">s<":
            while state.source.last?.isWhitespace == true { state.source.removeLast() }
            state.joinNextToken = true
        case ">n<":
            if state.source.hasSuffix("\n") {
                while state.source.last?.isWhitespace == true { state.source.removeLast() }
                state.source.append(" ")
            }
        default:
            break
        }
    }

    private func sampleTerminal(named name: String, using rng: inout SplitMix64) -> String {
        guard let pattern = grammar.terminals[name] else { return name }
        if pattern.isLiteral { return pattern.source }

        let lower = name.lowercased()
        if lower.contains("identifier") || lower.contains("name") { return ["x", "value", "T", "async"].random(using: &rng) }
        if lower.contains("string") { return ["\"x\"", #""\(x)""#, "#\"x\"#"].random(using: &rng) }
        if lower.contains("regex") || lower.contains("regularexpression") { return ["/x/", "#/x/#"].random(using: &rng) }
        if lower.contains("floating") { return ["0.0", "1e2", "0x1p0"].random(using: &rng) }
        if lower.contains("integer") || lower.contains("digit") || lower.contains("number") { return ["0", "1", "42"].random(using: &rng) }
        if lower.contains("operator") { return ["+", "-", "==", "??"].random(using: &rng) }
        if lower.contains("comment") { return "/*c*/" }
        if lower.contains("whitespace") { return " " }
        if lower.contains("character") { return "x" }
        return "x"
    }
}


/// Generates compiler-accepted anchors from Swift.apus, then probes the immediate rejection
/// boundary with exactly one local edit. Anchors are not retained after their mutations are queued.
final class BoundaryRecoveryGenerator {
    private let grammarGenerator: GrammarDirectedGenerator
    private var pending: [GeneratedSource] = []
    private var anchorsProbed = 0
    private var anchorsAccepted = 0
    private var mutationsProbed = 0
    private var compilerRejectedMutations = 0
    private var apusOveraccepts = 0
    private var swiftSyntaxRecoveryOveraccepts = 0

    init(_ grammarGenerator: GrammarDirectedGenerator) {
        self.grammarGenerator = grammarGenerator
    }

    func next(using rng: inout SplitMix64) -> GeneratedSource {
        if !pending.isEmpty {
            mutationsProbed += 1
            return pending.removeLast()
        }
        while true {
            let anchor = grammarGenerator.next(using: &rng)
            guard FuzzTokens(anchor.source).tokens.count >= 3 else { continue }
            anchorsProbed += 1
            return GeneratedSource(
                label: "boundary:anchor:\(anchor.label)",
                source: anchor.source,
                grammarAlternatives: anchor.grammarAlternatives
            )
        }
    }

    func observe(_ generated: GeneratedSource, probe: ProbeOutput?) {
        guard let probe else { return }
        if generated.label.hasPrefix("boundary:anchor:") {
            guard probe.compilerAccepted == true, probe.adventBuiltTree else { return }
            anchorsAccepted += 1
            grammarGenerator.observeAccepted(generated)
            pending = mutations(of: generated.source)
            return
        }
        guard generated.label.hasPrefix("boundary:mutation:"),
              probe.compilerAccepted == false else { return }
        compilerRejectedMutations += 1
        guard probe.adventBuiltTree else { return }
        apusOveraccepts += 1
        if !probe.swiftSyntaxHasError {
            swiftSyntaxRecoveryOveraccepts += 1
        }
    }

    func statisticsLines() -> [String] {
        [
            "boundary-anchors-probed: \(anchorsProbed)",
            "boundary-anchors-accepted: \(anchorsAccepted)",
            "boundary-mutations-probed: \(mutationsProbed)",
            "boundary-compiler-rejections: \(compilerRejectedMutations)",
            "boundary-apus-overaccepts: \(apusOveraccepts)",
            "boundary-swiftsyntax-recovery-overaccepts: \(swiftSyntaxRecoveryOveraccepts)",
        ]
    }

    private func mutations(of source: String) -> [GeneratedSource] {
        let original = FuzzTokens(source)
        let count = original.tokens.count
        guard count >= 3 else { return [] }

        // Deletion is the strongest recovery probe, so exercise it at every selected site. Pair it
        // with one different boundary edit; each emitted source still contains exactly one edit.
        let siteCount = min(8, count)
        let sites = (0..<siteCount).map { min(count - 1, $0 * count / siteCount) }
        var results: [GeneratedSource] = []
        var seen = Set<String>()

        func append(_ stream: FuzzTokens, name: String, index: Int) {
            let mutated = stream.rendered
            guard mutated != source, seen.insert(mutated).inserted else { return }
            results.append(GeneratedSource(
                label: "boundary:mutation:\(name):token=\(index)/\(count)",
                source: mutated
            ))
        }

        for index in sites {
            var deleted = original
            let leading = deleted.tokens[index].leading
            deleted.tokens.remove(at: index)
            if index < deleted.tokens.count, deleted.tokens[index].leading.isEmpty {
                deleted.tokens[index].leading = leading
            }
            append(deleted, name: "delete", index: index)

            var secondary = original
            if secondary.tokens[index].kind == .word {
                secondary.tokens[index].text = "x"
                append(secondary, name: "replace-name", index: index)
            } else if index == count - 1 || secondary.tokens[index].text == ")" ||
                        secondary.tokens[index].text == "]" || secondary.tokens[index].text == "}" {
                secondary.tokens = Array(secondary.tokens.prefix(index))
                secondary.trailing = ""
                append(secondary, name: "truncate", index: index)
            } else {
                secondary.tokens[index].leading =
                    secondary.tokens[index].leading.contains("\n") ? " " : "\n"
                append(secondary, name: "toggle-newline", index: index)
            }
        }
        return results.reversed()
    }
}
