//
//  DerivationBuilder.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.03.22.
//
//  Rebuilds a single concrete parse tree from the BSR yields left on the GrammarNodes, and
//  reports the spans it could not resolve to one alternate as `diagnostics`. That diagnostic
//  set is the ambiguity oracle the test suites assert on (`AdventParseResult.isUnambiguous`)
//  and what the APUS_SIG_DUMP harvester clusters into signatures.
//
//  Until 2026-09-15 this also held a Graphviz renderer and a separate all-derivations walk
//  that only the renderer used; both went with the diagrams. tinyGLL's explorer is the
//  interactive replacement.

import Foundation
import OSLog

// MARK: - Parse Tree Node

class ParseTreeNode: CustomStringConvertible {
    let name: String
    /// Source slice covered by this node when it's a leaf (terminal or
    /// boundary). `nil` for non-terminal interior nodes — those are described
    /// by their children. Replaces the old `token: Token?` field that
    /// indirected through the scanner-produced token array.
    let image: Substring?
    let from: CharPosition
    let to: CharPosition
    var children: [ParseTreeNode] = []
    var isAmbiguous = false
    var isMissing = false
    var isTerminal: Bool { image != nil }

    init(_ name: String, from: CharPosition, to: CharPosition, image: Substring? = nil) {
        self.name = name
        self.image = image
        self.from = from
        self.to = to
    }

    var description: String {
        if let image { return "\(name)(\"\(image)\")" }
        if isMissing { return "\(name) <missing>" }
        return "\(name)[\(children.count)]"
    }

    func dump(indent: Int = 0) -> String {
        let pad = String(repeating: "  ", count: indent)
        if isMissing { return "\(pad)\(name) <missing>\n" }
        if let image {
            if image.isEmpty { return "\(pad)\(name)\n" }
            return "\(pad)\(name) \"\(image)\"\n"
        }
        var result = "\(pad)\(name)\n"
        for child in children {
            result += child.dump(indent: indent + 1)
        }
        return result
    }
}

// MARK: - Derivation Builder

/// Builds concrete parse trees from BSR yield evidence on GrammarNodes.
/// EBNF brackets are transparent — their contents are inlined as direct children.
class DerivationBuilder {
    let parser: MessageParser
    let grammar: Grammar
    let input: String

    private var expanding = Set<NodeSpan>()
    private var endCache = [NodePos: Set<CharPosition>]()
    private var endGuard = Set<NodePos>()

    private struct NodeSpan: Hashable { let id: ObjectIdentifier; let from, to: CharPosition }
    private struct NodePos: Hashable  { let id: ObjectIdentifier; let from: CharPosition }

    init(parser: MessageParser, input: String) {
        self.parser = parser
        self.grammar = parser.grammar
        self.input = input
    }

    // MARK: - Single Deterministic AST

    struct Diagnostic: CustomStringConvertible {
        let message: String
        let node: String
        let from: CharPosition
        let to: CharPosition
        let candidateCount: Int
        /// Canonical, position-independent fingerprint of the competing alternates
        /// (or the pivot body). Used by the ambiguity-harvest workflow to cluster
        /// the many failing tests into a small set of distinct root-cause signatures.
        let signature: String

        var description: String {
            let subject = node.isEmpty ? signature : node
            return "\(subject) [\(from)..\(to)]: \(message) (\(candidateCount) candidates)"
        }
        /// `node ⟪message⟫ signature` — stable across source positions.
        var fingerprint: String { "\(node)\t\(message)\t\(signature)" }
    }

    private(set) var diagnostics: [Diagnostic] = []

    func buildAST() -> ParseTreeNode? {
        diagnostics = []
        let n = input.endIndex
        let origin = input.startIndex
        // A yield ending at `y.j` also counts when only trivia separates `y.j` from
        // input end — EOS lex trivia-skips and matches iff the scan reaches `n`.
        // Mirrors the success criterion in MessageParser and SwiftSyntaxTests.runAdventOnce.
        let rootNode = parser.currentParseRoot ?? grammar.root
        let acceptingYield = parser.yield(of: rootNode).first { y in
            guard y.i == origin else { return false }
            if y.j == n { return true }
            return !parser.lexer.lex(at: y.j, terminalID: grammar.eosID).isEmpty
        }
        guard let acceptingYield else {
            Logger.ui.warning("AST: no complete parse found")
            return nil
        }
        let root = buildASTNode(rootNode, from: origin, to: acceptingYield.j)
        if !diagnostics.isEmpty {
            Logger.ui.warning("AST: \(self.diagnostics.count, privacy: .public) residual ambiguities")
            for d in diagnostics {
                Logger.ui.warning("  \(d.description, privacy: .public)")
            }
        }
        return root
    }

    private func buildASTNode(_ nt: GrammarNode, from: CharPosition, to: CharPosition) -> ParseTreeNode {
        let key = NodeSpan(id: ObjectIdentifier(nt), from: from, to: to)
        guard expanding.insert(key).inserted else {
            let node = ParseTreeNode(nt.name, from: from, to: to)
            node.isMissing = true
            return node
        }
        defer { expanding.remove(key) }

        let node = ParseTreeNode(nt.name, from: from, to: to)
        node.children = buildASTAlternate(nt, from: from, to: to)
        return node
    }

    private func buildASTAlternate(_ node: GrammarNode, from: CharPosition, to: CharPosition) -> [ParseTreeNode] {
        var candidates: [(alt: GrammarNode, children: [ParseTreeNode])] = []
        var alt = node.alt
        while let a = alt {
            defer { alt = a.alt }
            let body = a.bodySymbols.filter { $0.kind != .EPS }
            if body.isEmpty {
                if from == to { candidates.append((a, [])) }
            } else if let tiled = tileASTBody(body, from: from, to: to) {
                candidates.append((a, tiled))
            }
        }

        if candidates.count > 1 {
            let sig = candidates
                .map { "[" + $0.alt.bodySymbols.filter { $0.kind != .EPS }.map(\.name).joined(separator: " ") + "]" }
                .sorted().joined(separator: " | ")
            diagnostics.append(Diagnostic(
                message: "ambiguous alternate",
                node: node.name,
                from: from, to: to,
                candidateCount: candidates.count,
                signature: sig
            ))
        }

        return candidates.first?.children ?? []
    }

    /// Memo for `tileASTBody`, keyed by (first body symbol, suffix length, span).
    ///
    /// Without it `tileASTBody` is an EXHAUSTIVE backtracking search with no reuse: for each
    /// candidate pivot it recurses on the suffix, and it deliberately does not stop at the first
    /// success because it counts every tiling for the "ambiguous pivot" diagnostic. For a body of
    /// n symbols with k candidate ends each that is O(k^n). Measured consequence: with the
    /// `followCheck` pre-filter disabled, `testEnum65#1` goes from 1,791 to 2,624 yields and
    /// `buildAST` never returns (marker frozen for 200s across two polls) — while its parse and
    /// Oracle both finish normally. Memoising collapses the search to O(n x positions^2).
    ///
    /// The suffix is always a tail of one fixed body array, so (identity of `symbols[0]`, count)
    /// identifies it. Subtrees are shared on a hit, which is sound because an identical
    /// (symbol, from, to) IS the same subtree — `buildASTClosure` already relies on that.
    private struct TileKey: Hashable {
        let firstID: ObjectIdentifier
        let count: Int
        let from: CharPosition
        let to: CharPosition
    }
    private struct TileResult {
        let children: [ParseTreeNode]?
        let count: Int
    }
    private var tileMemo: [TileKey: TileResult] = [:]

    private func tileASTBody(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> [ParseTreeNode]? {
        guard let first = symbols.first else { return from == to ? [] : nil }
        let rest = Array(symbols.dropFirst())

        let memoKey = TileKey(firstID: ObjectIdentifier(first), count: symbols.count,
                              from: from, to: to)
        if let hit = tileMemo[memoKey] { return hit.children }

        var candidates: [ParseTreeNode]? = nil
        var candidateCount = 0

        for mid in endPositions(first, from: from) where mid <= to {
            guard let head = buildASTSymbol(first, from: from, to: mid) else { continue }
            guard let tail = tileASTBody(rest, from: mid, to: to) else { continue }
            if candidateCount == 0 {
                candidates = [head] + tail
            }
            candidateCount += 1
        }

        if candidateCount > 1 {
            diagnostics.append(Diagnostic(
                message: "ambiguous pivot",
                node: symbols.first?.name ?? "?",
                from: from, to: to,
                candidateCount: candidateCount,
                signature: "body=[" + symbols.map(\.name).joined(separator: " ") + "]"
            ))
        }

        tileMemo[memoKey] = TileResult(children: candidates, count: candidateCount)
        return candidates
    }

    private func buildASTSymbol(_ sym: GrammarNode, from: CharPosition, to: CharPosition) -> ParseTreeNode? {
        switch sym.kind {
        case .T, .TI, .C:
            let image = parser.terminalImage(startingAt: from) ?? input[from..<to]
            return ParseTreeNode(sym.name, from: from, to: to, image: image)

        case .B:
            // Boundary: zero-length predicate; no source content.
            return ParseTreeNode(sym.name, from: from, to: to, image: input[from..<from])

        case .N:
            guard let lhs = sym.alt else { return nil }
            return buildASTNode(lhs, from: from, to: to)

        case .DO, .OPT, .KLN, .POS:
            return buildASTBracket(sym, from: from, to: to)

        default:
            return nil
        }
    }

    private func buildASTBracket(_ bracket: GrammarNode, from: CharPosition, to: CharPosition) -> ParseTreeNode? {
        let node = ParseTreeNode(bracket.name, from: from, to: to)
        if from == to { return node }

        if !bracket.kind.isClosure {
            node.children.append(contentsOf: buildASTAlternate(bracket, from: from, to: to))
            return node
        }

        guard let children = buildASTClosure(bracket, from: from, to: to) else {
            return nil
        }
        node.children.append(contentsOf: children)
        return node
    }

    private func buildASTClosure(_ bracket: GrammarNode, from: CharPosition, to: CharPosition) -> [ParseTreeNode]? {
        var memo: [CharPosition: (children: [ParseTreeNode]?, count: Int)] = [:]
        let symbols = bracket.alt?.bodySymbols ?? []
        let signature = "iter=[" + symbols.filter { $0.kind != .EPS }.map(\.name).joined(separator: " ") + "]"

        func build(from pos: CharPosition) -> (children: [ParseTreeNode]?, count: Int) {
            if pos == to { return ([], 1) }
            if let cached = memo[pos] { return cached }

            var firstChildren: [ParseTreeNode]? = nil
            var successful = 0
            let ends = iterationEndPositions(bracket, from: pos).filter { $0 > pos && $0 <= to }
            for end in ends {
                let head = buildASTAlternate(bracket, from: pos, to: end)
                let tail = build(from: end)
                guard tail.count > 0, let tailChildren = tail.children else { continue }
                if firstChildren == nil {
                    firstChildren = head + tailChildren
                }
                successful += tail.count
            }

            if successful > 1 {
                diagnostics.append(Diagnostic(
                    message: "ambiguous iteration extent",
                    node: bracket.name,
                    from: pos, to: to,
                    candidateCount: successful,
                    signature: signature
                ))
            }

            let result = (firstChildren, successful)
            memo[pos] = result
            return result
        }

        let result = build(from: from)
        return result.count > 0 ? result.children : nil
    }

    // MARK: - BSR End Position Queries

    private func endPositions(_ sym: GrammarNode, from: CharPosition) -> Set<CharPosition> {
        let key = NodePos(id: ObjectIdentifier(sym), from: from)
        if let cached = endCache[key] { return cached }
        guard endGuard.insert(key).inserted else { return [] }
        defer { endGuard.remove(key) }

        let result: Set<CharPosition>
        switch sym.kind {
        case .T, .TI, .C, .B:
            result = Set(parser.yield(of: sym).lazy.filter { $0.k == from }.map(\.j))
        case .N:
            if sym.isRHS {
                guard let lhs = sym.alt else { return [] }
                let occurrenceEnds = Set(parser.yield(of: sym).lazy.filter { $0.k == from }.map(\.j))
                let lhsEnds = Set(parser.yield(of: lhs).lazy.filter { $0.i == from }.map(\.j))
                result = occurrenceEnds.intersection(lhsEnds)
            } else {
                result = Set(parser.yield(of: sym).lazy.filter { $0.i == from }.map(\.j))
            }
        case .DO, .OPT, .KLN, .POS:
            if sym.disambiguation != nil {
                // ANNOTATED bracket (@longest/@shortest): read its OWN (Oracle-prunable)
                // yields so the extent prune drives the builder's ambiguity/tiling.
                // Yields are (alternate-start, k = bracket-start, j) → filter k == from.
                result = Set(parser.yield(of: sym).lazy.filter { $0.k == from }.map(\.j))
            } else {
                // UNANNOTATED bracket: original body-recompute path, untouched.
                var positions = Set<CharPosition>()
                if sym.kind == .KLN || sym.kind == .OPT { positions.insert(from) }
                if sym.kind.isClosure {
                    var visited = Set<CharPosition>()
                    var queue = [from]
                    while !queue.isEmpty {
                        let pos = queue.removeFirst()
                        guard visited.insert(pos).inserted else { continue }
                        for end in iterationEndPositions(sym, from: pos) where end > pos {
                            positions.insert(end)
                            queue.append(end)
                        }
                    }
                } else {
                    positions.formUnion(iterationEndPositions(sym, from: from))
                }
                result = positions
            }
        case .EPS:
            result = [from]
        default:
            result = []
        }
        endCache[key] = result
        return result
    }

    /// End positions after exactly one bracket iteration, computed by chaining
    /// end positions through each alternate's body symbols.
    private func iterationEndPositions(_ bracket: GrammarNode, from: CharPosition) -> Set<CharPosition> {
        var positions = Set<CharPosition>()
        var alt = bracket.alt
        while let a = alt {
            let body = a.bodySymbols.filter { $0.kind != .EPS }
            if body.isEmpty {
                positions.insert(from)
            } else {
                var frontier: Set<CharPosition> = [from]
                for sym in body {
                    frontier = frontier.reduce(into: Set()) { $0.formUnion(endPositions(sym, from: $1)) }
                    if frontier.isEmpty { break }
                }
                positions.formUnion(frontier)
            }
            alt = a.alt
        }
        return positions
    }
}
