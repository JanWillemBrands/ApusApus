//
//  Derivation.swift
//  tinyGLL
//
//  Reads concrete derivation trees back out of the BSR, and lays them out for drawing.
//

import Foundation

// MARK: - Derivation Tree

/// One node of a concrete derivation tree. Unlike a BSR element — which records only a
/// (left, pivot, right) triple and leaves the shape implicit — this is the reconstructed
/// tree: a nonterminal with its chosen alternate's symbols as children.
///
/// ALT and END nodes never appear. An alternate's body is inlined as the nonterminal's
/// direct children, so the tree reads exactly like the production it came from.
nonisolated final class DerivationNode {
    let grammarNode: GrammarNode
    let from: Int
    let to: Int

    /// The source text this node covers. Empty for ε, which consumes nothing. Stored rather
    /// than computed: it used to read the engine's global input, which is gone, and the
    /// builder is the last place that still has the input to hand.
    let image: String

    var children: [DerivationNode] = []

    /// Set when the nonterminal's span could be derived in more than one way. The other
    /// derivations are separate trees in the builder's result; this flag marks where they
    /// diverge, which is the interesting thing to look at.
    var isAmbiguous = false

    init(_ grammarNode: GrammarNode, from: Int, to: Int, image: String) {
        self.grammarNode = grammarNode
        self.from = from
        self.to = to
        self.image = image
    }

    var kind: GrammarNodeKind { grammarNode.kind }
    var isTerminal: Bool { kind == .T || kind == .EPS }

    /// Total nodes in this subtree, used for the badge on a collapsed node.
    var subtreeCount: Int { 1 + children.reduce(0) { $0 + $1.subtreeCount } }

    /// Indented text rendering — the headless counterpart of the explorer's tree view.
    func dump(indent: Int = 0) -> String {
        let pad = String(repeating: "  ", count: indent)
        var line = "\(pad)\(grammarNode.name)  [\(from), \(to))"
        if isTerminal && !image.isEmpty { line += "  \"\(image)\"" }
        if isAmbiguous { line += "  ← ambiguous" }
        return line + "\n" + children.map { $0.dump(indent: indent + 1) }.joined()
    }
}

// MARK: - Derivation Builder

/// Rebuilds derivation trees from the BSR yields left on the grammar nodes by parseInput().
///
/// The whole job is answering one question repeatedly: "starting at input position `from`,
/// where can this grammar symbol end?" The BSR already holds those answers — see
/// `endPositions` — so building a tree is just tiling each alternate's body over a span
/// using recorded end positions as the split points.
nonisolated final class DerivationBuilder {

    private struct Span: Hashable { let n, from, to: Int }
    private struct Pos: Hashable  { let n, from: Int }

    private let parser: Parser

    private var expanding = Set<Span>()
    private var endCache = [Pos: Set<Int>]()
    private var endGuard = Set<Pos>()

    init(parser: Parser) {
        self.parser = parser
    }

    /// Every derivation of the whole input, up to `limit`. Empty when the parse failed.
    func allDerivations(limit: Int = 24) -> [DerivationNode] {
        guard parser.parseAccepted, let root = parser.nonTerminalDefinitions["S"] else { return [] }
        return trees(for: root, from: 0, to: parser.input.count, limit: limit)
    }

    /// The input slice a node covers, clamped: a span can name a position past the end of a
    /// rejected input.
    private func image(from: Int, to: Int) -> String {
        let lower = min(from, parser.input.count)
        let upper = min(max(to, lower), parser.input.count)
        return String(parser.input[lower..<upper])
    }

    private func node(_ grammarNode: GrammarNode, from: Int, to: Int) -> DerivationNode {
        DerivationNode(grammarNode, from: from, to: to, image: image(from: from, to: to))
    }

    private func trees(for nt: GrammarNode, from: Int, to: Int, limit: Int) -> [DerivationNode] {
        // A cyclic grammar (S = S .) would otherwise recur forever on the same span.
        let key = Span(n: nt.number, from: from, to: to)
        guard expanding.insert(key).inserted else { return [] }
        defer { expanding.remove(key) }

        let expansions = expandAlternates(nt, from: from, to: to, limit: limit)
        let skeletons = Set(expansions.map { kids in
            kids.map { "\($0.grammarNode.number):\($0.from):\($0.to)" }.joined(separator: "|")
        })
        let ambiguous = skeletons.count > 1

        return expansions.map { kids in
            let node = self.node(nt, from: from, to: to)
            node.children = kids
            node.isAmbiguous = ambiguous
            return node
        }
    }

    /// Walk the ALT chain of a LHS nonterminal and tile each alternate's body over [from, to).
    private func expandAlternates(_ nt: GrammarNode, from: Int, to: Int, limit: Int) -> [[DerivationNode]] {
        var results = [[DerivationNode]]()
        var alt = nt.alt
        while let a = alt {
            defer { alt = a.alt }
            guard results.count < limit else { break }
            let body = bodySymbols(of: a)
            results.append(contentsOf: tile(body, from: from, to: to, limit: limit - results.count))
        }
        return results
    }

    /// The symbols of one alternate: the seq chain from the ALT node up to its END node.
    private func bodySymbols(of alt: GrammarNode) -> [GrammarNode] {
        var symbols = [GrammarNode]()
        var node = alt.seq
        while let n = node, n.kind != .END {
            symbols.append(n)
            node = n.seq
        }
        return symbols
    }

    /// Tile body symbols left to right, using BSR end positions as the split points.
    private func tile(_ symbols: [GrammarNode], from: Int, to: Int, limit: Int) -> [[DerivationNode]] {
        guard let first = symbols.first else { return from == to ? [[]] : [] }
        let rest = Array(symbols.dropFirst())

        var results = [[DerivationNode]]()
        for mid in endPositions(first, from: from).sorted() where mid <= to {
            guard results.count < limit else { break }
            for head in nodes(for: first, from: from, to: mid, limit: limit - results.count) {
                guard results.count < limit else { break }
                for tail in tile(rest, from: mid, to: to, limit: limit - results.count) {
                    guard results.count < limit else { break }
                    results.append(head + tail)
                }
            }
        }
        return results
    }

    private func nodes(for symbol: GrammarNode, from: Int, to: Int, limit: Int) -> [[DerivationNode]] {
        switch symbol.kind {
        case .T, .EPS:
            return [[node(symbol, from: from, to: to)]]
        case .N:
            // Recur into the definition, not the reference, so the subtree is labelled by
            // the production that actually produced it.
            guard let definition = symbol.alt else { return [] }
            return trees(for: definition, from: from, to: to, limit: limit).map { [$0] }
        case .ALT, .END:
            return [[]]
        }
    }

    // MARK: BSR End Position Queries

    /// Where can `symbol` end, given that it starts at `from`?
    ///
    /// Which field of the span carries "starts at" depends on how the yield was recorded:
    ///   - terminals and ε are keyed by the pivot `k` (addYield(..., k: cI, ...) in parseInput)
    ///   - an RHS nonterminal reference is also keyed by `k` (addYield(..., k: cU, ...) in rtn)
    ///   - a LHS definition's own span is keyed by `i`, since its pivot equals its left extent
    private func endPositions(_ symbol: GrammarNode, from: Int) -> Set<Int> {
        let yields = parser.yields
        guard yields.indices.contains(symbol.number) else { return [] }

        let key = Pos(n: symbol.number, from: from)
        if let cached = endCache[key] { return cached }
        guard endGuard.insert(key).inserted else { return [] }
        defer { endGuard.remove(key) }

        let result: Set<Int>
        switch symbol.kind {
        case .T, .EPS:
            result = Set(yields[symbol.number].lazy.filter { $0.k == from }.map(\.j))

        case .N where symbol.seq != nil:
            // An RHS reference. Its own yields say where the *call* got to; the definition's
            // yields say where the nonterminal actually derived to. Only ends that both agree
            // on are real, so intersect them.
            guard let definition = symbol.alt, yields.indices.contains(definition.number) else { return [] }
            let occurrence = Set(yields[symbol.number].lazy.filter { $0.k == from }.map(\.j))
            let derived = Set(yields[definition.number].lazy.filter { $0.i == from }.map(\.j))
            result = occurrence.intersection(derived)

        case .N:
            result = Set(yields[symbol.number].lazy.filter { $0.i == from }.map(\.j))

        case .ALT, .END:
            result = []
        }

        endCache[key] = result
        return result
    }
}

// MARK: - Readback

nonisolated extension GrammarNode {
    /// `S = aS | ε` — the production a LHS nonterminal defines, reassembled from the
    /// seq/alt links for display in the inspector.
    var production: String {
        guard kind == .N, seq == nil else { return String(name) }
        var alternates = [String]()
        var alt = self.alt
        while let a = alt {
            var body = ""
            var node = a.seq
            while let n = node, n.kind != .END {
                body.append(n.name)
                node = n.seq
            }
            alternates.append(body.isEmpty ? "ε" : body)
            alt = a.alt
        }
        return "\(name) = " + alternates.joined(separator: " | ")
    }
}

// MARK: - Tree Layout

/// Grid-coordinate placement of a derivation tree. One unit is one cell; the view scales.
///
/// A parse tree needs none of Graphviz's crossing-minimisation machinery. Leaves are pinned
/// to a baseline row in source order, so the bottom row reads back as the input text, and an
/// interior node sits at the midpoint of its children. Sibling subtrees cover disjoint source
/// intervals, which makes that assignment non-overlapping and crossing-free by construction.
struct TreeLayout {

    struct Node: Identifiable {
        let id: String              // DFS path, stable across collapse
        let derivation: DerivationNode
        let x, y: CGFloat
        let isCollapsed: Bool
        var hasChildren: Bool { !derivation.children.isEmpty }
    }

    struct Edge: Identifiable {
        let id: String
        let childPath: String       // for highlighting the root-to-selection path
        let from, to: CGPoint
    }

    var nodes: [Node] = []
    var edges: [Edge] = []
    var columns: CGFloat = 1
    var rows: CGFloat = 1

    /// A node counts as a leaf when it has no children, or when the user has collapsed it.
    /// Collapsed nodes join the baseline row, which is right: they stand in for the source
    /// span their hidden subtree covers, so the bottom row still reads left to right.
    private static func isLeaf(_ node: DerivationNode, path: String, collapsed: Set<String>) -> Bool {
        node.children.isEmpty || collapsed.contains(path)
    }

    private static func leafDepth(_ node: DerivationNode, path: String, depth: Int, collapsed: Set<String>) -> Int {
        if isLeaf(node, path: path, collapsed: collapsed) { return depth }
        return node.children.enumerated()
            .map { leafDepth($1, path: "\(path).\($0)", depth: depth + 1, collapsed: collapsed) }
            .max() ?? depth
    }

    init(root: DerivationNode, collapsed: Set<String> = []) {
        let baseline = Self.leafDepth(root, path: "0", depth: 0, collapsed: collapsed)
        var cursor: CGFloat = 0
        place(root, path: "0", depth: 0, baseline: baseline, collapsed: collapsed, cursor: &cursor)
        columns = max(cursor, 1)
        rows = CGFloat(baseline + 1)
    }

    @discardableResult
    private mutating func place(_ node: DerivationNode, path: String, depth: Int,
                                baseline: Int, collapsed: Set<String>,
                                cursor: inout CGFloat) -> CGPoint {
        let isCollapsed = collapsed.contains(path)
        let point: CGPoint

        if Self.isLeaf(node, path: path, collapsed: collapsed) {
            point = CGPoint(x: cursor, y: CGFloat(baseline))
            cursor += 1
        } else {
            var childPoints = [CGPoint]()
            for (index, child) in node.children.enumerated() {
                childPoints.append(place(child, path: "\(path).\(index)", depth: depth + 1,
                                         baseline: baseline, collapsed: collapsed, cursor: &cursor))
            }
            point = CGPoint(x: (childPoints.first!.x + childPoints.last!.x) / 2, y: CGFloat(depth))
            for (index, childPoint) in childPoints.enumerated() {
                edges.append(Edge(id: "\(path)>\(index)",
                                  childPath: "\(path).\(index)",
                                  from: point, to: childPoint))
            }
        }

        nodes.append(Node(id: path, derivation: node, x: point.x, y: point.y, isCollapsed: isCollapsed))
        return point
    }
}
