//
//  StackDiagram.swift
//  tinyGLL
//
//  The Call Return Forest as a picture, drawn the way "Derivation representation using
//  binary subtree sets" draws it (§5.1, and the worked CRF for `abaa` in §5.4).
//
//    (X, k)              a cluster node — an oval. X was entered at input position k.
//    Y ::= α X · β, i    a return node — a box. A call to X made from that grammar slot,
//                        in a frame that began at input position i.
//
//  Edges run from a cluster to each of its children, leftwards, so the children of (X, k)
//  sit in the box column immediately left of k's oval column. A return node is shared by
//  every cluster that names it, which is the sharing that keeps the CRF cubic.
//
//  There is no edge for the return step itself, because a return node's label already is
//  one: `Y ::= α X · β, i` returns into the cluster (Y, i). Reading down the stack means
//  reading the labels, which the inspector will follow for you.
//

import SwiftUI

// MARK: - Snapshot

/// A value-type copy of the engine's CRF, taken when a parse finishes.
///
/// The engine's `crf` maps to `ParseCluster`, a class it mutates in place, and the explorer
/// wants the forest *as it was left* rather than a live view of whatever the next parse does
/// to those objects. Copying the two sets out is the whole job.
struct CRFSnapshot {

    struct Cluster {
        let key: ParsePosition          // paper: the cluster node (X, k)
        let returns: [ParsePosition]    // paper: its children, the return nodes
        let pops: [Int]                 // paper: the contingent return set P for this (X, k)

        var nonTerminal: GrammarNode { key.slot }
        var index: Int { key.index }
    }

    var clusters: [Cluster] = []
    var root: ParsePosition?

    init() {}

    init(crf: [ParsePosition: ParseCluster], root definition: GrammarNode?) {
        clusters = crf
            .map { Cluster(key: $0.key, returns: $0.value.returns.sorted(), pops: $0.value.pops.sorted()) }
            .sorted { ($0.index, String($0.nonTerminal.name)) < ($1.index, String($1.nonTerminal.name)) }
        root = definition.map { ParsePosition(slot: $0, index: 0) }
    }

    var isEmpty: Bool { clusters.isEmpty }

    /// Return nodes are counted after sharing, which is the number the paper's figures show.
    var returnNodeCount: Int { Set(clusters.flatMap(\.returns)).count }
    var edgeCount: Int { clusters.reduce(0) { $0 + $1.returns.count } }

    func cluster(_ key: ParsePosition) -> Cluster? { clusters.first { $0.key == key } }
}

// MARK: - Labels

/// A return node's label is a grammar slot, `Y ::= α X · β`, so it needs the production the
/// call was made from — not just the nonterminal being called. All of it is recoverable from
/// the RHS reference node the engine stores: walking its `seq` chain reaches the alternate's
/// END node, whose `seq` is the LHS Y and whose `alt` is the head of the alternate's body.
enum CRFLabels {

    /// `S ::= A · CaB` — the alternate holding `reference`, dotted just after it.
    static func slot(after reference: GrammarNode) -> String {
        guard let end = alternateEnd(from: reference),
              let definition = end.seq,
              let head = end.alt else {
            return String(reference.name)
        }

        var symbols: [String] = []
        var dotAfter = -1
        var node = head.seq
        while let current = node, current.kind != .END {
            if current == reference { dotAfter = symbols.count }
            symbols.append(String(current.name))
            node = current.seq
        }

        let dot = "\u{00B7}"
        let body: String
        if dotAfter < 0 {
            body = symbols.joined()
        } else {
            let before = symbols[...dotAfter].joined()
            let after = symbols[(dotAfter + 1)...].joined()
            // The paper writes a slot at the end of a production tight — `S ::= aAB·` —
            // and spaces the dot only when symbols follow it.
            body = after.isEmpty ? before + dot : "\(before) \(dot) \(after)"
        }
        return "\(definition.name) ::= \(body)"
    }

    /// The LHS nonterminal whose production `reference` appears in. Paired with a return
    /// node's own index it names the cluster that node returns into — the next frame down.
    static func enclosingDefinition(of reference: GrammarNode) -> GrammarNode? {
        alternateEnd(from: reference)?.seq
    }

    private static func alternateEnd(from reference: GrammarNode) -> GrammarNode? {
        var node: GrammarNode? = reference
        while let current = node {
            if current.kind == .END { return current }
            node = current.seq
        }
        return nil
    }
}

// MARK: - Layout

/// Grid placement of a CRF.
///
/// Columns alternate — the return nodes called from input position k in column 2k, the
/// clusters at position k in column 2k + 1 — which is the paper's arrangement (children in a
/// box column immediately left of their oval) and makes the x axis the input position, so
/// the picture grows rightwards as the parse advances.
///
/// Column widths come from the labels rather than being fixed, because a slot box is several
/// times wider than an `(X, k)` oval and a uniform grid would either overlap the boxes or
/// strand the ovals. Both labels are monospaced, so their width is a character count — see
/// `width`.
struct CRFLayout {

    enum NodeKind { case cluster, returnNode }

    struct Node: Identifiable {
        let id: String
        let kind: NodeKind
        let position: ParsePosition
        let label: String
        let column: Int
        let row: CGFloat
        let size: CGSize            // unzoomed; used for column widths and edge clipping
        let isRoot: Bool
        let ownerCount: Int         // return nodes: how many clusters share it

        var isShared: Bool { ownerCount > 1 }
    }

    struct Edge {
        let id: String              // only to order the drawing deterministically
        let from, to: String
    }

    var nodes: [Node] = []
    var edges: [Edge] = []
    var byID: [String: Node] = [:]
    var columnWidths: [CGFloat] = []
    var rows: CGFloat = 1

    var totalWidth: CGFloat { columnWidths.reduce(0, +) }

    func centre(of column: Int) -> CGFloat {
        guard columnWidths.indices.contains(column) else { return 0 }
        return columnWidths.prefix(column).reduce(0, +) + columnWidths[column] / 2
    }

    init(snapshot: CRFSnapshot) {
        guard !snapshot.isEmpty else { return }

        // A return node is drawn once however many clusters name it, so collect the owners
        // of each before placing anything.
        var owners: [ParsePosition: [ParsePosition]] = [:]
        for cluster in snapshot.clusters {
            for returnNode in cluster.returns {
                owners[returnNode, default: []].append(cluster.key)
            }
        }

        var clusterColumn: [ParsePosition: Int] = [:]
        for cluster in snapshot.clusters {
            clusterColumn[cluster.key] = 2 * cluster.index + 1
        }

        // A shared node goes left of the leftmost cluster that names it, so at least one of
        // its edges is the paper's short leftward step and the rest reach further.
        var returnColumn: [ParsePosition: Int] = [:]
        for (returnNode, clusters) in owners {
            returnColumn[returnNode] = 2 * (clusters.map(\.index).min() ?? returnNode.index)
        }

        // Rows are packed per column. Clusters go first so return nodes can be ordered by
        // the rows of the clusters pointing at them, which keeps the edges short.
        var nextRow: [Int: Int] = [:]
        var rowOf: [String: CGFloat] = [:]

        for cluster in snapshot.clusters {
            let column = clusterColumn[cluster.key]!
            let row = nextRow[column] ?? 0
            nextRow[column] = row + 1
            rowOf[Self.clusterID(cluster.key)] = CGFloat(row)
        }

        func barycentre(_ returnNode: ParsePosition) -> CGFloat {
            let rows = (owners[returnNode] ?? []).compactMap { rowOf[Self.clusterID($0)] }
            guard !rows.isEmpty else { return 0 }
            return rows.reduce(0, +) / CGFloat(rows.count)
        }

        // Dictionary order is not stable across runs, so the tie-break is on the node itself.
        let orderedReturns = owners.keys.sorted { left, right in
            let a = barycentre(left), b = barycentre(right)
            return a == b ? left < right : a < b
        }

        for returnNode in orderedReturns {
            let column = returnColumn[returnNode]!
            let row = nextRow[column] ?? 0
            nextRow[column] = row + 1
            rowOf[Self.returnID(returnNode)] = CGFloat(row)
        }

        for cluster in snapshot.clusters {
            let id = Self.clusterID(cluster.key)
            let label = "\(cluster.nonTerminal.name), \(cluster.index)"
            nodes.append(Node(id: id,
                              kind: .cluster,
                              position: cluster.key,
                              label: label,
                              column: clusterColumn[cluster.key]!,
                              row: rowOf[id] ?? 0,
                              size: CGSize(width: Self.width(label, fontSize: Self.clusterFontSize) + 26, height: 28),
                              isRoot: cluster.key == snapshot.root,
                              ownerCount: 0))
        }

        for returnNode in orderedReturns {
            let id = Self.returnID(returnNode)
            let label = "\(CRFLabels.slot(after: returnNode.slot)), \(returnNode.index)"
            nodes.append(Node(id: id,
                              kind: .returnNode,
                              position: returnNode,
                              label: label,
                              column: returnColumn[returnNode]!,
                              row: rowOf[id] ?? 0,
                              size: CGSize(width: Self.width(label, fontSize: Self.returnFontSize) + 22, height: 26),
                              isRoot: false,
                              ownerCount: owners[returnNode]?.count ?? 0))
        }

        byID = Dictionary(uniqueKeysWithValues: nodes.map { ($0.id, $0) })

        columnWidths = Array(repeating: 0, count: (nodes.map(\.column).max() ?? 0) + 1)
        for node in nodes {
            columnWidths[node.column] = max(columnWidths[node.column], node.size.width + Self.columnGap)
        }

        rows = CGFloat(max(nextRow.values.max() ?? 1, 1))

        for cluster in snapshot.clusters {
            for returnNode in cluster.returns {
                edges.append(Edge(id: "\(cluster.key) \(returnNode)",
                                  from: Self.clusterID(cluster.key),
                                  to: Self.returnID(returnNode)))
            }
        }
        edges.sort { $0.id < $1.id }
    }

    // MARK: Measurement

    static let columnGap: CGFloat = 32

    /// The point sizes CRFNodeBadge draws these two labels at. Shared with the badge so the
    /// measurement below and the text on screen cannot drift apart.
    static let clusterFontSize: CGFloat = 12
    static let returnFontSize: CGFloat = 11

    /// How wide a label will be.
    ///
    /// Both labels are monospaced, so this is just the character count times one advance —
    /// which means no text measurement, and so no AppKit. 0.6 em is the advance of the
    /// monospaced system font; the figure only has to be close, because it decides column
    /// spacing and edge clipping while SwiftUI still lays out each badge from its own text.
    private static func width(_ text: String, fontSize: CGFloat) -> CGFloat {
        CGFloat(text.count) * fontSize * 0.6
    }

    /// Cluster keys hold a LHS definition node and return nodes a RHS reference node, so the
    /// two can never collide — the prefix is there to keep the ids readable in a trace.
    static func clusterID(_ position: ParsePosition) -> String {
        "C\(position.slot.number).\(position.index)"
    }

    static func returnID(_ position: ParsePosition) -> String {
        "R\(position.slot.number).\(position.index)"
    }
}

// MARK: - Diagram

struct StackDiagramView: View {

    let snapshot: CRFSnapshot

    @State private var selection: String?
    @State private var zoom = 1.0

    private let rowHeight: CGFloat = 52
    private let margin: CGFloat = 34

    private var layout: CRFLayout { CRFLayout(snapshot: snapshot) }

    var body: some View {
        HSplitView {
            canvas
            inspector
                .frame(minWidth: 240, idealWidth: 300, maxWidth: 420)
        }
    }

    // MARK: Canvas

    private func point(_ node: CRFLayout.Node, in layout: CRFLayout) -> CGPoint {
        CGPoint(x: margin + layout.centre(of: node.column) * zoom,
                y: margin + (node.row + 0.5) * rowHeight * zoom)
    }

    private func contentSize(_ layout: CRFLayout) -> CGSize {
        CGSize(width: margin * 2 + layout.totalWidth * zoom,
               height: margin * 2 + layout.rows * rowHeight * zoom)
    }

    @ViewBuilder
    private var canvas: some View {
        let layout = self.layout
        if layout.nodes.isEmpty {
            ZStack {
                Color(.textBackgroundColor)
                Text("No call return forest — parse something first")
                    .foregroundStyle(.secondary)
            }
            .frame(minWidth: 420, minHeight: 300)
        } else {
            let size = contentSize(layout)
            VStack(spacing: 0) {
                ScrollView([.horizontal, .vertical]) {
                    ZStack(alignment: .topLeading) {
                        Canvas { context, _ in
                            draw(edges: layout, in: context)
                        }
                        .frame(width: size.width, height: size.height)
                        // The badges sit above this layer and carry their own gestures, so a
                        // tap that reaches the canvas is a tap on the background.
                        .contentShape(Rectangle())
                        .onTapGesture(perform: resetDiagram)

                        ForEach(layout.nodes) { node in
                            CRFNodeBadge(node: node,
                                         isSelected: selection == node.id,
                                         zoom: zoom,
                                         select: { selection = node.id })
                                .position(point(node, in: layout))
                        }
                    }
                    .frame(width: size.width, height: size.height)
                }
                // Covers the part of the viewport the content does not reach.
                .background(Color(.textBackgroundColor).onTapGesture(perform: resetDiagram))

                Divider()
                controls
            }
        }
    }

    private func draw(edges layout: CRFLayout, in context: GraphicsContext) {
        for edge in layout.edges {
            guard let source = layout.byID[edge.from], let target = layout.byID[edge.to] else { continue }

            let from = point(source, in: layout)
            let to = point(target, in: layout)
            let lit = selection == edge.from || selection == edge.to

            // Clipped to the node borders at both ends: the badges are opaque, so an edge
            // drawn to the centres would lose its arrowhead underneath the box.
            let tail = border(from: to, to: from, half: half(of: source))
            let tip = border(from: from, to: to, half: half(of: target))

            var path = Path()
            path.move(to: tail)
            path.addLine(to: tip)

            let colour = lit ? Color.accentColor : .primary.opacity(0.5)
            context.stroke(path, with: .color(colour), lineWidth: lit ? 2 : 1)
            context.fill(arrowhead(at: tip, from: tail, size: 7 * zoom), with: .color(colour))
        }
    }

    private func half(of node: CRFLayout.Node) -> CGSize {
        CGSize(width: (node.size.width / 2 + 3) * zoom,
               height: (node.size.height / 2 + 3) * zoom)
    }

    /// Where the segment from `start` crosses the box of half-size `half` centred on `end`.
    private func border(from start: CGPoint, to end: CGPoint, half: CGSize) -> CGPoint {
        let dx = start.x - end.x
        let dy = start.y - end.y
        guard dx != 0 || dy != 0 else { return end }

        var t = CGFloat.greatestFiniteMagnitude
        if dx != 0 { t = min(t, half.width / abs(dx)) }
        if dy != 0 { t = min(t, half.height / abs(dy)) }
        return CGPoint(x: end.x + dx * min(t, 1), y: end.y + dy * min(t, 1))
    }

    private func arrowhead(at tip: CGPoint, from tail: CGPoint, size: CGFloat) -> Path {
        let angle = atan2(tip.y - tail.y, tip.x - tail.x)
        let spread = CGFloat.pi / 7
        var path = Path()
        path.move(to: tip)
        path.addLine(to: CGPoint(x: tip.x - size * cos(angle - spread),
                                 y: tip.y - size * sin(angle - spread)))
        path.addLine(to: CGPoint(x: tip.x - size * cos(angle + spread),
                                 y: tip.y - size * sin(angle + spread)))
        path.closeSubpath()
        return path
    }

    private var controls: some View {
        HStack {
            Spacer()
            ZoomStrip(zoom: $zoom)
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 6)
    }

    /// Clicking the background puts the forest back to its defaults.
    private func resetDiagram() {
        selection = nil
        zoom = 1
    }

    // MARK: Inspector

    @ViewBuilder
    private var inspector: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 14) {
                switch selection.flatMap({ layout.byID[$0] }) {
                case .some(let node) where node.kind == .cluster: clusterDetail(node)
                case .some(let node):                             returnDetail(node)
                case .none:                                       summary
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(12)
        }
    }

    @ViewBuilder
    private func clusterDetail(_ node: CRFLayout.Node) -> some View {
        let cluster = snapshot.cluster(node.position)

        InspectorSection("Cluster node") {
            InspectorRow("label", node.label)
            InspectorRow("entered at", "\(node.position.index)")
            InspectorRow("production", node.position.slot.production)
            InspectorRow("children", "\(cluster?.returns.count ?? 0)")
            // The paper's contingent return set P, which for this node is the set of input
            // positions the call has been seen to reach.
            InspectorRow("returns at", (cluster?.pops ?? []).map(String.init).joined(separator: ", "))
            if node.isRoot {
                Text("The root cluster, created before the descriptor loop starts.")
                    .font(.system(size: 11))
                    .foregroundStyle(.secondary)
            }
        }
    }

    @ViewBuilder
    private func returnDetail(_ node: CRFLayout.Node) -> some View {
        InspectorSection("Return node") {
            InspectorRow("slot", CRFLabels.slot(after: node.position.slot))
            InspectorRow("called", String(node.position.slot.name))
            InspectorRow("frame from", "\(node.position.index)")
            InspectorRow("shared by", "\(node.ownerCount) cluster\(node.ownerCount == 1 ? "" : "s")")
        }

        // The step the diagram leaves to the label: (Y, i) is the frame below this one.
        if let definition = CRFLabels.enclosingDefinition(of: node.position.slot) {
            let target = ParsePosition(slot: definition, index: node.position.index)
            InspectorSection("Returns into") {
                Button {
                    selection = CRFLayout.clusterID(target)
                } label: {
                    Text(verbatim: "\(definition.name), \(node.position.index)")
                        .font(.system(size: 11).monospaced())
                }
                .buttonStyle(.link)
                .disabled(layout.byID[CRFLayout.clusterID(target)] == nil)
            }
        }
    }

    @ViewBuilder
    private var summary: some View {
        InspectorSection("Call return forest") {
            InspectorRow("clusters", "\(snapshot.clusters.count)")
            InspectorRow("return nodes", "\(snapshot.returnNodeCount)")
            InspectorRow("edges", "\(snapshot.edgeCount)")
        }

        Text("An oval is a cluster node (X, k): the nonterminal X was entered at input position k. A box is a return node Y ::= \u{03B1}X \u{00B7} \u{03B2}, i: a call to X from that slot, in a frame that began at i — and so the frame below it is (Y, i).")
            .font(.system(size: 11))
            .foregroundStyle(.secondary)
    }
}

// MARK: - Node

private struct CRFNodeBadge: View {
    let node: CRFLayout.Node
    let isSelected: Bool
    let zoom: Double
    let select: () -> Void

    var body: some View {
        Text(node.label)
            .font(.system(size: (node.kind == .cluster ? CRFLayout.clusterFontSize
                                                       : CRFLayout.returnFontSize) * zoom,
                          weight: node.kind == .cluster ? .semibold : .regular).monospaced())
            .padding(.horizontal, 9 * zoom)
            .padding(.vertical, 4 * zoom)
            .diagramBadge(shape,
                          fill: fill,
                          stroke: stroke,
                          lineWidth: isSelected ? 2.5 : (node.isRoot ? 2 : 1))
            .help(tooltip)
            .onTapGesture { select() }
    }

    /// The paper draws cluster nodes as ovals and return nodes as boxes.
    private var shape: AnyShape {
        node.kind == .cluster ? AnyShape(Capsule()) : AnyShape(RoundedRectangle(cornerRadius: 4))
    }

    private var fill: Color {
        if isSelected { return .accentColor.opacity(0.35) }
        return node.kind == .cluster ? .accentColor.opacity(node.isRoot ? 0.22 : 0.13)
                                     : .secondary.opacity(0.1)
    }

    private var stroke: Color {
        if isSelected { return .accentColor }
        if node.isRoot { return .accentColor.opacity(0.7) }
        return .secondary.opacity(0.45)
    }

    private var tooltip: String {
        switch node.kind {
        case .cluster:
            return "cluster \(node.label)" + (node.isRoot ? " — root" : "")
        case .returnNode:
            return node.label + (node.isShared ? "  — shared by \(node.ownerCount) clusters" : "")
        }
    }
}

#Preview("Stack — ambiguous") {
    StackDiagramView(snapshot: ParseResult.previewAmbiguous.crf)
        .frame(width: 1000, height: 560)
}
