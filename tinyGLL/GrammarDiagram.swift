//
//  GrammarDiagram.swift
//  tinyGLL
//
//  The GrammarNode graph as a grid — the SwiftUI replacement for the Graphviz ART diagram.
//

import SwiftUI

// MARK: - Layout

/// Grid placement of the GrammarNode graph for one nonterminal and the ones it references.
///
/// The grid falls straight out of the two link kinds: `.seq` steps down one row, `.alt` steps
/// right one column. Nothing else is needed — no crossing minimisation, no rank solving.
///
/// Advent's Graphviz version had to cache a `Cell` on every GrammarNode and then fabricate
/// invisible nodes joined by invisible `weight=100000000` / `rank=same` edges, purely because
/// Graphviz accepts no coordinates and had to be bullied into a lattice. Assigning coordinates
/// directly needs none of that, and needs nothing stored on the model.
///
/// Three link families cannot follow the grid, because they point backwards or sideways to an
/// arbitrary place, and they are the ones drawn optionally:
///   - `endSeq`    END → the LHS nonterminal whose production it closes
///   - `endAlt`    END → the ALT heading its own alternate
///   - `reference` an RHS nonterminal → its LHS definition, possibly in another cluster
/// Everything else is planar by construction. (In Advent, bracket `.alt` links are a fourth
/// family: a bracket body consumes columns, which is the only thing that makes a horizontal
/// `.alt` span more than one column. tinyGLL has no brackets, so its grid is fully planar.)
struct ASTLayout {

    /// Blank rows left between stacked clusters.
    static let clusterGap: CGFloat = 1.4

    enum EdgeKind {
        case seq, alt              // the grid itself
        case endSeq, endAlt        // END's two back-links
        case reference             // RHS nonterminal → its definition

        /// Back-links are drawn as arcs bowing clear of the grid, which is what the Graphviz
        /// version was reaching for with `constraint = false`.
        var isBackLink: Bool { self != .seq && self != .alt }
    }

    struct Node: Identifiable {
        let id: Int                // GrammarNode.number — already unique per load
        let node: GrammarNode
        let x, y: CGFloat
        let cluster: Character

        /// An RHS reference whose definition is missing from the grammar.
        var isDangling: Bool { node.kind == .N && node.seq != nil && node.alt == nil }
    }

    struct Edge: Identifiable {
        let id: String
        let kind: EdgeKind
        let from, to: CGPoint
    }

    struct Cluster: Identifiable {
        let id: Character
        let production: String
        let origin: CGFloat        // top row in the shared coordinate space
        let columns, rows: CGFloat
        let isFocus: Bool

        /// The box's fill opacity. A node standing on the box re-applies it under its own
        /// fill, so that an opaque node matches the backdrop it hides.
        var tint: Double { isFocus ? 0.08 : 0.04 }
    }

    var nodes: [Node] = []
    var edges: [Edge] = []
    var clusters: [Cluster] = []
    var columns: CGFloat = 1
    var rows: CGFloat = 1

    init(focus: Character,
         definitions: [Character: GrammarNode],
         showEndLinks: Bool = false,
         showReferences: Bool = true) {

        guard let focusDefinition = definitions[focus] else { return }

        // Focus first, then each distinct nonterminal its production references, in order of
        // appearance — one hop. A self-reference adds no second cluster: its edge simply loops
        // back into the focus cluster.
        var order: [Character] = [focus]
        for name in Self.references(in: focusDefinition)
        where !order.contains(name) && definitions[name] != nil {
            order.append(name)
        }

        // Edges are collected as node numbers and resolved to points afterwards: a back-link
        // can name a node in a cluster that has not been placed yet.
        var positions: [Int: CGPoint] = [:]
        var pending: [(from: Int, to: Int, kind: EdgeKind)] = []
        var originRow: CGFloat = 0

        for name in order {
            guard let definition = definitions[name] else { continue }

            var maxRow = 0
            var maxCol = 0
            place(definition, cluster: name, row: 0, col: 0, originRow: originRow,
                  maxRow: &maxRow, maxCol: &maxCol, positions: &positions, pending: &pending)

            clusters.append(Cluster(id: name,
                                    production: definition.production,
                                    origin: originRow,
                                    columns: CGFloat(maxCol + 1),
                                    rows: CGFloat(maxRow + 1),
                                    isFocus: name == focus))

            originRow += CGFloat(maxRow + 1) + Self.clusterGap
            columns = max(columns, CGFloat(maxCol + 1))
        }

        rows = max(originRow - Self.clusterGap, 1)

        for (index, link) in pending.enumerated() {
            switch link.kind {
            case .endSeq, .endAlt: if !showEndLinks { continue }
            case .reference:       if !showReferences { continue }
            case .seq, .alt:       break
            }
            // A one-hop view can reference a nonterminal two hops out, which has no position.
            guard let from = positions[link.from], let to = positions[link.to] else { continue }
            edges.append(Edge(id: "\(index)", kind: link.kind, from: from, to: to))
        }
    }

    /// Walks one production, assigning `.seq` down and `.alt` right. The same recursion as
    /// Advent's `draw`, minus the grid bookkeeping and the scaffolding pass.
    ///
    /// `maxCol` is a running allocator rather than `col + 1`, so alternates of different
    /// lengths never land in the same column.
    private mutating func place(_ node: GrammarNode, cluster: Character,
                                row: Int, col: Int, originRow: CGFloat,
                                maxRow: inout Int, maxCol: inout Int,
                                positions: inout [Int: CGPoint],
                                pending: inout [(from: Int, to: Int, kind: EdgeKind)]) {

        let point = CGPoint(x: CGFloat(col), y: originRow + CGFloat(row))
        positions[node.number] = point
        nodes.append(Node(id: node.number, node: node, x: point.x, y: point.y, cluster: cluster))

        if let seq = node.seq {
            if node.kind == .END {
                // END.seq is the LHS nonterminal, back at the cluster's origin.
                pending.append((from: node.number, to: seq.number, kind: .endSeq))
            } else {
                maxRow = max(maxRow, row + 1)
                place(seq, cluster: cluster, row: row + 1, col: col, originRow: originRow,
                      maxRow: &maxRow, maxCol: &maxCol, positions: &positions, pending: &pending)
                pending.append((from: node.number, to: seq.number, kind: .seq))
            }
        }

        if let alt = node.alt {
            if node.kind == .END {
                // END.alt heads its own alternate — a back-link up its own column.
                pending.append((from: node.number, to: alt.number, kind: .endAlt))
            } else if node.kind == .N && node.seq != nil {
                // An RHS reference. Recursing here would not terminate; the definition is a
                // cluster of its own.
                pending.append((from: node.number, to: alt.number, kind: .reference))
            } else {
                maxCol = max(maxCol + 1, col + 1)
                place(alt, cluster: cluster, row: row, col: maxCol, originRow: originRow,
                      maxRow: &maxRow, maxCol: &maxCol, positions: &positions, pending: &pending)
                pending.append((from: node.number, to: alt.number, kind: .alt))
            }
        }
    }

    /// The RHS nonterminal names a production mentions, in order of appearance.
    private static func references(in definition: GrammarNode) -> [Character] {
        var names: [Character] = []
        var alt = definition.alt
        while let a = alt {
            var node = a.seq
            while let n = node, n.kind != .END {
                if n.kind == .N { names.append(n.name) }
                node = n.seq
            }
            alt = a.alt
        }
        return names
    }
}

// MARK: - Diagram

struct GrammarDiagramView: View {

    let definitions: [Character: GrammarNode]

    /// BSR yields by GrammarNode.number, for the inspector.
    let yields: [Set<BinarySpan>]

    @State private var focus: Character?
    @State private var selection: Int?
    @State private var showEndLinks = false
    @State private var showReferences = true
    @State private var zoom = 1.0

    private let cell = CGSize(width: 72, height: 58)
    private let margin: CGFloat = 34

    /// Falls back to the start symbol, then to the first definition, so the view stays valid
    /// when the grammar is edited under it and the focused nonterminal disappears.
    private var effectiveFocus: Character? {
        if let focus, definitions[focus] != nil { return focus }
        if definitions["S"] != nil { return "S" }
        return definitions.keys.sorted().first
    }

    private var layout: ASTLayout? {
        guard let effectiveFocus else { return nil }
        return ASTLayout(focus: effectiveFocus,
                         definitions: definitions,
                         showEndLinks: showEndLinks,
                         showReferences: showReferences)
    }

    var body: some View {
        HSplitView {
            sidebar
                .frame(minWidth: 130, idealWidth: 150, maxWidth: 220)
            canvas
            inspector
                .frame(minWidth: 220, idealWidth: 260, maxWidth: 380)
        }
    }

    // MARK: Sidebar

    private var sidebar: some View {
        VStack(alignment: .leading, spacing: 0) {
            Text("NONTERMINALS")
                .font(.system(size: 10, weight: .semibold))
                .foregroundStyle(.secondary)
                .padding(.horizontal, 10)
                .padding(.top, 10)
                .padding(.bottom, 4)

            List(definitions.keys.sorted(), id: \.self, selection: $focus) { name in
                HStack(spacing: 6) {
                    Text(String(name))
                        .font(.system(size: 12, weight: .semibold).monospaced())
                    Text(definitions[name]?.production ?? "")
                        .font(.system(size: 10).monospaced())
                        .foregroundStyle(.secondary)
                        .lineLimit(1)
                }
                .tag(name)
            }
            .listStyle(.sidebar)

            Divider()

            VStack(alignment: .leading, spacing: 6) {
                Toggle(isOn: $showReferences) {
                    Label("reference links", systemImage: "arrow.turn.down.right")
                        .font(.system(size: 11))
                }
                Toggle(isOn: $showEndLinks) {
                    Label("END links", systemImage: "arrow.uturn.left")
                        .font(.system(size: 11))
                }
            }
            .toggleStyle(.checkbox)
            .padding(10)
        }
    }

    // MARK: Canvas

    private func canvasPoint(_ x: CGFloat, _ y: CGFloat) -> CGPoint {
        CGPoint(x: margin + (x + 0.5) * cell.width * zoom,
                y: margin + (y + 0.5) * cell.height * zoom)
    }

    private func contentSize(_ layout: ASTLayout) -> CGSize {
        CGSize(width: margin * 2 + layout.columns * cell.width * zoom,
               height: margin * 2 + layout.rows * cell.height * zoom)
    }

    @ViewBuilder
    private var canvas: some View {
        if let layout, !layout.nodes.isEmpty {
            let size = contentSize(layout)
            VStack(spacing: 0) {
                ScrollView([.horizontal, .vertical]) {
                    ZStack(alignment: .topLeading) {
                        Canvas { context, _ in
                            draw(clusters: layout.clusters, in: context)
                            draw(edges: layout.edges, in: context)
                        }
                        .frame(width: size.width, height: size.height)
                        // The badges sit above this layer and carry their own gestures, so a
                        // tap that reaches the canvas is a tap on the background.
                        .contentShape(Rectangle())
                        .onTapGesture(perform: resetDiagram)

                        ForEach(layout.nodes) { node in
                            GrammarNodeBadge(node: node,
                                             isSelected: selection == node.id,
                                             clusterTint: tint(of: node, in: layout),
                                             zoom: zoom,
                                             select: { selection = node.id },
                                             jump: { jump(from: node) })
                                .position(canvasPoint(node.x, node.y))
                        }
                    }
                    .frame(width: size.width, height: size.height)
                }
                // Covers the part of the viewport the content does not reach.
                .background(Color(.textBackgroundColor).onTapGesture(perform: resetDiagram))

                Divider()
                legend
            }
        } else {
            ZStack {
                Color(.textBackgroundColor)
                Text(definitions.isEmpty ? "No grammar — parse one first" : "Select a nonterminal")
                    .foregroundStyle(.secondary)
            }
            .frame(minWidth: 380, minHeight: 300)
        }
    }

    /// The fill of the cluster box a node stands on, so the node can reproduce it opaquely.
    private func tint(of node: ASTLayout.Node, in layout: ASTLayout) -> Double {
        layout.clusters.first { $0.id == node.cluster }?.tint ?? 0
    }

    private func draw(clusters: [ASTLayout.Cluster], in context: GraphicsContext) {
        for cluster in clusters {
            let topLeft = canvasPoint(-0.45, cluster.origin - 0.35)
            let bottomRight = canvasPoint(cluster.columns - 0.55, cluster.origin + cluster.rows - 0.65)
            let box = Path(roundedRect: CGRect(x: topLeft.x, y: topLeft.y,
                                               width: bottomRight.x - topLeft.x,
                                               height: bottomRight.y - topLeft.y),
                           cornerRadius: 8)

            context.fill(box, with: .color(.secondary.opacity(cluster.tint)))
            context.stroke(box,
                           with: .color(cluster.isFocus ? .accentColor.opacity(0.5) : .secondary.opacity(0.25)),
                           lineWidth: 1)

            context.draw(Text(cluster.production)
                            .font(.system(size: 10 * zoom).monospaced())
                            .foregroundStyle(cluster.isFocus ? Color.accentColor : .secondary),
                         at: CGPoint(x: topLeft.x + 6, y: topLeft.y - 8),
                         anchor: .bottomLeading)
        }
    }

    private func draw(edges: [ASTLayout.Edge], in context: GraphicsContext) {
        for edge in edges {
            let start = canvasPoint(edge.from.x, edge.from.y)
            let end = canvasPoint(edge.to.x, edge.to.y)

            var path = Path()
            path.move(to: start)
            if edge.kind.isBackLink {
                // Bow the arc sideways, clear of the column it travels along.
                let bow = max(40, abs(end.y - start.y) * 0.28) * (edge.kind == .endAlt ? -1 : 1)
                path.addQuadCurve(to: end,
                                  control: CGPoint(x: (start.x + end.x) / 2 + bow,
                                                   y: (start.y + end.y) / 2))
            } else {
                path.addLine(to: end)
            }

            context.stroke(path,
                           with: .color(color(for: edge.kind)),
                           style: StrokeStyle(lineWidth: 1,
                                              dash: edge.kind.isBackLink ? [4, 3] : []))
        }
    }

    /// Same colour assignment the Graphviz version used for these three families.
    private func color(for kind: ASTLayout.EdgeKind) -> Color {
        switch kind {
        case .seq, .alt:  return .secondary.opacity(0.45)
        case .endSeq:     return .red.opacity(0.55)
        case .endAlt:     return .green.opacity(0.6)
        case .reference:  return .blue.opacity(0.55)
        }
    }

    private var legend: some View {
        HStack(spacing: 14) {
            ForEach([("seq / alt", Color.secondary.opacity(0.45)),
                     ("END → nonterminal", .red.opacity(0.55)),
                     ("END → alternate", .green.opacity(0.6)),
                     ("reference → definition", .blue.opacity(0.55))], id: \.0) { label, color in
                HStack(spacing: 4) {
                    RoundedRectangle(cornerRadius: 1).fill(color).frame(width: 14, height: 2)
                    Text(label).font(.system(size: 10)).foregroundStyle(.secondary)
                }
            }
            Spacer()
            ZoomStrip(zoom: $zoom)
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 6)
    }

    /// Clicking the background puts the diagram back to its defaults. The focused
    /// nonterminal is deliberately left alone: it is chosen in the sidebar, or by following a
    /// reference, and a stray click should not navigate away from it.
    private func resetDiagram() {
        selection = nil
        showEndLinks = false
        showReferences = true
        zoom = 1
    }

    /// Double-clicking an RHS reference refocuses on its definition — the navigation that
    /// replaces drawing every cross-reference at once.
    private func jump(from node: ASTLayout.Node) {
        guard node.node.kind == .N, node.node.seq != nil,
              definitions[node.node.name] != nil else { return }
        focus = node.node.name
        selection = nil
    }

    // MARK: Inspector

    private var selectedNode: ASTLayout.Node? {
        guard let selection, let layout else { return nil }
        return layout.nodes.first { $0.id == selection }
    }

    @ViewBuilder
    private var inspector: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 14) {
                if let selected = selectedNode {
                    let node = selected.node

                    InspectorSection("Node") {
                        InspectorRow("symbol", node.kind == .ALT || node.kind == .END
                                      ? "—" : String(node.name))
                        InspectorRow("kind", "\(node.kind)")
                        InspectorRow("number", "#\(node.number)")
                        InspectorRow("cluster", String(selected.cluster))
                        InspectorRow("grid", "row \(Int(selected.y)), col \(Int(selected.x))")
                    }

                    InspectorSection("Links") {
                        InspectorRow("seq", node.seq.map { "#\($0.number)  \($0.kind)" } ?? "none")
                        InspectorRow("alt", node.alt.map { "#\($0.number)  \($0.kind)" } ?? "none")
                        if selected.isDangling {
                            Text("References '\(String(node.name))', which the grammar does not define.")
                                .font(.system(size: 11))
                                .foregroundStyle(.red)
                        }
                    }

                    InspectorSection("BSR yields  (i:k:j)") {
                        let spans = yields.indices.contains(node.number)
                            ? yields[node.number].sorted()
                            : []
                        if spans.isEmpty {
                            Text("none — this slot yielded nothing in the last parse")
                                .font(.system(size: 11))
                                .foregroundStyle(.secondary)
                        } else {
                            ForEach(spans, id: \.self) { span in
                                Text(span.description)
                                    .font(.system(size: 11).monospaced())
                                    .foregroundStyle(.secondary)
                            }
                        }
                    }
                } else {
                    Text("Select a node")
                        .foregroundStyle(.secondary)
                    Text("Click to inspect. Double-click a nonterminal reference to follow it to its definition.")
                        .font(.system(size: 11))
                        .foregroundStyle(.secondary)
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(12)
        }
    }
}

// MARK: - Node

private struct GrammarNodeBadge: View {
    let node: ASTLayout.Node
    let isSelected: Bool
    let clusterTint: Double
    let zoom: Double
    let select: () -> Void
    let jump: () -> Void

    var body: some View {
        Text(label)
            .font(.system(size: fontSize * zoom, weight: weight).monospaced())
            .foregroundStyle(node.isDangling ? Color.red : .primary)
            .frame(minWidth: 22 * zoom)
            .padding(.horizontal, 7 * zoom)
            .padding(.vertical, 3 * zoom)
            .diagramBadge(shape,
                          fill: fill,
                          under: .secondary.opacity(clusterTint),
                          stroke: stroke,
                          lineWidth: isSelected ? 2.5 : 1)
            .help(tooltip)
            .onTapGesture(count: 2) { jump() }
            .onTapGesture { select() }
    }

    /// ALT and END carry '[' and ']' as names, which read as punctuation rather than as the
    /// structural markers they are, so they are labelled by kind instead.
    private var label: String {
        switch node.node.kind {
        case .ALT: return "alt"
        case .END: return "end"
        default:   return String(node.node.name)
        }
    }

    private var fontSize: CGFloat { node.node.kind == .ALT || node.node.kind == .END ? 9 : 13 }

    private var weight: Font.Weight { node.node.kind == .N ? .semibold : .regular }

    private var shape: AnyShape {
        switch node.node.kind {
        case .N:          return AnyShape(Capsule())
        case .ALT, .END:  return AnyShape(RoundedRectangle(cornerRadius: 3))
        default:          return AnyShape(RoundedRectangle(cornerRadius: 4))
        }
    }

    private var fill: Color {
        if isSelected { return .accentColor.opacity(0.35) }
        switch node.node.kind {
        case .ALT, .END: return .secondary.opacity(0.1)
        case .EPS:       return .secondary.opacity(0.12)
        case .N:         return node.node.seq == nil ? .accentColor.opacity(0.16)
                                                     : .blue.opacity(0.12)
        default:         return Color(.controlBackgroundColor)
        }
    }

    private var stroke: Color {
        if isSelected { return .accentColor }
        if node.isDangling { return .red }
        return .secondary.opacity(node.node.kind == .ALT || node.node.kind == .END ? 0.3 : 0.5)
    }

    private var tooltip: String {
        var text = "#\(node.node.number)  \(node.node.kind)"
        if node.node.kind != .ALT && node.node.kind != .END { text += "  \(node.node.name)" }
        if node.node.kind == .N && node.node.seq == nil { text += "  (definition)" }
        if node.node.kind == .N && node.node.seq != nil { text += "  (reference — double-click to follow)" }
        if node.isDangling { text += "  — undefined" }
        return text
    }
}

#Preview("Grammar") {
    let result = ParseResult.preview()
    GrammarDiagramView(definitions: result.definitions, yields: result.yields)
        .frame(width: 1000, height: 600)
}
