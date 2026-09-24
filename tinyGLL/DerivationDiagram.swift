//
//  DerivationDiagram.swift
//  tinyGLL
//
//  One concrete derivation tree, read back out of the BSR. Click a node to see its yields
//  and the source span it covers, double-click to collapse it, and step through the
//  alternative derivations of an ambiguous parse.
//
//  The placement itself is TreeLayout, in Derivation.swift: leaves pinned to a baseline row
//  in source order, interior nodes at the midpoint of their children, so the bottom row of
//  the tree reads back as the input.
//

import SwiftUI

// MARK: - Diagram

struct DerivationDiagramView: View {

    /// Every derivation of the input. More than one means the parse was ambiguous, and the
    /// stepper in the bottom strip moves between them.
    let derivations: [DerivationNode]

    /// The parsed input, for the source strip below the tree.
    let input: [Character]

    /// BSR yields by GrammarNode.number, for the inspector.
    let yields: [Set<BinarySpan>]

    @State private var index = 0
    @State private var collapsed: Set<String> = []
    @State private var selection: String?
    @State private var zoom = 1.0

    private let cell = CGSize(width: 78, height: 68)
    private let margin: CGFloat = 44

    var body: some View {
        VStack(spacing: 0) {
            HSplitView {
                treeArea
                inspector
                    .frame(minWidth: 260, idealWidth: 300, maxWidth: 420)
            }
            Divider()
            controls
        }
    }

    // MARK: Tree

    private var layout: TreeLayout? {
        guard derivations.indices.contains(index) else { return nil }
        return TreeLayout(root: derivations[index], collapsed: collapsed)
    }

    private func canvasPoint(_ x: CGFloat, _ y: CGFloat) -> CGPoint {
        CGPoint(x: margin + (x + 0.5) * cell.width * zoom,
                y: margin + (y + 0.5) * cell.height * zoom)
    }

    private func contentSize(_ layout: TreeLayout) -> CGSize {
        CGSize(width: margin * 2 + layout.columns * cell.width * zoom,
               height: margin * 2 + layout.rows * cell.height * zoom)
    }

    /// The paths from the root down to the selected node, used to light up that branch.
    private var ancestry: Set<String> {
        guard let selection else { return [] }
        var result = Set<String>()
        var parts = selection.split(separator: ".").map(String.init)
        while !parts.isEmpty {
            result.insert(parts.joined(separator: "."))
            parts.removeLast()
        }
        return result
    }

    @ViewBuilder
    private var treeArea: some View {
        if let layout {
            let size = contentSize(layout)
            ScrollView([.horizontal, .vertical]) {
                ZStack(alignment: .topLeading) {
                    Canvas { context, _ in
                        for edge in layout.edges {
                            var path = Path()
                            path.move(to: canvasPoint(edge.from.x, edge.from.y))
                            path.addLine(to: canvasPoint(edge.to.x, edge.to.y))
                            let lit = ancestry.contains(edge.childPath)
                            context.stroke(path,
                                           with: .color(lit ? .accentColor : .secondary.opacity(0.4)),
                                           lineWidth: lit ? 2 : 1)
                        }
                    }
                    .frame(width: size.width, height: size.height)
                    // The badges sit above this layer and carry their own gestures, so a tap
                    // that reaches the canvas is a tap on the background.
                    .contentShape(Rectangle())
                    .onTapGesture(perform: resetDiagram)

                    ForEach(layout.nodes) { node in
                        NodeBadge(node: node,
                                  isSelected: selection == node.id,
                                  onBranch: ancestry.contains(node.id),
                                  zoom: zoom,
                                  select: { selection = node.id },
                                  toggle: { toggle(node) })
                            .position(canvasPoint(node.x, node.y))
                    }
                }
                .frame(width: size.width, height: size.height)
                .animation(.easeInOut(duration: 0.22), value: collapsed)
            }
            // Covers the part of the viewport the content does not reach.
            .background(Color(.textBackgroundColor).onTapGesture(perform: resetDiagram))
        } else {
            ZStack {
                Color(.textBackgroundColor)
                Text("No derivation to show")
                    .foregroundStyle(.secondary)
            }
            .frame(minWidth: 420, minHeight: 300)
        }
    }

    private func toggle(_ node: TreeLayout.Node) {
        guard node.hasChildren else { return }
        if collapsed.contains(node.id) {
            collapsed.remove(node.id)
        } else {
            collapsed.insert(node.id)
        }
    }

    private func resetView() {
        collapsed.removeAll()
        selection = nil
    }

    /// Clicking the background puts the tree back as the parse left it. The derivation index
    /// is deliberately left alone: which of several derivations you are looking at is chosen
    /// in the strip below, and a stray click should not navigate away from it.
    private func resetDiagram() {
        resetView()
        zoom = 1
    }

    // MARK: Controls

    /// The input with the selected node's span highlighted, alongside the controls that act
    /// on this canvas — one strip, as in the other two diagrams.
    private var controls: some View {
        let span = selectedNode.map { ($0.derivation.from, $0.derivation.to) }
        return HStack(spacing: 8) {
            Text("input").font(.system(size: 10, weight: .semibold)).foregroundStyle(.secondary)
            HStack(spacing: 1) {
                ForEach(Array(input.enumerated()), id: \.offset) { offset, character in
                    let covered = span.map { offset >= $0.0 && offset < $0.1 } ?? false
                    Text(String(character))
                        .font(.system(size: 13).monospaced())
                        .frame(width: 17, height: 24)
                        .background(RoundedRectangle(cornerRadius: 3)
                            .fill(covered ? Color.accentColor.opacity(0.3) : Color.secondary.opacity(0.1)))
                }
                if let span, span.0 == span.1 {
                    // A zero-width span (ε, or a nonterminal deriving nothing) has no character
                    // to highlight, so mark the position it sits at instead.
                    Text("‸")
                        .font(.system(size: 13).monospaced())
                        .foregroundStyle(Color.accentColor)
                }
            }
            if let span {
                Text(span.0 == span.1 ? "at \(span.0)" : "[\(span.0), \(span.1))")
                    .font(.system(size: 10).monospaced())
                    .foregroundStyle(.secondary)
            }

            Spacer()

            if derivations.count > 1 {
                HStack(spacing: 6) {
                    Button { step(-1) } label: { Image(systemName: "chevron.left") }
                    Text("derivation \(index + 1) of \(derivations.count)")
                        .font(.system(size: 11).monospaced())
                    Button { step(1) } label: { Image(systemName: "chevron.right") }
                }
            }

            Button("Expand All") { collapsed.removeAll() }
                .disabled(collapsed.isEmpty)

            ZoomStrip(zoom: $zoom)
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
    }

    private func step(_ delta: Int) {
        index = (index + delta + derivations.count) % derivations.count
        resetView()
    }

    // MARK: Inspector

    private var selectedNode: TreeLayout.Node? {
        guard let selection, let layout else { return nil }
        return layout.nodes.first { $0.id == selection }
    }

    @ViewBuilder
    private var inspector: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 14) {
                if let node = selectedNode {
                    let d = node.derivation

                    InspectorSection("Node") {
                        InspectorRow("symbol", String(d.grammarNode.name))
                        InspectorRow("kind", "\(d.kind)")
                        InspectorRow("grammar node", "#\(d.grammarNode.number)")
                        if !d.isTerminal {
                            InspectorRow("production", d.grammarNode.production)
                        }
                    }

                    InspectorSection("Span") {
                        InspectorRow("extent", "[\(d.from), \(d.to))")
                        InspectorRow("length", "\(d.to - d.from)")
                        InspectorRow("image", d.image.isEmpty ? "⟨empty⟩" : "\"\(d.image)\"")
                    }

                    InspectorSection("Subtree") {
                        InspectorRow("children", "\(d.children.count)")
                        InspectorRow("nodes", "\(d.subtreeCount)")
                        if d.isAmbiguous {
                            Text("This span is derivable in more than one way — step through the derivations below to see the alternatives.")
                                .font(.system(size: 11))
                                .foregroundStyle(.orange)
                        }
                    }

                    InspectorSection("BSR yields  (i:k:j)") {
                        let spans = yields.indices.contains(d.grammarNode.number)
                            ? yields[d.grammarNode.number].sorted()
                            : []
                        if spans.isEmpty {
                            Text("none").font(.system(size: 11).monospaced()).foregroundStyle(.secondary)
                        } else {
                            ForEach(spans, id: \.self) { span in
                                let isThisOne = (span.k == d.from || span.i == d.from) && span.j == d.to
                                Text(span.description)
                                    .font(.system(size: 11).monospaced())
                                    .foregroundStyle(isThisOne ? Color.accentColor : .secondary)
                            }
                        }
                    }
                } else {
                    Text("Select a node")
                        .foregroundStyle(.secondary)
                    Text("Click to inspect. Double-click a nonterminal to collapse or expand its subtree.")
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

private struct NodeBadge: View {
    let node: TreeLayout.Node
    let isSelected: Bool
    let onBranch: Bool
    let zoom: Double
    let select: () -> Void
    let toggle: () -> Void

    var body: some View {
        let d = node.derivation

        HStack(spacing: 3) {
            Text(String(d.grammarNode.name))
                .font(.system(size: 13 * zoom, weight: d.isTerminal ? .regular : .semibold).monospaced())
            if node.isCollapsed {
                Text("\(d.subtreeCount)")
                    .font(.system(size: 9 * zoom).monospaced())
                    .padding(.horizontal, 3)
                    .background(Capsule().fill(.secondary.opacity(0.3)))
            }
        }
        .padding(.horizontal, 8 * zoom)
        .padding(.vertical, 4 * zoom)
        .diagramBadge(shape,
                      fill: fill,
                      stroke: stroke,
                      lineWidth: isSelected ? 2.5 : (d.isAmbiguous ? 2 : 1))
        .help(tooltip)
        .onTapGesture(count: 2) { toggle() }
        .onTapGesture { select() }
    }

    private var shape: AnyShape {
        node.derivation.isTerminal ? AnyShape(RoundedRectangle(cornerRadius: 4)) : AnyShape(Capsule())
    }

    private var fill: Color {
        if isSelected { return .accentColor.opacity(0.35) }
        if node.isCollapsed { return .secondary.opacity(0.22) }
        if node.derivation.kind == .EPS { return .secondary.opacity(0.1) }
        if node.derivation.isTerminal { return Color(.controlBackgroundColor) }
        return onBranch ? .accentColor.opacity(0.16) : .secondary.opacity(0.12)
    }

    private var stroke: Color {
        if isSelected { return .accentColor }
        if node.derivation.isAmbiguous { return .orange }
        return .secondary.opacity(0.5)
    }

    private var tooltip: String {
        let d = node.derivation
        var text = "\(d.grammarNode.name)  [\(d.from), \(d.to))"
        if !d.image.isEmpty { text += "  \"\(d.image)\"" }
        if d.isAmbiguous { text += "  — ambiguous" }
        if node.hasChildren { text += node.isCollapsed ? "  (collapsed)" : "" }
        return text
    }
}

#Preview("Derivation — ambiguous") {
    let result = ParseResult.previewAmbiguous
    DerivationDiagramView(derivations: result.derivations,
                          input: result.input,
                          yields: result.yields)
        .frame(width: 1000, height: 600)
}
