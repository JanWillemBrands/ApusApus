//
//  ExplorerView.swift
//  tinyGLL
//
//  The window around the diagrams: a grammar and an input to parse, a pane picker, and the
//  parse itself. Each pane is a self-contained view holding its own state —
//  DerivationDiagramView, GrammarDiagramView, StackDiagramView, TraceView.
//

import SwiftUI
import AppKit

// MARK: - Explorer

struct ExplorerView: View {

    @Environment(ParserModel.self) private var model

    @State private var pane = Pane.derivation

    enum Pane: String, CaseIterable, Identifiable {
        case derivation = "Derivation"
        case grammar = "Grammar"
        case stack = "Stack"
        case trace = "Trace"

        var id: Self { self }
    }

    var body: some View {
        VStack(spacing: 0) {
            controls
            Divider()
            switch pane {
            case .derivation:
                DerivationDiagramView(derivations: model.result.derivations,
                                      input: model.result.input,
                                      yields: model.result.yields)
                    .id(model.parseID)
            case .grammar:
                GrammarDiagramView(definitions: model.result.definitions,
                                   yields: model.result.yields)
            case .stack:
                StackDiagramView(snapshot: model.result.crf)
            case .trace:
                TraceView(text: model.result.trace)
            }
        }
        .task { model.parse() }
        .sheet(isPresented: Binding(get: { model.isShowingBenchmark },
                                    set: { model.isShowingBenchmark = $0 })) {
            BenchmarkSheet()
        }
        .alert("Something went wrong",
               isPresented: Binding(get: { model.toolError != nil },
                                    set: { if !$0 { model.toolError = nil } })) {
            Button("OK") { model.toolError = nil }
        } message: {
            Text(model.toolError ?? "")
        }
    }

    // MARK: Controls

    /// Only what is shared by all panes. Anything that acts on one canvas lives in that
    /// pane's own strip, next to the thing it acts on.
    private var controls: some View {
        VStack(spacing: 8) {
            HStack(spacing: 8) {
                Text("Grammar").foregroundStyle(.secondary)
                TextField("S = aS | ε .", text: Binding(get: { model.grammarText },
                                                        set: { model.grammarText = $0 }))
                    .font(.system(size: 12).monospaced())
                    .onSubmit { model.parse() }
                Text("Input").foregroundStyle(.secondary)
                TextField("aa", text: Binding(get: { model.inputText },
                                              set: { model.inputText = $0 }))
                    .font(.system(size: 12).monospaced())
                    .frame(width: 130)
                    .onSubmit { model.parse() }
                Button("Parse") { model.parse() }
            }

            HStack(spacing: 12) {
                Picker("", selection: $pane) {
                    ForEach(Pane.allCases) { Text($0.rawValue).tag($0) }
                }
                .pickerStyle(.segmented)
                .labelsHidden()
                .frame(width: 320)

                statusLabel

                Spacer()

                if let parserFile = model.generatedParser {
                    GeneratedParserLabel(url: parserFile)
                }
            }
        }
        .padding(10)
    }

    @ViewBuilder
    private var statusLabel: some View {
        switch model.status {
        case .idle:
            Label("not parsed", systemImage: "circle.dashed").foregroundStyle(.secondary)
        case .accepted(let count):
            Label(count > 1 ? "accepted — ambiguous, \(count) derivations" : "accepted",
                  systemImage: count > 1 ? "exclamationmark.triangle.fill" : "checkmark.circle.fill")
                .foregroundStyle(count > 1 ? .orange : .green)
        case .rejected:
            Label("rejected — no derivation covers the whole input", systemImage: "xmark.circle.fill")
                .foregroundStyle(.red)
        case .failed(let message):
            Label(message, systemImage: "exclamationmark.octagon.fill").foregroundStyle(.red)
        }
    }
}

// MARK: - Generated parser

/// Where Generate put the parser. The CLI printed the path; a window has somewhere better to
/// put it, and somewhere to click.
private struct GeneratedParserLabel: View {
    let url: URL

    var body: some View {
        HStack(spacing: 6) {
            Image(systemName: "swift").foregroundStyle(.secondary)
            Text(url.lastPathComponent)
                .font(.system(size: 11).monospaced())
                .help(url.path(percentEncoded: false))
            Button("Reveal") { NSWorkspace.shared.activateFileViewerSelecting([url]) }
                .buttonStyle(.link)
                .font(.system(size: 11))
        }
    }
}

// MARK: - Trace

/// The text the CLI's trace and tree modes printed to stdout: the grammar's link table, the
/// verdict, the start symbol's yields, and every derivation indented.
struct TraceView: View {
    let text: String

    var body: some View {
        ScrollView([.horizontal, .vertical]) {
            Text(text.isEmpty ? "Nothing parsed yet." : text)
                .font(.system(size: 11).monospaced())
                .textSelection(.enabled)
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(12)
        }
        .background(Color(.textBackgroundColor))
    }
}

// MARK: - Shared diagram chrome

// The three diagram panes are different pictures of the same parse, so they share an
// inspector, a zoom control and a node badge. Each used to carry its own copy, which is how
// they drifted apart — three label column widths, two zoom ranges, two hover scales.

/// A titled group of rows in a pane's inspector.
struct InspectorSection<Content: View>: View {
    let title: String
    @ViewBuilder let content: Content

    init(_ title: String, @ViewBuilder content: () -> Content) {
        self.title = title
        self.content = content()
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text(title.uppercased())
                .font(.system(size: 10, weight: .semibold))
                .foregroundStyle(.secondary)
            content
        }
    }
}

/// One `label  value` line. The value is monospaced and selectable, because it is almost
/// always something you want to copy into a grammar or a test.
struct InspectorRow: View {
    let label: String
    let value: String

    init(_ label: String, _ value: String) {
        self.label = label
        self.value = value
    }

    var body: some View {
        HStack(alignment: .firstTextBaseline, spacing: 6) {
            Text(label)
                .font(.system(size: 11))
                .foregroundStyle(.secondary)
                .frame(width: 92, alignment: .leading)
            Text(value.isEmpty ? "—" : value)
                .font(.system(size: 11).monospaced())
                .textSelection(.enabled)
        }
    }
}

/// The zoom slider every canvas carries at the bottom right.
struct ZoomStrip: View {
    @Binding var zoom: Double

    var body: some View {
        HStack(spacing: 4) {
            Image(systemName: "minus.magnifyingglass").foregroundStyle(.secondary)
            Slider(value: $zoom, in: 0.6...2.0).frame(width: 100)
            Image(systemName: "plus.magnifyingglass").foregroundStyle(.secondary)
        }
    }
}

extension View {
    /// The common look of a node badge on a canvas: an opaque backdrop, one or two fills, a
    /// stroke, and a nudge on hover.
    ///
    /// The backdrop is the part that matters. Badges are layered over the edge lines, so
    /// without repainting the canvas colour underneath them the lines run straight through
    /// the label. `under` is painted between backdrop and fill, for the grammar diagram's
    /// cluster tint, so an opaque node still matches the box it stands on.
    func diagramBadge(_ shape: AnyShape,
                      fill: Color,
                      under: Color? = nil,
                      stroke: Color,
                      lineWidth: CGFloat) -> some View {
        modifier(DiagramBadge(shape: shape, fill: fill, under: under,
                              stroke: stroke, lineWidth: lineWidth))
    }
}

private struct DiagramBadge: ViewModifier {
    let shape: AnyShape
    let fill: Color
    let under: Color?
    let stroke: Color
    let lineWidth: CGFloat

    @State private var hovering = false

    func body(content: Content) -> some View {
        content
            .background {
                shape.fill(Color(.textBackgroundColor))
                if let under { shape.fill(under) }
                shape.fill(fill)
            }
            .overlay(shape.stroke(stroke, lineWidth: lineWidth))
            .scaleEffect(hovering ? 1.08 : 1.0)
            .animation(.easeOut(duration: 0.12), value: hovering)
            .onHover { hovering = $0 }
    }
}

// MARK: - Menu commands

/// Parse, Generate and Benchmark as menu items. The old CLI chose between these with
/// --flags, and the first explorer hand-built an NSMenu just to get ⌘Q and ⌘C back.
struct ParserCommands: Commands {

    let model: ParserModel

    var body: some Commands {
        CommandMenu("Parse") {
            Button("Parse") { model.parse() }
                .keyboardShortcut("r")

            Divider()

            Button("Generate Parser…") { model.generateParser() }
                .keyboardShortcut("g")
                .disabled(!model.canGenerate)

            Button("Benchmark…") { model.isShowingBenchmark = true }
        }
    }
}

#Preview {
    ExplorerView()
        .environment(ParserModel(defaults: .tinyGLLPreview))
        .frame(width: 1000, height: 700)
}

#Preview("Grammar error") {
    let model = ParserModel(defaults: .tinyGLLPreview)
    model.grammarText = "S = a"        // no closing '.', so the reader throws
    model.inputText = "a"
    return ExplorerView()
        .environment(model)
        .frame(width: 1000, height: 420)
}
