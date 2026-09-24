//
//  BenchmarkSheet.swift
//  tinyGLL
//
//  The interpreted-vs-compiled sweep, which the CLI wrote to stdout as bare numbers so they
//  pasted into a spreadsheet. The table is the readable version; Copy as TSV keeps the paste.
//

import SwiftUI
import AppKit

struct BenchmarkSheet: View {

    @Environment(ParserModel.self) private var model
    @Environment(\.dismiss) private var dismiss

    @State private var maxLength = Benchmark.defaultMaxLength

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            header
            Divider()
            content
            Divider()
            footer
        }
        .frame(width: 560, height: 520)
    }

    // MARK: Header

    private var header: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("Benchmark").font(.headline)
            Text("Parses \"b\" × n against \(Benchmark.syntax.trimmingCharacters(in: .whitespaces)) for n in 1…\(maxLength), interpreted and compiled. Only the descriptor loop is timed.")
                .font(.system(size: 11))
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)

            HStack(spacing: 8) {
                Stepper("lengths 1…\(maxLength)", value: $maxLength, in: 1...400, step: 10)
                    .font(.system(size: 11))
                    .disabled(model.isBenchmarking)
                Spacer()
                Button(model.benchmark == nil ? "Run" : "Run Again") {
                    Task { await model.runBenchmark(maxLength: maxLength) }
                }
                .disabled(model.isBenchmarking)
            }
        }
        .padding(12)
    }

    // MARK: Content

    @ViewBuilder
    private var content: some View {
        if model.isBenchmarking {
            centred {
                ProgressView("Sweeping 1…\(maxLength), and compiling the generated parser")
                    .font(.system(size: 11))
            }
        } else if let report = model.benchmark {
            Table(report.rows) {
                TableColumn("n") { Text("\($0.length)").monospaced() }
                    .width(44)
                TableColumn("interpreted (s)") { Text(seconds($0.interpreted)).monospaced() }
                TableColumn("compiled (s)") { row in
                    Text(row.compiled.map(seconds) ?? "—").monospaced()
                }
            }
        } else {
            centred {
                Text("Not run yet. A debug build measures Swift's bounds and retain checks rather than the parser, so the numbers are only meaningful from a release build.")
                    .font(.system(size: 11))
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: 360)
            }
        }
    }

    @ViewBuilder
    private func centred<Content: View>(@ViewBuilder content: () -> Content) -> some View {
        VStack { Spacer(); content(); Spacer() }
            .frame(maxWidth: .infinity)
    }

    // MARK: Footer

    private var footer: some View {
        HStack(spacing: 10) {
            if let report = model.benchmark {
                VStack(alignment: .leading, spacing: 2) {
                    Text(totals(report))
                        .font(.system(size: 11).monospaced())
                    if report.compiledTotal == nil {
                        Text("compiled column skipped — swiftc unavailable, or the generated source did not build")
                            .font(.system(size: 10))
                            .foregroundStyle(.secondary)
                    }
                    if !report.rejected.isEmpty {
                        Text("rejected at lengths \(report.rejected.map(String.init).joined(separator: ", "))")
                            .font(.system(size: 10))
                            .foregroundStyle(.red)
                    }
                }
            }

            Spacer()

            if let report = model.benchmark {
                Button("Copy as TSV") { copy(report.tsv) }
            }
            Button("Done") { dismiss() }
                .keyboardShortcut(.defaultAction)
        }
        .padding(12)
    }

    private func totals(_ report: BenchmarkReport) -> String {
        var text = String(format: "interpreted %.4fs", report.interpretedTotal)
        if let compiledTotal = report.compiledTotal {
            text += String(format: "   compiled %.4fs", compiledTotal)
        }
        if let speedup = report.speedup {
            text += String(format: "   speedup %.2fx", speedup)
        }
        return text
    }

    private func seconds(_ value: Double) -> String {
        String(format: "%.6f", value)
    }

    /// Writing to the pasteboard has no SwiftUI equivalent — `.copyable` needs the content to
    /// be a selection in the view, and this is a whole-report action on a button.
    private func copy(_ text: String) {
        NSPasteboard.general.clearContents()
        NSPasteboard.general.setString(text, forType: .string)
    }
}

#Preview {
    BenchmarkSheet()
        .environment(ParserModel(defaults: .tinyGLLPreview))
}
