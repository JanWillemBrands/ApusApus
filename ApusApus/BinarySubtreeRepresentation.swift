//
//  BinarySubtreeRepresentation.swift
//  ApusApus
//
//  Created by Johannes Brands on 27/04/2025.
//

import Foundation

struct BinarySpan: Hashable, Comparable, CustomStringConvertible {
    let i: CharPosition  // left extent
    let k: CharPosition  // pivot
    let j: CharPosition  // right extent
    var description: String { "\(i):\(k):\(j)" }

    static func < (lhs: BinarySpan, rhs: BinarySpan) -> Bool {
        if lhs.i != rhs.i { return lhs.i < rhs.i }
        if lhs.k != rhs.k { return lhs.k < rhs.k }
        return lhs.j < rhs.j
    }
}

// MARK: - MessageParser BSR Operations

extension MessageParser {

    // Paper: bsrAdd(X ::= α·β, i, k, j) — add BSR element to the yield
    func addYield(L: GrammarNode, i: CharPosition, k: CharPosition, j: CharPosition) {
        let triple = BinarySpan(i: i, k: k, j: j)
        if yields[L.number].insert(triple).inserted {
            yieldCount += 1
        }
    }
}

// MARK: - YieldNavigator
//
// One indexed implementation of "where can this symbol end when it starts here?" over the BSR
// yields. The Oracle's dead-wood walk, the DerivationBuilder and the SwiftSyntax converter each
// had their own copy (TODO.md item 7), with different indexing (the converter still scanned every
// yield of the symbol per query — the quadratic pattern the Oracle lost on 2026-09-26) and one
// semantic drift (the converter lacked the annotated-bracket branch).
//
// A navigator is a SNAPSHOT: it indexes yields lazily, the first time a symbol is asked about, and
// never looks again. Create a fresh one whenever the yields may have changed (the Oracle does, once
// per `pruneUnproductive` pass); the builder and converter run after the Oracle and keep theirs.

final class YieldNavigator {
    private struct NodePos: Hashable { let id: ObjectIdentifier; let from: CharPosition }
    private struct IJ: Hashable { let a, b: CharPosition }
    private struct SymbolIndex {
        var endsByI: [CharPosition: Set<CharPosition>] = [:]   // i → { j }
        var endsByK: [CharPosition: Set<CharPosition>] = [:]   // k → { j }
        var spansIJ: Set<IJ> = []
        var spansKJ: Set<IJ> = []
    }

    private let parser: MessageParser
    private var indexes: [Int: SymbolIndex] = [:]
    private var endCache: [NodePos: Set<CharPosition>] = [:]
    private var endGuard: Set<NodePos> = []

    init(parser: MessageParser) {
        self.parser = parser
    }

    private func index(_ sym: GrammarNode) -> SymbolIndex {
        if let cached = indexes[sym.number] { return cached }
        var x = SymbolIndex()
        for y in parser.yield(of: sym) {
            x.endsByI[y.i, default: []].insert(y.j)
            x.endsByK[y.k, default: []].insert(y.j)
            x.spansIJ.insert(IJ(a: y.i, b: y.j))
            x.spansKJ.insert(IJ(a: y.k, b: y.j))
        }
        indexes[sym.number] = x
        return x
    }

    /// Ends of `sym`'s yields that START at `from` (`i == from`) — an LHS derivation.
    func ends(of sym: GrammarNode, startingAt from: CharPosition) -> Set<CharPosition> {
        index(sym).endsByI[from] ?? []
    }

    /// Ends of `sym`'s yields whose PIVOT is `from` (`k == from`) — an RHS occurrence / slot.
    func ends(of sym: GrammarNode, pivot from: CharPosition) -> Set<CharPosition> {
        index(sym).endsByK[from] ?? []
    }

    /// Is there a yield of `sym` spanning exactly `[i, j]`?
    func hasSpan(_ sym: GrammarNode, i: CharPosition, j: CharPosition) -> Bool {
        index(sym).spansIJ.contains(IJ(a: i, b: j))
    }

    /// Is there a yield of `sym` with pivot `k` ending at `j`?
    func hasPivotSpan(_ sym: GrammarNode, k: CharPosition, j: CharPosition) -> Bool {
        index(sym).spansKJ.contains(IJ(a: k, b: j))
    }

    /// End positions reachable from `sym` starting at `from`.
    ///
    /// Memoised per (symbol, position). The recursion guard returns `[]` for a query that is
    /// already on the stack (left-recursive closures); that behaviour is inherited unchanged from
    /// the three implementations this replaces.
    func endPositions(_ sym: GrammarNode, from: CharPosition) -> Set<CharPosition> {
        let key = NodePos(id: ObjectIdentifier(sym), from: from)
        if let cached = endCache[key] { return cached }
        guard endGuard.insert(key).inserted else { return [] }
        defer { endGuard.remove(key) }

        let result: Set<CharPosition>
        switch sym.kind {
        case .T, .TI, .C, .B:
            result = ends(of: sym, pivot: from)
        case .N:
            if sym.isRHS {
                guard let lhs = sym.alt else { return [] }
                result = ends(of: sym, pivot: from).intersection(ends(of: lhs, startingAt: from))
            } else {
                result = ends(of: sym, startingAt: from)
            }
        case .DO, .OPT, .KLN, .POS:
            if sym.disambiguation != nil {
                // ANNOTATED bracket (@longest/@shortest): read its OWN (Oracle-prunable) yields so
                // the extent prune is honoured. A bracket is an RHS occurrence — yields are
                // `(alternate-start, k = bracket-start, j)` — so filter on the pivot.
                result = ends(of: sym, pivot: from)
            } else {
                var positions = Set<CharPosition>()
                if sym.kind == .KLN || sym.kind == .OPT { positions.insert(from) }
                if sym.kind.isClosure {
                    var visited = Set<CharPosition>()
                    var queue = [from]
                    var head = 0
                    while head < queue.count {
                        let pos = queue[head]
                        head += 1
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

    /// End positions of ONE iteration of `bracket` (one alternate of its body) starting at `from`.
    func iterationEndPositions(_ bracket: GrammarNode, from: CharPosition) -> Set<CharPosition> {
        var positions = Set<CharPosition>()
        var alt = bracket.alt
        while let a = alt {
            var frontier: Set<CharPosition> = [from]
            var consumedSymbol = false
            for sym in a.bodySymbols where sym.kind != .EPS {
                consumedSymbol = true
                frontier = frontier.reduce(into: Set()) { $0.formUnion(endPositions(sym, from: $1)) }
                if frontier.isEmpty { break }
            }
            positions.formUnion(consumedSymbol ? frontier : [from])
            alt = a.alt
        }
        return positions
    }
}
