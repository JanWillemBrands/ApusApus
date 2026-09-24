//
//  CallReturnForest.swift
//  ApusApus
//
//  Created by Johannes Brands on 29/04/2025.
//

// "Derivation representation using binary subtree sets"
// https://pure.royalholloway.ac.uk/ws/portalfiles/portal/33174042/Accepted_Manuscript.pdf

// Paper: CRF = Call Return Forest
// Paper: P = contingent return set (pops)
// Paper: cL = current grammar slot, cI = current input index, cU = current cluster index

import OSLog
import Foundation


// Lightweight value type for CRF dictionary keys and return edges.
// Matches the paper's crfNode (L, i).
struct ParsePosition: Hashable, Comparable, CustomStringConvertible {
    let slot: GrammarNode
    let index: CharPosition

    var description: String { "\(slot).\(index)" }
    var ebnfDot: String { "\(slot.ebnfDot()),\(index)" }

    static func < (lhs: ParsePosition, rhs: ParsePosition) -> Bool {
        lhs.description < rhs.description
    }
}

// Cluster node in the CRF. Mutable, identity-based.
// Represents clusterNode (X, k) from the paper. The (X, k) label is the `crf`
// dictionary key (a ParsePosition), so it is not duplicated here — what a cluster
// adds over its identity is these two sets.
final class ParseCluster {
    var returns: Set<ParsePosition> = []
    var pops: Set<CharPosition> = []   // Paper: P — contingent returns
}


// MARK: - MessageParser CRF Operations

extension MessageParser {

    // Paper: ntAdd(X, j) — add descriptors for all alternates of a bracket/nonterminal
    func addDescriptorsForAlternates(X: GrammarNode, k: CharPosition, i: CharPosition) {
        assert([.N, .DO, .OPT, .ALT, .KLN, .POS].contains(X.kind), "Called \(#function) on a GrammarNode \(X) which is not a bracket")
        var selectedAlternate = false
        var current = X.alt
        while let alt = current {
            if testSelect(slot: alt, bracket: X) {
                selectedAlternate = true
                addDescriptor(L: alt.seq!, k: k, i: i)
            }
            current = alt.alt
        }

        if !selectedAlternate, X.kind == .N {
            recordMismatch(expected: X.first, at: i, slot: X)
        }
    }

    // Paper: call(L, i, j) — enter a nonterminal (paper §5.3.1, where "L is Y ::= αX·β":
    // the slot with the dot AFTER the called nonterminal). The paper labels both the CRF
    // node and the BSR element with that slot.
    //
    // The return edge here stores the RHS nonterminal node itself — the dot BEFORE — so
    // that one stored node serves both uses on the way back out (see rtn):
    //   edge.slot        is the yield key   (paper: bsrAdd(L, ...))
    //   edge.slot.seq!   is the paper's L   (paper: dscAdd(L, ...))
    // Storing the paper's L instead would need a backward link to recover the nonterminal
    // for the yield. node ↔ node.seq is a bijection, so this is a relabeling, not a
    // difference — but note that yields are therefore keyed one `.seq` link earlier than
    // the BSR elements in the paper's worked examples.
    func call() {
        // cL points to the RHS nonterminal node
        // cL.alt points to the LHS nonterminal node

        // Create the return edge: (L=cL, i=cU)
        let returnEdge = ParsePosition(slot: cL, index: cU)

        // Find or create the cluster node for (X=cL.alt!, k=cI)
        let clusterKey = ParsePosition(slot: cL.alt!, index: cI)

        if let existingCluster = crf[clusterKey] {
            if existingCluster.returns.insert(returnEdge).inserted {
                for pop in existingCluster.pops {
                    if continuationViable(continuation: cL.seq!, at: pop) {
                        addDescriptor(L: cL.seq!, k: cU, i: pop)
                        addYield(L: cL, i: cU, k: cI, j: pop)
                    } else {
                        recordSuppressedContinuation(cL.seq!, at: pop)
                        suppressedDescriptorCount += 1
                    }
                }
            }
        } else {
            let newCluster = ParseCluster()
            crf[clusterKey] = newCluster
            newCluster.returns.insert(returnEdge)
            addDescriptorsForAlternates(X: cL.alt!, k: cI, i: cI)
        }
    }

    // Paper: rtn(X, k, j) — return from a nonterminal
    func rtn(X: GrammarNode) {
        let clusterKey = ParsePosition(slot: X, index: cU)
        guard let cluster = crf[clusterKey] else { return }

        if cluster.pops.insert(cI).inserted {
            for returnEdge in cluster.returns {
                if continuationViable(continuation: returnEdge.slot.seq!, at: cI) {
                    addDescriptor(L: returnEdge.slot.seq!, k: returnEdge.index, i: cI)
                    addYield(L: returnEdge.slot, i: returnEdge.index, k: cU, j: cI)
                } else {
                    recordSuppressedContinuation(returnEdge.slot.seq!, at: cI)
                    suppressedDescriptorCount += 1
                }
            }
        }
    }

    // bracketCall — enter a bracket (DO, OPT, KLN, POS)
    // Similar to call() but the bracket node IS the "nonterminal" — no indirection through .alt
    func bracketCall(bracket: GrammarNode) {
        let returnEdge = ParsePosition(slot: bracket, index: cU)
        let clusterKey = ParsePosition(slot: bracket, index: cI)

        if let existingCluster = crf[clusterKey] {
            if existingCluster.returns.insert(returnEdge).inserted {
                for pop in existingCluster.pops {
                    if continuationViable(continuation: bracket.seq!, at: pop) {
                        addDescriptor(L: bracket.seq!, k: cU, i: pop)
                        addYield(L: bracket, i: cU, k: cI, j: pop)
                    } else {
                        recordSuppressedContinuation(bracket.seq!, at: pop)
                        suppressedDescriptorCount += 1
                    }
                }
            }
        } else {
            let newCluster = ParseCluster()
            crf[clusterKey] = newCluster
            newCluster.returns.insert(returnEdge)
            addDescriptorsForAlternates(X: bracket, k: cI, i: cI)
        }
    }

    // bracketRtn — return from a bracket
    // Similar to rtn() but also handles KLN/POS re-entry
    func bracketRtn(bracket: GrammarNode) {
        let clusterKey = ParsePosition(slot: bracket, index: cU)
        guard let cluster = crf[clusterKey] else { return }

        if cluster.pops.insert(cI).inserted {
            for returnEdge in cluster.returns {
                if continuationViable(continuation: returnEdge.slot.seq!, at: cI) {
                    addYield(L: returnEdge.slot, i: returnEdge.index, k: cU, j: cI)
                    addDescriptor(L: returnEdge.slot.seq!, k: returnEdge.index, i: cI)
                } else {
                    recordSuppressedContinuation(returnEdge.slot.seq!, at: cI)
                    suppressedDescriptorCount += 1
                }
            }

            if bracket.kind.isClosure {
                // KLN/POS re-entry: iterate the body from `cI`, returning to the SAME
                // cluster (`k = cU`, the closure's start). One CRF node per closure —
                // the native-EBNF model (GLL Syntax Analysers for EBNF Grammars §4.3:
                // a single GSS node, looped, `pop` offered each iteration). Replaces
                // the old per-iteration cluster + `returns` snapshot, which cost O(N)
                // CRF nodes AND was order-dependent (the snapshot missed return edges
                // that arrived after it). The DerivationBuilder reconstructs iteration
                // boundaries by re-tiling the BODY yields, so it never reads the
                // closure node's own yields — this change is tree-invariant.
                addDescriptorsForAlternates(X: bracket, k: cU, i: cI)
            }
        }
    }
}
