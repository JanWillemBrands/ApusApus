//
//  Descriptor.swift
//  ApusApus
//
//  Created by Johannes Brands on 29/04/2025.
//

import OSLog
import Foundation
import BitCollections

// The same letters mean different things in a descriptor and in a BinarySpan:
//   descriptor  (L, k, i):  k = cluster index,  i = input index
//   BinarySpan  (i, k, j):  i = left extent,    k = pivot,  j = right extent
// A descriptor's `k` therefore becomes a span's `i`, which is why the yields are
// added as addYield(L: cL, i: cU, k: cI, ...) — the swap is deliberate.

// Paper: descriptor = (L, k, i) — grammar slot, cluster index, input index
struct Descriptor: Hashable {
    let L: GrammarNode          // grammar slot
    let k: CharPosition         // cluster index
    let i: CharPosition         // input index
}   // this is three 64-bit words (24 bytes)
// TODO: pack the descriptor and simplify the hash: L.id << 48 | k << 24 | i.
// (Tried 2026-11-18 with fixed 16/24/24 widths: no measurable gain. Descriptor bookkeeping was
// ≈ 4% of a parse, and `Set` hashes the one word with SipHash all the same.)

// MARK: - MessageParser Descriptor Operations

extension MessageParser {

    // Paper: dscAdd(L, k, i)
    func addDescriptor(L: GrammarNode, k: CharPosition, i: CharPosition) {
        let d = Descriptor(L: L, k: k, i: i)
        if unique.insert(d).inserted {
            remaining.append(d)
            descriptorCount += 1
        } else {
            duplicateDescriptorCount += 1
        }
    }

    // Paper: get next descriptor from R
    func getDescriptor() -> Bool {
        if remaining.isEmpty {
            return false
        } else {
            let d = remaining.removeLast()
            cL = d.L
            cU = d.k
            cI = d.i
            return true
        }
    }
}

// MARK: - Decision statistics (`APUS_DECISION_STATS=1`)
//  `APUS_DECISION_STATS=1`: how LL(1)-like a parse was, decision by decision.
//  A decision is a call of a nonterminal or bracket at a position where `viable` let more
//  than one alternative through. GLL then runs them all; the ones that never complete are the
//  work a better prediction could save. After the parse (before the Oracle), each such
//  alternative is followed through its own yields from the decision point: did it complete, and
//  if not, how many tokens did it read before it died? A loser that read at most one token can
//  in principle be told apart by two tokens of lookahead (an upper bound for static LL(2) sets,
//  which also approximate the context).
//  Off by default; the hook in `addDescriptorsForAlternates` costs one flag test when unset.

/// `APUS_DECISION_STATS=1` — record multi-alternative decisions for `decisionStatistics()`.
nonisolated(unsafe) var decisionStats =
    ProcessInfo.processInfo.environment["APUS_DECISION_STATS"] == "1"

/// One call where more than one alternative passed `viable`.
struct Decision {
    let owner: GrammarNode
    let position: CharPosition
    let alternatives: [GrammarNode]
}

/// What happened to one alternative of a decision.
struct AlternativeFate {
    /// The alternative read its whole body from the decision point.
    let completed: Bool
    /// Tokens it read from the decision point before it stopped (for a survivor: in its longest reading).
    let tokensRead: Int
    /// Yields of its body that it produced from the decision point.
    let yields: Int
    /// For a loser: the body symbol at which no reading continued.
    var stoppedAt: GrammarNode? = nil
}

/// Aggregated over a parse, and per decision site.
struct DecisionReport {
    var calls = 0                 // calls that selected at least one alternative
    var multiCalls = 0            // calls that selected more than one
    var selectedAlternatives = 0  // alternatives selected in multi calls
    var losers = 0                // selected alternatives that never completed
    var loserYields = 0           // yields produced by losers (wasted BSR work)
    var allSurvive = 0            // multi calls where every selected alternative completed
    /// Losers by tokens read before they died: index 0, 1, 2, 3; index 4 is 4 or more.
    var loserTokens = [Int](repeating: 0, count: 5)
    /// Per site (owner node number): multi calls, losers, losers that read ≤ 1 token.
    var sites: [Int: (name: String, multi: Int, losers: Int, shortLosers: Int, loserYields: Int)] = [:]
    /// Zero-token losers by (site, symbol where they stopped): which first steps `viable` let through in vain.
    var zeroStops: [String: Int] = [:]

    func summary(top: Int = 25) -> String {
        func pct(_ a: Int, _ b: Int) -> String { b == 0 ? "-" : String(format: "%.1f%%", 100.0 * Double(a) / Double(b)) }
        var s = ""
        s += "decisions: \(calls) calls, \(multiCalls) with >1 alternative (\(pct(multiCalls, calls)))\n"
        s += "  alternatives selected there: \(selectedAlternatives), losers: \(losers) (\(pct(losers, selectedAlternatives))), "
        s += "every alternative survived: \(allSurvive) calls\n"
        s += "  loser yields (wasted BSR work): \(loserYields)\n"
        let short = loserTokens[0] + loserTokens[1]
        s += "  losers by tokens read before dying: 0: \(loserTokens[0])  1: \(loserTokens[1])  2: \(loserTokens[2])  3: \(loserTokens[3])  4+: \(loserTokens[4])\n"
        s += "  losers LL(2) could cut at best (read ≤ 1 token): \(short) (\(pct(short, losers)))\n"
        s += "top sites by losers:\n"
        let ranked = sites.values.sorted { ($0.losers, $0.multi) > ($1.losers, $1.multi) }.prefix(top)
        for site in ranked {
            s += "  \(site.name): multi \(site.multi), losers \(site.losers), ≤1 token \(site.shortLosers) (\(pct(site.shortLosers, site.losers))), loser yields \(site.loserYields)\n"
        }
        s += "zero-token losers by where they stopped (site ← symbol kind name):\n"
        for (key, n) in zeroStops.sorted(by: { $0.value > $1.value }).prefix(top) { s += "  \(n)  \(key)\n" }
        return s
    }
}

extension MessageParser {

    /// Record a decision; called from `addDescriptorsForAlternates` when `decisionStats` is on.
    func recordDecision(owner: GrammarNode, position: CharPosition, selected: [GrammarNode]) {
        guard currentParseRoot === grammar.root else { return }
        if selected.isEmpty { emptyCalls.insert(ParsePosition(slot: owner, index: position)); return }
        decisionCalls += 1
        if selected.count > 1 {
            decisionLog.append(Decision(owner: owner, position: position, alternatives: selected))
        }
    }

    /// Follow one alternative from `start` through its body symbols' yields: the frontier after
    /// each symbol is the set of ends of that symbol's yields that start (pivot `k`) on the
    /// previous frontier. The context start `i` is not checked (a loop round's yields carry the
    /// loop's start), so this can over-approximate when the same slot is used at the same pivot in
    /// another context; for statistics that is fine.
    func fate(of alternative: GrammarNode, from start: CharPosition, tokenEnds: [CharPosition]) -> AlternativeFate {
        let body = alternative.bodySymbols
        var frontier: Set<CharPosition> = [start]
        var reach = start
        var yieldsSeen = 0
        for symbol in body {
            var next = Set<CharPosition>()
            for y in yields[symbol.number] where frontier.contains(y.k) {
                next.insert(y.j)
                yieldsSeen += 1
                if y.j > reach { reach = y.j }
            }
            if next.isEmpty {
                return AlternativeFate(completed: false, tokensRead: tokens(from: start, to: reach, tokenEnds), yields: yieldsSeen, stoppedAt: symbol)
            }
            frontier = next
        }
        return AlternativeFate(completed: true, tokensRead: tokens(from: start, to: reach, tokenEnds), yields: yieldsSeen)
    }

    /// Distinct token ends in (from, to].
    private func tokens(from: CharPosition, to: CharPosition, _ ends: [CharPosition]) -> Int {
        guard to > from else { return 0 }
        // `ends` is sorted: count the ends e with from < e <= to.
        func firstIndex(after p: CharPosition) -> Int {
            var lo = 0, hi = ends.count
            while lo < hi { let mid = (lo + hi) / 2; if ends[mid] <= p { lo = mid + 1 } else { hi = mid } }
            return lo
        }
        return firstIndex(after: to) - firstIndex(after: from)
    }

    /// The statistics of the last full parse. Read them before the Oracle runs: it removes yields.
    func decisionStatistics() -> DecisionReport {
        var report = DecisionReport()
        report.calls = decisionCalls
        let tokenEnds = Array(Set(commits.map(\.triviaEnd))).sorted()
        // Name each site: a nonterminal by itself, a bracket by its kind, number and production.
        var production = [Int: String]()
        var seen = Set<Int>()
        func walk(_ node: GrammarNode?, in name: String) {
            guard let node, seen.insert(node.number).inserted else { return }
            production[node.number] = name
            if node.kind != .END { walk(node.seq, in: name) }
            if !node.isRHS { walk(node.alt, in: name) }
        }
        for nt in grammar.allProductions { walk(nt, in: nt.name) }
        func siteName(_ owner: GrammarNode) -> String {
            owner.kind == .N ? owner.name : "\(owner.kind)#\(owner.number) in \(production[owner.number] ?? "?")"
        }
        for decision in decisionLog {
            report.multiCalls += 1
            report.selectedAlternatives += decision.alternatives.count
            var site = report.sites[decision.owner.number] ?? (siteName(decision.owner), 0, 0, 0, 0)
            site.multi += 1
            var survivors = 0
            for alternative in decision.alternatives {
                let f = fate(of: alternative, from: decision.position, tokenEnds: tokenEnds)
                if f.completed { survivors += 1; continue }
                report.losers += 1
                report.loserYields += f.yields
                report.loserTokens[min(f.tokensRead, 4)] += 1
                site.losers += 1
                site.loserYields += f.yields
                if f.tokensRead <= 1 { site.shortLosers += 1 }
                if f.tokensRead == 0, let stop = f.stoppedAt {
                    let index = alternative.bodySymbols.firstIndex(where: { $0 === stop }) ?? -1
                    report.zeroStops["\(site.name) ← #\(index) \(stop.kind) \(stop.name)", default: 0] += 1
                }
            }
            if survivors == decision.alternatives.count { report.allSurvive += 1 }
            report.sites[decision.owner.number] = site
        }
        return report
    }
}

/// Calls that never returned: a call cluster (X, i) with no pops. A ROOT dead call is one made from
/// a caller that does return (some other reading of the caller succeeded), so it is a wrong
/// prediction at that call site, not the fallout of a dead caller.
struct DeadCallReport {
    var clusters = 0
    var dead = 0
    var rootDead = 0
    /// Root dead calls where `viable` selected no alternative: only a cluster was made.
    var rootEmpty = 0
    /// Root dead calls by tokens read before they died: 0, 1, 2, 3, 4+.
    var rootTokens = [Int](repeating: 0, count: 5)
    /// Root dead calls by call site (the caller's slot, as `ebnfDot`), with their token histogram.
    var sites: [String: (count: Int, tokens: [Int])] = [:]

    func summary(top: Int = 30) -> String {
        func pct(_ a: Int, _ b: Int) -> String { b == 0 ? "-" : String(format: "%.1f%%", 100.0 * Double(a) / Double(b)) }
        var s = "calls: \(clusters) clusters, \(dead) never returned (\(pct(dead, clusters))), \(rootDead) of them from a caller that did (\(pct(rootDead, clusters)) of all calls)\n"
        s += "  of the root dead calls, \(rootEmpty) selected no alternative (only a cluster was made); the rest started and died:\n"
        s += "  root dead calls that started, by tokens read before dying: 0: \(rootTokens[0])  1: \(rootTokens[1])  2: \(rootTokens[2])  3: \(rootTokens[3])  4+: \(rootTokens[4])\n"
        let started = rootDead - rootEmpty
        s += "  of those, LL(1)-imprecise (0 tokens): \(pct(rootTokens[0], started)), LL(2) could cut (1 token): \(pct(rootTokens[1], started))\n"
        s += "top call sites of root dead calls (count: 0/1/2/3/4+ tokens):\n"
        for (site, v) in sites.sorted(by: { $0.value.count > $1.value.count }).prefix(top) {
            s += "  \(v.count): \(v.tokens.map(String.init).joined(separator: "/"))  \(site)\n"
        }
        return s
    }
}

extension MessageParser {

    func deadCallStatistics() -> DeadCallReport {
        var report = DeadCallReport()
        let tokenEnds = Array(Set(commits.map(\.triviaEnd))).sorted()
        // The innermost definition (LHS nonterminal or bracket) that owns each body symbol.
        var owner = [Int: GrammarNode]()
        var seen = Set<Int>()
        func walk(_ node: GrammarNode?) {
            guard let node, seen.insert(node.number).inserted else { return }
            if node.isLHS || node.kind.isBracket {
                var alt = node.alt
                while let a = alt { for b in a.bodySymbols { owner[b.number] = node }; alt = a.alt }
            }
            if node.kind != .END { walk(node.seq) }
            if !node.isRHS { walk(node.alt) }
        }
        for nt in grammar.allProductions { walk(nt) }
        for (key, cluster) in crf {
            report.clusters += 1
            guard cluster.pops.isEmpty else { continue }
            report.dead += 1
            // A live caller: the cluster of the definition owning the calling slot, at the edge's index.
            let liveEdge = cluster.returns.first { e in
                guard let o = owner[e.slot.number], let c = crf[ParsePosition(slot: o, index: e.index)] else { return false }
                return !c.pops.isEmpty
            }
            guard let edge = liveEdge else { continue }
            report.rootDead += 1
            if emptyCalls.contains(key) { report.rootEmpty += 1; continue }
            // How far the call got: the furthest yield of its alternatives from the call position.
            var reach = 0
            var alt = key.slot.alt
            while let a = alt {
                reach = max(reach, fate(of: a, from: key.index, tokenEnds: tokenEnds).tokensRead)
                alt = a.alt
            }
            let bucket = min(reach, 4)
            report.rootTokens[bucket] += 1
            let site = edge.slot.ebnfDot()
            var entry = report.sites[site] ?? (0, [0, 0, 0, 0, 0])
            entry.count += 1
            entry.tokens[bucket] += 1
            report.sites[site] = entry
        }
        return report
    }
}
