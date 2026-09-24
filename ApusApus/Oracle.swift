//
//  Oracle.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.05.04.
//

// Post-parse disambiguator operating entirely on BSR yield sets.
//
// Two phases:
//   1. Prune unproductive yields — walk BSR top-down from root, remove
//      yields not on any complete derivation path.
//   2. Disambiguate — apply grammar-annotated rules (shortest/longest match)
//      to choose among genuinely ambiguous alternatives.
//
// After phase 1, every surviving yield participates in at least one
// complete derivation, so phase 2 can prune without risk of
// inadvertently destroying the only valid parse.

import Foundation

// MARK: - Disambiguation Rule

protocol DisambiguationRule {
    func prune(_ yields: inout Set<BinarySpan>) -> Int
    /// HARD CONSTRAINT (`true`) vs PREFERENCE (`false`) — decides the pass this rule runs in.
    ///
    /// Hard constraints say what the LANGUAGE permits: a lookahead/containment predicate or a
    /// trivia-mode span rule removes a reading swift-syntax would never construct. Preferences
    /// (`@longest`/`@shortest`/`@prefer`/`@avoid`, associativity) merely choose among readings that
    /// are all legal.
    ///
    /// Order matters because prunes are irreversible. Running them interleaved let a PREFERENCE
    /// delete a reading that a hard constraint was about to make the only legal one:
    /// `var x: Int = foo()⏎{ didSet {} }` — `LongestMatchRule` dropped the short `prefixExpression`
    /// `foo()` in favour of the maximal `foo() { … }`, and the accessor-block reading needs exactly
    /// that short one. The lookahead predicate then removed the trailing closure, leaving nothing
    /// and turning valid input into a reject. Constraints first, then preferences over the
    /// survivors, with a dead-wood sweep between so the cascade is visible to the second pass.
    var isHardConstraint: Bool { get }
}

extension DisambiguationRule {
    var isHardConstraint: Bool { false }
}

struct LongestMatchRule: DisambiguationRule {
    let input: String
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByExtent(yields: &yields, input: input, keepLongest: true)
    }
}

struct ShortestMatchRule: DisambiguationRule {
    let input: String
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByExtent(yields: &yields, input: input, keepLongest: false)
    }
}

struct LeftAssocRule: DisambiguationRule {
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByPivot(yields: &yields, keep: { $0.max()! })
    }
}

struct RightAssocRule: DisambiguationRule {
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByPivot(yields: &yields, keep: { $0.min()! })
    }
}

/// The optional-skip rule — compiled from an `@avoid` alternate inside an OPT/KLN: prefer NOT
/// taking the optional whenever skipping still yields a complete parse. Registered on the
/// symbol immediately FOLLOWING the bracket. Competing readings reach the same enclosing span
/// `(i, j)` and differ only in the pivot `k` = where the bracket ended / the follower began.
/// The pivot uniformly encodes HOW MUCH the bracket consumed: `k = i` (bracket start) is the
/// skip, larger `k` are progressively longer takes. Keep the min-`k` (least consumption) and
/// prune the rest — so this prefers the skip, and, where the skip is not viable, the SHORTEST
/// take. That uniformity is exactly why the decision lives on the follower's pivot and not on
/// the avoided alternate's own yields: "skip" is the *absence* of an avoided-alternate yield,
/// observable only here. When skipping does not complete, phase-1 has already removed the skip
/// yield, so the lone take survives (e.g. `-x`).
///
/// ALTERNATE-AWARE: the bare pivot `k` cannot say WHICH alternate produced a taken reading, so a
/// non-avoided sibling `B` sharing `A`'s pivot would be collateral-pruned. `protectedLast` holds
/// the non-avoided siblings' last body symbols; any pivot they reach from the bracket start is
/// exempted. `A`'s same-span removal is `PreferRule`'s job. Single-body `[ @avoid X ]` has no
/// siblings, so `protectedLast` is empty and this is the classic keep-min-pivot.
struct AvoidOptionalRule: DisambiguationRule {
    let protectedLast: [GrammarNode]
    let yieldsOf: (GrammarNode) -> Set<BinarySpan>
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        let grouped = Dictionary(grouping: yields) { SpanKey(i: $0.i, j: $0.j) }
        var pruned = 0
        for (_, spans) in grouped where spans.count > 1 {
            let ks = spans.map(\.k)
            guard let minK = ks.min(), Set(ks).count > 1 else { continue }
            var protected = Set<CharPosition>()
            for sym in protectedLast {
                for y in yieldsOf(sym) where y.i == minK { protected.insert(y.j) }
            }
            for span in spans where span.k != minK && !protected.contains(span.k) {
                yields.remove(span)
                pruned += 1
            }
        }
        return pruned
    }
}

/// Alternate-level `@prefer` — same-span (flavor-3) preference. Only the *preferred*
/// alternate is annotated in the grammar; the Oracle registers this rule on each
/// NON-preferred sibling's last body symbol and prunes its completion yield `(i, j)`
/// wherever a preferred sibling covers the EXACT same span `(i, j)`. `@prefer` chooses
/// among alternates that tile the same extent — it is NOT an extent tool. Prefer-the-
/// longer is `@longest`'s job (see the note in `prune`).
struct PreferRule: DisambiguationRule {
    let preferredLastSymbols: [GrammarNode]
    let yieldsOf: (GrammarNode) -> Set<BinarySpan>
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        // Flavor-3 (same-span) ONLY: prune a non-preferred loser `(i, j)` iff a preferred sibling
        // covers the EXACT same span `(i, j)`. `@prefer` chooses among alternates that tile the same
        // extent — it is NOT an extent tool. Different-extent preference ("prefer the longer
        // alternate") is `@longest`'s job. Keying on start alone (the old behaviour) conflated the
        // two and wrongly pruned genuinely LONGER same-start neighbours (broke `a?.b`, multi-arg
        // subscripts, etc.). `span.i` = alternate start, `span.j` = alternate end.
        var preferredSpans = Set<SpanKey>()
        for sym in preferredLastSymbols {
            for y in yieldsOf(sym) { preferredSpans.insert(SpanKey(i: y.i, j: y.j)) }
        }
        var pruned = 0
        for span in yields where preferredSpans.contains(SpanKey(i: span.i, j: span.j)) {
            yields.remove(span)
            pruned += 1
        }
        return pruned
    }
}

private func pruneByExtent(
    yields: inout Set<BinarySpan>,
    input: String,
    keepLongest: Bool
) -> Int {
    // Extent compares interval LENGTH `j - k`, not the end `j`. For an `.N` LHS yield
    // `i == k`, so length ↔ `j` and this matches the classic behaviour. For a bracket
    // (yield `(alternate-start i, k = bracket-start, j)`), the competing readings of one
    // occurrence share `i`; they may differ in `j` (same start, S1) OR in `k` (start
    // moved by a variable-length prefix, so `j` is pinned — S2). Comparing `j` alone
    // can't see the S2 case; length can. Group by the alternate anchor `i`, keep the
    // min/max-length reading, prune the rest. `pruneUnproductive` then propagates the
    // kill backward/forward along the sequence.
    let grouped = Dictionary(grouping: yields) { $0.i }
    var pruned = 0
    for (_, spans) in grouped where spans.count > 1 {
        let lengths = spans.map { input.distance(from: $0.k, to: $0.j) }
        guard Set(lengths).count > 1 else { continue }
        let target = keepLongest ? lengths.max()! : lengths.min()!
        for span in spans where input.distance(from: span.k, to: span.j) != target {
            yields.remove(span)
            pruned += 1
        }
    }
    return pruned
}

private struct SpanKey: Hashable {
    let i: CharPosition
    let j: CharPosition
}

/// Parse predicate `@cannotParse(N)` / `@canParse(N)` with a nonterminal operand (see
/// `Grammar Predicate Lookahead Design.md`). Anchored on the alternate's FIRST body symbol,
/// whose yield start `i` is the alternate start. For each such yield, ask the Way-1 BSR
/// question "does `N` derive at `i`?" (`∃` a target yield with `.i == i`) and prune when the
/// predicate fails: negative (`@cannotParse`) fails where `N` DOES derive here; positive
/// (`@canParse`) fails where it does NOT. Removal cascades to the whole alternate via the
/// dead-wood sweep.
struct LookaheadPredicateRule: DisambiguationRule {
    var isHardConstraint: Bool { true }
    let negated: Bool
    /// Start positions where the target derives, SNAPSHOT from the RAW forest at Oracle registration
    /// (before dead-wood). This is swift-syntax's `canParseAsXxx`: a SPECULATIVE "could N parse here?",
    /// independent of whether the enclosing parse survives — so a target that lexes/parses but whose
    /// enclosing parse fails still counts (e.g. `/foo/` in `_ = /foo/ {}`, C3). The resulting prune
    /// cascades to a reject via the greatest-fixpoint `pruneUnsupported`.
    let targetStarts: Set<CharPosition>
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        var pruned = 0
        for span in yields {
            let derivesHere = targetStarts.contains(span.i)
            if negated ? derivesHere : !derivesHere { yields.remove(span); pruned += 1 }
        }
        return pruned
    }
}

/// Containment predicate `@within(N…)` on an alternate (see `Grammar Predicate Lookahead
/// Design.md`). Anchored on the alternate's first body symbol: keep a yield `[i,j]` only where
/// it is CONTAINED in a yield of EACH container `N` (`∃` an N-yield `[a,b]` with `a ≤ i` and
/// `j ≤ b`); prune otherwise. Conjunction over multiple containers. If a container has no yields
/// at all, nothing is contained in it → the alternate is pruned everywhere (positive semantics —
/// the reading is valid ONLY inside `N`). This is the declarative form of the retired procedural
/// `@within` filter (`WithinRule`): the context is read off the BSR, not a hand-rolled scan.
/// Containment predicate. `negated == false` = `@confinedTo` (keep only where contained in ALL
/// containers → prune where not); `negated == true` = `@excludedFrom` (prune where contained in
/// ALL). Both stack as a conjunction over `containers`. See `Grammar Predicate Lookahead Design.md`.
struct ContainmentRule: DisambiguationRule {
    var isHardConstraint: Bool { true }
    let containers: [() -> Set<BinarySpan>]
    let negated: Bool
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        let cys = containers.map { $0() }
        var pruned = 0
        for span in yields {
            let containedInAll = cys.allSatisfy { cy in cy.contains { $0.i <= span.i && span.j <= $0.j } }
            if containedInAll == negated { yields.remove(span); pruned += 1 }   // confinedTo prunes ¬contained; excludedFrom prunes contained
        }
        return pruned
    }
}

/// `@sameLine`. Prunes a yield whose span contains a newline that the parse crossed as trivia —
/// i.e. a newline not inside any committed terminal's content. Newlines INSIDE a token (a nested
/// multiline string, a block comment) are fine, which is what keeps `"a\("""⏎x⏎""")"` legal.
///
/// Models swift-syntax's per-lexer-state trivia mode rather than a check: `Cursor.swift`
/// `leadingTriviaLexingMode` returns `.noNewlines` while `inStringInterpolation` for a single-line
/// literal, and `lexInStringInterpolation` pops the state on `\r`/`\n`. The state persists at any
/// paren depth, which is why a `>n<` gate on the owned boundaries cannot cover every case and this
/// SPAN-level rule can.
///
/// The token cover comes from `commits`, a flat log of every commit including ones from derivations
/// that later died. That over-approximates the cover, so the rule can only ever MISS a prune, never
/// remove a legitimate parse — the safe direction.
struct SameLineSpanRule: DisambiguationRule {
    var isHardConstraint: Bool { true }
    /// Newline positions in the input.
    let newlines: [CharPosition]
    /// Content spans of the only tokens that may legitimately contain a newline (nested multiline
    /// strings, block comments). Pre-filtered to those, so the cover is tiny and the intent is
    /// explicit: a newline is legal ONLY inside such a token.
    let newlineBearingTokens: [(CharPosition, CharPosition)]
    /// Content start of every committed token, used to tell a CROSSED newline from a trailing one.
    let tokenStarts: [CharPosition]

    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        guard !newlines.isEmpty else { return 0 }
        var pruned = 0
        for span in yields {
            let crossedAsTrivia = newlines.contains { nl in
                nl >= span.i && nl < span.j
                    // Not inside a token that may legitimately contain newlines.
                    && !newlineBearingTokens.contains { $0.0 <= nl && nl < $0.1 }
                    // The parse must actually have CONTINUED past this newline inside the span.
                    // A yield's `j` is `triviaEnd`, so every span includes its own TRAILING trivia —
                    // `"\(x)"⏎` and `"\(x)"⏎// comment` both end with a newline that was never
                    // crossed. Requiring a token to START after the newline (still inside the span)
                    // distinguishes "crossed it" from "it merely trails".
                    && tokenStarts.contains { $0 > nl && $0 < span.j }
            }
            if crossedAsTrivia {
                yields.remove(span); pruned += 1
            }
        }
        return pruned
    }
}

private func pruneByPivot(
    yields: inout Set<BinarySpan>,
    keep: ([CharPosition]) -> CharPosition
) -> Int {
    let grouped = Dictionary(grouping: yields) { SpanKey(i: $0.i, j: $0.j) }
    var pruned = 0
    for (_, spans) in grouped where spans.count > 1 {
        let ks = spans.map(\.k)
        guard Set(ks).count > 1 else { continue }
        let target = keep(ks)
        for span in spans where span.k != target {
            yields.remove(span)
            pruned += 1
        }
    }
    return pruned
}

// MARK: - Oracle

class Oracle {
    let parser: MessageParser
    let grammar: Grammar
    let input: String
    private var rules: [(node: GrammarNode, rule: DisambiguationRule)] = []

    // MARK: - Prune tracing (diagnostics)
    //
    // Opt-in via `APUS_TRACE_ORACLE=1`. Reports which rule removed which yields, and whether the
    // root yield survives each of the three phases (dead-wood → rules → dead-wood). Exists because
    // a prune that removes the LAST reading is otherwise invisible: the parse reports `matched: 1`
    // and `adventParse` merely returns nil, with nothing to say who did it. Reach for this before
    // theorising about a disambiguation surprise.
    private var traceRulePrunes: Bool {
        ProcessInfo.processInfo.environment["APUS_TRACE_ORACLE"] == "1"
    }

    private func describe(_ span: BinarySpan) -> String {
        let i = input.distance(from: input.startIndex, to: span.i)
        let j = input.distance(from: input.startIndex, to: span.j)
        let text = input[span.i..<span.j].replacingOccurrences(of: "\n", with: "⏎")
        return "[\(i)..\(j)]'\(text.prefix(40))'"
    }

    private func logRulePrune(rule: DisambiguationRule, node: GrammarNode, removed: Set<BinarySpan>) {
        let label = node.name.isEmpty ? "<\(node.kind)#\(node.number)>" : "\(node.name)#\(node.number)"
        for span in removed.sorted() {
            print("oracle-trace: \(type(of: rule)) pruned \(label) \(describe(span))")
        }
    }

    /// The invariant EVERY pruning pass must preserve: a parse that existed when the Oracle
    /// started must still exist when it finishes. Disambiguation may reduce the NUMBER of
    /// derivations — never to zero. `disambiguate()` returns early unless the root's full-span
    /// yield is present, so past that guard "rawMatch" holds by construction and this is simply
    /// "postMatch must still hold", checked at every step.
    ///
    /// Asserted PER PHASE rather than once at the end, so a violation names the pass responsible
    /// instead of just the fact. Both ε defects fixed on 2026-09-03 (TODO 23) would have tripped
    /// this the moment they landed; instead they surfaced as a silently missing tree, and the
    /// design doc recorded the case as settled while it was broken.
    private func logRootStatus(_ phase: String) {
        let alive = parser.yield(of: grammar.root).contains {
            $0.i == input.startIndex && $0.j == input.endIndex
        }
        if traceRulePrunes {
            print("oracle-trace: after \(phase): root full-span yield \(alive ? "ALIVE" : "*** GONE ***")")
        }
        assert(alive, """
            Oracle over-pruned: the root's full-span yield existed before disambiguation and was \
            removed by '\(phase)'. Pruning may reduce the number of derivations, never to zero. \
            Re-run with APUS_TRACE_ORACLE=1 to see which pass or rule removed it.
            """)
    }

    /// `@sameLine` — anchored on the LHS, whose completion yields have `i == k` and `j` =
    /// the true end, i.e. the exact span of the construct. A body-symbol anchor cannot work: its yield is
    /// `(i = production start, k = symbol start, j = SYMBOL end)`, so the first symbol gives too
    /// little and the last gives an extent that measured wrong in practice (6 valid inputs pruned).
    ///
    /// Because the prune removes LHS yields, the annotated nonterminal must have exactly ONE
    /// alternate — otherwise it would take its siblings' yields too. That is why the grammar splits
    /// `interpolatedStringLiteral` into a single-line and a multiline nonterminal.
    private func registerSameLine(nonTerminal nt: GrammarNode) {
        guard nt.requiresSameLine else { return }
        assert(nt.alt?.alt == nil, "@sameLine needs a single-alternate nonterminal (it prunes LHS yields)")
        let newlines = input.indices.filter { input[$0] == "\n" || input[$0] == "\r" }
        // Only tokens that actually contain a newline can excuse one, so pre-filter to those.
        let bearing = parser.commits.compactMap { c -> (CharPosition, CharPosition)? in
            input[c.start..<c.end].contains { $0 == "\n" || $0 == "\r" } ? (c.start, c.end) : nil
        }
        let starts = parser.commits.map(\.start)
        rules.append((nt, SameLineSpanRule(
            newlines: newlines, newlineBearingTokens: bearing, tokenStarts: starts
        )))
    }

    private struct NodeSpan: Hashable { let id: ObjectIdentifier; let from, to: CharPosition }
    private struct NodePos: Hashable  { let id: ObjectIdentifier; let from: CharPosition }

    // MARK: - Support maps for the greatest-fixpoint dead-wood prune (`pruneUnsupported`).
    // Built once from the (static) grammar. Keyed by node.number. Unknown/missing entries are
    // treated as "keep" so a map gap can never over-remove a yield.
    private var supportMapsBuilt = false
    private var predecessorOf: [Int: GrammarNode] = [:]   // occurrence → previous body symbol
    private var isFirstBody: Set<Int> = []                 // occurrence is first in its body
    private var lastSymsOf: [Int: [GrammarNode]] = [:]     // definition (LHS/bracket) → alternates' last symbols
    private var hasEmptyAlt: Set<Int> = []                 // definition has an empty/nullable alternate
    private var allYieldNodes: [GrammarNode] = []          // every grammar node (for the sweep)

    init(parser: MessageParser, input: String) {
        self.parser = parser
        self.grammar = parser.grammar
        self.input = input
        for (_, nt) in grammar.nonTerminals {
            // Node-level extent/associativity (@longest/@shortest/@left/@right),
            // read off the owner node — for a nonterminal that is the production-start
            // form `@longest X = …` stored on `nt.disambiguation`.
            registerNodeDisambiguation(owner: nt)
            // Alternate-level @prefer / @avoid on the nonterminal's own alt chain.
            registerPrefer(altChainHead: nt.alt)
            // `@sameLine` — anchored on the LHS, see below.
            registerSameLine(nonTerminal: nt)
        }

        // Full-graph walk for the pragmas that live on a NESTED node — every ALT-bearing
        // node is treated exactly like a nonterminal:
        //   - node-level extent/assoc: `registerNodeDisambiguation` reads the pragma off
        //     the bracket node (`@longest ( … )` / `@left < … >`, parsed in `factor()`).
        //   - alternate-level @prefer / @avoid: `registerPrefer` reads `isPreferred` /
        //     `isAvoided` off the cluster's ALT nodes (a bracket owns its alternates via
        //     `.alt` exactly like a nonterminal LHS — `factor()` → `GrammarNode(.DO/…,
        //     alt: selection())`). Run per BRACKET node (not per ALT node, whose `.alt`
        //     is a sibling continuation), so each group is registered exactly once.
        //   - the optional-skip: an `@avoid` alternate inside an OPT/KLN competes against
        //     that group's implicit empty (skip) branch — the ε rival that `registerPrefer`
        //     can't key on. `registerOptionalSkip` compiles it to an alternate-aware
        //     follower-pivot rule (`AvoidOptionalRule`).
        var seen = Set<ObjectIdentifier>()
        func walk(_ node: GrammarNode?) {
            guard let node, seen.insert(ObjectIdentifier(node)).inserted else { return }
            if node.kind.isBracket {
                registerNodeDisambiguation(owner: node)
                registerPrefer(altChainHead: node.alt)
                registerOptionalSkip(bracket: node)
            }
            // Leading parse predicate on an ALT node (`@cannotParse(N)`/`@canParse(N)`, N a
            // nonterminal). Anchor the prune on the alternate's first body symbol.
            // Repeatable: each predicate becomes its own rule on the same anchor, so they compose as
            // a CONJUNCTION (every rule prunes independently).
            for predicate in node.forwardPredicates {
                if let target = grammar.nonTerminals[predicate.targetName], let anchor = node.bodySymbols.first {
                    // Snapshot RAW target starts NOW (Oracle init runs before dead-wood) — canParseAsXxx.
                    let targetStarts = Set(parser.yield(of: target).map(\.i))
                    rules.append((anchor, LookaheadPredicateRule(negated: predicate.negated,
                                                                 targetStarts: targetStarts)))
                } else {
                    assertionFailure("lookahead predicate: unresolved target '\(predicate.targetName)' or empty alternate")
                }
            }
            // Leading containment predicate(s) on an ALT node — `@confinedTo(N…)` (keep only where
            // contained) / `@excludedFrom(N…)` (prune where contained). Anchor on the first body symbol.
            for (names, negated) in [(node.confinedToContainers, false), (node.excludedFromContainers, true)]
            where !names.isEmpty {
                let p = parser
                if let anchor = node.bodySymbols.first {
                    let containers = names.compactMap { name -> (() -> Set<BinarySpan>)? in
                        guard let c = grammar.nonTerminals[name] else {
                            assertionFailure("containment: unknown container nonterminal '\(name)'"); return nil
                        }
                        return { p.yield(of: c) }
                    }
                    rules.append((anchor, ContainmentRule(containers: containers, negated: negated)))
                } else {
                    assertionFailure("containment predicate on an empty alternate")
                }
            }
            // `@sameLine` is registered per nonterminal, not here — it must
            // anchor on LHS completion yields to get the construct's exact span.
            if node.kind != .END { walk(node.seq) }
            walk(node.alt)
        }
        for nt in grammar.nonTerminals.values { walk(nt) }
    }

    /// Register node-level extent/associativity for an ALT-bearing `owner` (a
    /// nonterminal LHS or an inline `( )`/`[ ]`/`{ }`/`< >` cluster), reading the pragma
    /// off `owner.disambiguation` (set before the LHS in `production()` or before the
    /// bracket in `factor()`):
    ///   - extent (`@longest`/`@shortest`): register on the owner itself. Its yields from
    ///     a common start are what an extent rule prunes, and `endPositions` reads those
    ///     yields for `.N` nonterminals AND (now) `.OPT` brackets, so the prune propagates
    ///     through both the phase-1 cascade and the DerivationBuilder. (Closures still
    ///     recompute their transitive extent from the body, so extent on a `{ }`/`< >`
    ///     closure is not yet honored — a separate carrier problem.)
    ///   - associativity (`@left`/`@right`): register a pivot rule on every alternate's
    ///     body symbols (associativity governs the whole node's self-ambiguity).
    private func registerNodeDisambiguation(owner: GrammarNode) {
        guard let d = owner.disambiguation else { return }
        switch d {
        case .shortest, .longest:
            // BRACKET extent is handled in the phase-1 walk (`tileBody` keeps the min/max
            // feasible span per enclosing context). A NONTERMINAL keeps the classic global
            // extent on its own yields.
            if !owner.kind.isBracket {
                rules.append((owner, d == .shortest ? ShortestMatchRule(input: input) : LongestMatchRule(input: input)))
            }
        case .left, .right:
            let rule: DisambiguationRule = d == .left ? LeftAssocRule() : RightAssocRule()
            var alt = owner.alt
            while let a = alt {
                for sym in a.bodySymbols { rules.append((sym, rule)) }
                alt = a.alt
            }
        }
    }

    /// Register the same-span, last-symbol-keyed alternate preferences for one alternate
    /// group (a chain of `.ALT` nodes reachable from `altChainHead`). Level-agnostic: the
    /// head may be a nonterminal's `nt.alt` or an inline cluster's `bracket.alt`.
    ///   - `@prefer` names WINNERS: every non-preferred sibling is pruned where a
    ///     preferred sibling covers the same `(i, j)` span.
    ///   - `@avoid` names a LOSER: it is the dual — an avoided alternate is pruned where ANY
    ///     of its siblings covers the same `(i, j)`, i.e. `@avoid A` ≡ `@prefer` on all of
    ///     A's (non-empty) siblings. This handles only the EXPLICIT-sibling rivalry; the
    ///     avoided alternate's other rival — an OPT/KLN's implicit empty (skip) branch — is
    ///     compiled separately by `registerOptionalSkip`, because ε has no last body symbol
    ///     to key a same-span rule on.
    /// Both key on last body symbols, so a winner must be non-empty to be keyable.
    private func registerPrefer(altChainHead: GrammarNode?) {
        var alts: [GrammarNode] = []
        var scan = altChainHead
        while let a = scan { alts.append(a); scan = a.alt }
        let p = parser

        // @prefer: preferred alternates prune their non-preferred siblings.
        let preferredLast = alts.filter { $0.isPreferred }.compactMap { $0.bodySymbols.last }
        if !preferredLast.isEmpty {
            for a in alts where !a.isPreferred {
                if let last = a.bodySymbols.last {
                    rules.append((last, PreferRule(preferredLastSymbols: preferredLast,
                                                   yieldsOf: { p.yield(of: $0) })))
                }
            }
        }

        // @avoid (alt-prefix): an avoided alternate loses to all its (non-empty) siblings.
        for a in alts where a.isAvoided {
            let siblingsLast = alts.filter { $0 !== a }.compactMap { $0.bodySymbols.last }
            if let last = a.bodySymbols.last, !siblingsLast.isEmpty {
                rules.append((last, PreferRule(preferredLastSymbols: siblingsLast,
                                               yieldsOf: { p.yield(of: $0) })))
            }
        }
    }

    /// The optional-skip: an `@avoid` alternate inside an OPT (`[ … ]`) or KLN (`{ … }`)
    /// competes against the group's **implicit empty (skip) branch** — the ε rival that
    /// `registerPrefer` can't key on (ε has no last body symbol). Register an
    /// `AvoidOptionalRule` on EACH avoided alternate's own `lastContentSymbol`: it reads the
    /// bracket's follower to detect the take-vs-skip competition and removes the avoided
    /// alternate's own "taken" completions. POS (`< … >`) and DO (`( … )`) have no skip
    /// branch and are excluded.
    private func registerOptionalSkip(bracket: GrammarNode) {
        guard bracket.kind == .OPT || bracket.kind == .KLN else { return }
        var alts: [GrammarNode] = []
        var scan = bracket.alt
        while let a = scan { alts.append(a); scan = a.alt }
        guard alts.contains(where: { $0.isAvoided }) else { return }
        guard let next = bracket.seq, next.kind != .END else { return }
        let protectedLast = alts.filter { !$0.isAvoided }.compactMap { $0.bodySymbols.last }
        let p = parser
        rules.append((next, AvoidOptionalRule(protectedLast: protectedLast,
                                              yieldsOf: { p.yield(of: $0) })))
    }

    @discardableResult
    func disambiguate() -> Int {
        let n = input.endIndex
        let origin = input.startIndex
        guard parser.yield(of: grammar.root).contains(where: { $0.i == origin && $0.j == n }) else { return 0 }

        var deadYields = 0
        while true {
            // Split, not summed, so the tracer can say WHICH of the two dead-wood passes
            // removed the last reading — the two have very different failure modes.
            let unsupported = pruneUnsupported()
            logRootStatus("phase 1 pruneUnsupported (-\(unsupported))")
            let unproductive = pruneUnproductive(endPosition: n)
            logRootStatus("phase 1 pruneUnproductive (-\(unproductive))")
            let pruned = unsupported + unproductive
            deadYields += pruned
            if pruned == 0 { break }
        }
        logRootStatus("phase 1 dead-wood")
        // Two passes: HARD CONSTRAINTS first, then PREFERENCES over the survivors (see
        // `DisambiguationRule.isHardConstraint`). Prunes are irreversible, so a preference must
        // never get to delete a reading that a constraint is about to make the only legal one.
        // The dead-wood sweep between the passes propagates each constraint's kill, so the
        // preference pass sees the reduced forest rather than the raw one.
        var disambiguated = 0
        func runPass(_ selected: [(node: GrammarNode, rule: DisambiguationRule)]) {
            var changed = true
            while changed {
                changed = false
                for (node, rule) in selected {
                    // Copy out / write back instead of `&parser.yields[node.number]`
                    // — a rule's `yieldsOf` closure reads other nodes' yields out of the
                    // same `parser.yields` array, and Swift's law of exclusivity forbids a
                    // read and a modify on the same parent at the same time.
                    var spans = parser.yields[node.number]
                    let before = traceRulePrunes ? spans : []
                    let pruned = rule.prune(&spans)
                    parser.yields[node.number] = spans
                    if pruned > 0 {
                        if traceRulePrunes { logRulePrune(rule: rule, node: node, removed: before.subtracting(spans)) }
                        disambiguated += pruned
                        changed = true
                    }
                }
            }
        }

        runPass(rules.filter { $0.rule.isHardConstraint })
        logRootStatus("hard-constraint pass")
        var interDead = 0
        while true {
            let pruned = pruneUnsupported() + pruneUnproductive(endPosition: n)
            interDead += pruned
            if pruned == 0 { break }
        }
        logRootStatus("inter-pass dead-wood")
        runPass(rules.filter { !$0.rule.isHardConstraint })
        logRootStatus("rule pass")
        // Second dead-wood sweep: rules may have pruned body-symbol yields whose
        // parent .N yields are now unreachable. Cascade to a fixed point.
        var secondDead = 0
        while true {
            let pruned = pruneUnsupported() + pruneUnproductive(endPosition: n)
            secondDead += pruned
            if pruned == 0 { break }
        }

        logRootStatus("phase 2 dead-wood")
        let total = deadYields + interDead + secondDead + disambiguated
        if total > 0, parseReports {
            print("oracle: removed \(deadYields)+\(secondDead) dead + \(disambiguated) disambiguated yields")
        }
        assert(isUnambiguous(endPosition: n), "Oracle postcondition violated: residual ambiguity remains")
        return total
    }

    // MARK: - Postcondition: No Residual Ambiguity

    private func isUnambiguous(endPosition n: CharPosition) -> Bool {
        // TODO: implement full ambiguity check across all reachable nonterminals
        return true
    }

    // MARK: - Greatest-fixpoint support prune (cascades a targeted yield removal)

    /// Build the (grammar-static) support maps once. For each alternate body of every definition
    /// (LHS nonterminal or bracket), record: each symbol's predecessor / first-ness, and the
    /// definition's per-alternate last symbols + whether it has an empty alternate. OPT/KLN are
    /// always nullable.
    private func buildSupportMaps() {
        guard !supportMapsBuilt else { return }
        supportMapsBuilt = true
        var seen = Set<Int>()
        func collect(_ node: GrammarNode?) {
            guard let node, seen.insert(node.number).inserted else { return }
            allYieldNodes.append(node)
            if node.kind != .END { collect(node.seq) }
            collect(node.alt)
        }
        for nt in grammar.nonTerminals.values { collect(nt) }
        collect(grammar.root)

        // A definition is a node that OWNS alternates: an LHS nonterminal or a bracket.
        func indexDefinition(_ def: GrammarNode) {
            if def.kind == .OPT || def.kind == .KLN { hasEmptyAlt.insert(def.number) }  // nullable
            var alt = def.alt
            while let a = alt {
                defer { alt = a.alt }
                let body = a.bodySymbols
                // An alternate spelled `""` is NOT syntactically empty — its body holds an
                // EPS node. Treating only `body.isEmpty` as nullable made `A = "a" | ""`
                // unrecognised as nullable, so the completion `(A,i,i)` fell through to
                // `lastSymSpans` and was pruned as unsupported. Both spellings are ε.
                if body.allSatisfy({ $0.kind == .EPS }) { hasEmptyAlt.insert(def.number); continue }
                lastSymsOf[def.number, default: []].append(body[body.count - 1])
                for m in body.indices {
                    if m == 0 { isFirstBody.insert(body[m].number) }
                    else { predecessorOf[body[m].number] = body[m - 1] }
                }
            }
        }
        for node in allYieldNodes {
            if node.isLHS || node.kind.isBracket { indexDefinition(node) }
        }
    }

    /// Greatest-fixpoint (decreasing) removal of yields whose BSR support is gone. A yield
    /// `(i,k,j)` on a node means: the symbol derives `[k,j]` and the production-prefix before it
    /// derives `[i,k]` (for a definition/LHS completion `i==k`, span `[i,j]`). We remove a yield
    /// ONLY when its support is provably absent, iterating to a fixed point — so a targeted Oracle
    /// prune cascades to every ancestor, while grounded recursion keeps its base (cycle-safe, unlike
    /// a least-fixpoint). Unknown map entries and closures are kept, so this never over-removes.
    private func pruneUnsupported() -> Int {
        buildSupportMaps()

        // (i,j) LOOKUP INDEX. All three support queries below ask the same question — "does node X
        // carry a yield with this exact (i, j) pair?" — and each was a LINEAR scan of that node's
        // yield set (`yields[X].contains { $0.i == … && $0.j == … }`). Since the fixpoint filters
        // every node's yields on every round, that made a round quadratic in the yield count, which
        // is where this phase's time went (measured: 3.7s and 4.8s on two calls for a 38KB file,
        // against ~0.4s for the whole `pruneUnproductive` walk).
        //
        // Maintained INCREMENTALLY rather than rebuilt per round, deliberately: the round mutates
        // `parser.yields` as it walks nodes, so a round-start snapshot would answer with stale
        // yields. That converges to the same greatest fixpoint but over more rounds; refreshing the
        // one node we just filtered keeps the observable behaviour identical to the scan.
        // LAZY, and array-backed rather than a dictionary (node numbers index `parser.yields`
        // directly, so this follows the project's integer-ID convention and skips hashing the key).
        // Lazy matters: eagerly indexing every node cost more than it saved on the snippet suite,
        // where most nodes are never queried — building all of them made the default suite ~7%
        // slower even though it made a 38KB file ~9x faster. Only nodes actually consulted pay.
        var ijIndex = [Set<IJPair>?](repeating: nil, count: parser.yields.count)
        func hasIJ(_ num: Int, _ i: CharPosition, _ j: CharPosition) -> Bool {
            if ijIndex[num] == nil {
                let ys = parser.yields[num]
                var acc = Set<IJPair>(minimumCapacity: ys.count)
                for y in ys { acc.insert(IJPair(i: y.i, j: y.j)) }
                ijIndex[num] = acc
            }
            return ijIndex[num]!.contains(IJPair(i: i, j: j))
        }

        // prefix `[i,k]` derivable: first symbol ⇒ i==k; else the predecessor ended at k with the
        // same production-left i. Unknown predecessor ⇒ keep.
        func prefixOK(_ N: GrammarNode, _ y: BinarySpan) -> Bool {
            // A first body symbol has an EMPTY prefix → trivially satisfied. (Do NOT require i==k:
            // in a closure body, iterations after the first have i = closure-start ≠ k = iteration-
            // start, yet their prefix is still empty relative to the iteration.)
            if isFirstBody.contains(N.number) { return true }
            guard let p = predecessorOf[N.number] else { return true }
            return hasIJ(p.number, y.i, y.k)
        }
        // Some alternate of `def` has a last symbol spanning [from,to] (body-left == from).
        func lastSymSpans(_ def: GrammarNode, from: CharPosition, to: CharPosition) -> Bool {
            guard let syms = lastSymsOf[def.number] else { return true }  // unknown ⇒ keep
            for s in syms where hasIJ(s.number, from, to) { return true }
            return false
        }
        func supported(_ N: GrammarNode, _ y: BinarySpan) -> Bool {
            switch N.kind {
            case .N where N.isLHS:
                // Completion (a,a,b): supported iff some alternate's body tiled [a,b] (its last
                // symbol carries i==a, j==b), or an empty alternate covers a==b.
                if y.i == y.j && hasEmptyAlt.contains(N.number) { return true }
                return lastSymSpans(N, from: y.i, to: y.j)
            case .N:  // reference occurrence
                guard prefixOK(N, y) else { return false }
                guard let X = N.alt else { return true }            // no LHS ⇒ keep
                return hasIJ(X.number, y.k, y.j)                   // X derives [k,j]
            case .T, .TI, .C, .B, .EPS:
                return prefixOK(N, y)                                // terminal/boundary: leaf
            case .DO, .OPT, .POS, .KLN:
                guard prefixOK(N, y) else { return false }
                if N.kind == .KLN || N.kind == .POS { return true }  // closures kept (conservative)
                if y.k == y.j && hasEmptyAlt.contains(N.number) { return true }
                return lastSymSpans(N, from: y.k, to: y.j)           // bracket body over [k,j]
            default:
                return true                                          // EOS/END/ALT: keep
            }
        }

        var total = 0
        var changed = true
        while changed {
            changed = false
            for node in allYieldNodes {
                let num = node.number
                guard !parser.yields[num].isEmpty else { continue }
                let before = parser.yields[num].count
                parser.yields[num] = parser.yields[num].filter { supported(node, $0) }
                let removed = before - parser.yields[num].count
                if removed > 0 { total += removed; changed = true; ijIndex[num] = nil }
            }
        }
        return total
    }

/// Key for the `pruneUnsupported` (i,j) index — a yield's outer span, ignoring the pivot `k`.
private struct IJPair: Hashable {
    let i: CharPosition
    let j: CharPosition
}

    // MARK: - Phase 1: Prune Unproductive Yields

    private func pruneUnproductive(endPosition n: CharPosition) -> Int {
        var reachable = Set<NodeSpan>()
        var expanding = Set<NodeSpan>()
        var endCache = [NodePos: Set<CharPosition>]()
        var endGuard = Set<NodePos>()

        // End positions reachable from `sym` starting at `from`.
        // Mirrors DerivationBuilder.endPositions — read-only query on yields.
        func endPositions(_ sym: GrammarNode, from: CharPosition) -> Set<CharPosition> {
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
                    // yields so the extent prune is honored here. A bracket is an RHS
                    // occurrence — yields are `(alternate-start, k = bracket-start, j)`,
                    // filtered by `k == from` like a terminal; a closure's shared cluster
                    // accumulates its transitive ends the same way.
                    result = Set(parser.yield(of: sym).lazy.filter { $0.k == from }.map(\.j))
                } else {
                    // UNANNOTATED bracket: original body-recompute path, untouched — so the
                    // global operator/regex machinery keeps its exact phase-1 reachability.
                    var positions = Set<CharPosition>()
                    if sym.kind == .KLN || sym.kind == .OPT { positions.insert(from) }
                    if sym.kind.isClosure {
                        var visited = Set<CharPosition>()
                        var queue = [from]
                        while !queue.isEmpty {
                            let pos = queue.removeFirst()
                            guard visited.insert(pos).inserted else { continue }
                            for end in iterEndPositions(sym, from: pos) where end > pos {
                                positions.insert(end)
                                queue.append(end)
                            }
                        }
                    } else {
                        positions.formUnion(iterEndPositions(sym, from: from))
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

        func iterEndPositions(_ bracket: GrammarNode, from: CharPosition) -> Set<CharPosition> {
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

        // Walk the BSR graph top-down. Returns true if any valid tiling
        // of `node`'s alternates covers [from, to].
        @discardableResult
        func visit(_ node: GrammarNode, from: CharPosition, to: CharPosition) -> Bool {
            let key = NodeSpan(id: ObjectIdentifier(node), from: from, to: to)
            if reachable.contains(key) { return true }
            guard expanding.insert(key).inserted else { return false }
            defer { expanding.remove(key) }

            guard parser.yield(of: node).contains(where: { $0.i == from && $0.j == to }) else { return false }

            if visitAlternates(node, from: from, to: to) {
                reachable.insert(key)
                return true
            }
            return false
        }

        func visitAlternates(_ node: GrammarNode, from: CharPosition, to: CharPosition) -> Bool {
            var found = false
            var alt = node.alt
            while let a = alt {
                defer { alt = a.alt }
                let body = a.bodySymbols.filter { $0.kind != .EPS }
                if body.isEmpty {
                    if from == to {
                        found = true
                        // The walk VALIDATED this ε alternate, so it must also MARK it.
                        // EPS symbols are filtered out of the tiling (they consume nothing),
                        // which previously meant nothing ever marked their `(i,k,k)` yields
                        // reachable — so the sweep below deleted them, and `pruneUnsupported`
                        // then cascaded that loss into the enclosing nonterminal.
                        for eps in a.bodySymbols where eps.kind == .EPS {
                            reachable.insert(NodeSpan(id: ObjectIdentifier(eps), from: from, to: from))
                        }
                    }
                } else if tileBody(body, from: from, to: to) {
                    found = true
                }
            }
            return found
        }

        // Pure (side-effect-free) feasibility: can `symbols` tile exactly `[from, to]`?
        // Threads `endPositions` (itself read-only + memoised) as a frontier fold. Used to
        // decide, per enclosing context, which end positions of an EXTENT-annotated node keep
        // the parse complete — WITHOUT marking anything reachable.
        func bodyTiles(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> Bool {
            var frontier: Set<CharPosition> = [from]
            for sym in symbols {
                var next = Set<CharPosition>()
                for f in frontier { next.formUnion(endPositions(sym, from: f).filter { $0 <= to }) }
                if next.isEmpty { return false }
                frontier = next
            }
            return frontier.contains(to)
        }

        // Extent objective for a BRACKET (`@shortest`/`@longest [ … ]`): among the feasible
        // spans this node can take in THIS enclosing context, keep only the shortest/longest.
        // Per-context (not per-start) is the whole point — it's the constraint-solver reading:
        // minimise/maximise this node's span *subject to a complete parse existing*. Both
        // flavors collapse here: siblings absorb the slack (`[x][x]`, `{x}{x}{x}`), or the
        // follower does (optional-skip). Nonterminal extent stays on the classic global rule.
        func bracketExtent(_ node: GrammarNode) -> Disambiguation? {
            guard node.kind.isBracket, let d = node.disambiguation,
                  d == .shortest || d == .longest else { return nil }
            return d
        }

        struct BodyStep {
            let symbol: GrammarNode
            let from: CharPosition
            let to: CharPosition
        }

        struct BodyKey: Hashable {
            let index: Int
            let position: CharPosition
        }

        func constrainedTilings(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> [[BodyStep]] {
            var cache = [BodyKey: [[BodyStep]]]()

            func enumerate(index: Int, position: CharPosition) -> [[BodyStep]] {
                if index == symbols.count { return position == to ? [[]] : [] }
                let cacheKey = BodyKey(index: index, position: position)
                if let cached = cache[cacheKey] { return cached }

                let sym = symbols[index]
                var result: [[BodyStep]] = []
                for end in endPositions(sym, from: position) where end <= to {
                    for tail in enumerate(index: index + 1, position: end) {
                        result.append([BodyStep(symbol: sym, from: position, to: end)] + tail)
                    }
                }
                cache[cacheKey] = result
                return result
            }

            var tilings = enumerate(index: 0, position: from)
            for sym in symbols {
                guard let d = bracketExtent(sym) else { continue }
                let lengths = tilings.compactMap { tiling -> Int? in
                    guard let step = tiling.first(where: { $0.symbol === sym }) else { return nil }
                    return input.distance(from: step.from, to: step.to)
                }
                guard let target = d == .longest ? lengths.max() : lengths.min() else { continue }
                tilings = tilings.filter { tiling in
                    guard let step = tiling.first(where: { $0.symbol === sym }) else { return false }
                    return input.distance(from: step.from, to: step.to) == target
                }
            }
            return tilings
        }

        // Tile body symbols over [from, to]. Returns true if any complete
        // tiling exists, and recursively visits nonterminals along the way.
        func tileBody(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> Bool {
            if symbols.contains(where: { bracketExtent($0) != nil }) {
                let tilings = constrainedTilings(symbols, from: from, to: to)
                guard !tilings.isEmpty else { return false }
                for tiling in tilings {
                    for step in tiling {
                        visitSymbol(step.symbol, from: step.from, to: step.to)
                    }
                }
                return true
            }

            guard let first = symbols.first else { return from == to }
            let rest = Array(symbols.dropFirst())
            // Feasible end positions of `first` in this context.
            var mids = endPositions(first, from: from).filter { mid in
                mid <= to && (rest.isEmpty ? mid == to : bodyTiles(rest, from: mid, to: to))
            }
            guard !mids.isEmpty else { return false }
            // Extent objective: an annotated bracket keeps only its shortest/longest feasible span.
            if let d = bracketExtent(first) {
                let target = d == .longest ? mids.max()! : mids.min()!
                mids = [target]
            }
            for mid in mids {
                visitSymbol(first, from: from, to: mid)
                if !rest.isEmpty { _ = tileBody(rest, from: mid, to: to) }
            }
            return true
        }

        func visitSymbol(_ sym: GrammarNode, from: CharPosition, to: CharPosition) {
            if parser.yield(of: sym).contains(where: { ($0.i == from && $0.j == to) || ($0.k == from && $0.j == to) }) {
                reachable.insert(NodeSpan(id: ObjectIdentifier(sym), from: from, to: to))
            }

            switch sym.kind {
            case .N:
                guard let lhs = sym.alt else { return }
                visit(lhs, from: from, to: to)
            case .DO, .OPT, .KLN, .POS:
                visitBracket(sym, from: from, to: to)
            default:
                break
            }
        }

        func visitBracket(_ bracket: GrammarNode, from: CharPosition, to: CharPosition) {
            if from == to { return }
            // For a non-closure bracket, iterate the bracket's OWN (Oracle-pruned) end
            // positions — so an extent prune on the bracket is honored by the reachability
            // walk and dead sibling/prefix yields get removed ("walk the rest of the
            // sequence to kill dead paths"). Using `iterEndPositions` (body recompute) here
            // re-marked extent-pruned spans reachable, leaving stale readings that kept an
            // enclosing pivot ambiguous. Closures still step per-iteration (their own ends
            // are transitive, not single-step) and recurse below.
            let ends = bracket.kind.isClosure
                ? iterEndPositions(bracket, from: from)
                : endPositions(bracket, from: from)
            for end in ends where end <= to && end > from {
                if visitAlternates(bracket, from: from, to: end) {
                    reachable.insert(NodeSpan(id: ObjectIdentifier(bracket), from: from, to: end))
                    if end == to {
                        // iteration covers the full span
                    } else if bracket.kind.isClosure {
                        visitBracket(bracket, from: end, to: to)
                    }
                }
            }
        }

        // Seed from root
        visit(grammar.root, from: input.startIndex, to: n)

        // Remove unreachable yields from every grammar node. Body-symbol yields
        // can otherwise keep stale tilings alive after a parent alternate was pruned.
        var allNodes: [GrammarNode] = [grammar.root]
        var seen = Set<ObjectIdentifier>()

        func collect(_ node: GrammarNode?) {
            guard let node else { return }
            guard seen.insert(ObjectIdentifier(node)).inserted else { return }
            allNodes.append(node)
            if node.kind != .END {
                collect(node.seq)
            }
            collect(node.alt)
        }

        for nt in grammar.nonTerminals.values {
            collect(nt)
        }

        var pruned = 0
        for node in allNodes {
            let before = parser.yields[node.number].count
            parser.yields[node.number] = parser.yields[node.number].filter { span in
                reachable.contains(NodeSpan(id: ObjectIdentifier(node), from: span.i, to: span.j))
                    || reachable.contains(NodeSpan(id: ObjectIdentifier(node), from: span.k, to: span.j))
            }
            pruned += before - parser.yields[node.number].count
        }
        return pruned
    }
}
