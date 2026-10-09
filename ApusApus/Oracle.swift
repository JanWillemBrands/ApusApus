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
//   2. Disambiguate — apply the grammar-annotated rules, one `OraclePass` at a time
//      (filter → sameSpan → structure → extent), with a dead-wood sweep after each.
//
// After phase 1, every surviving yield participates in at least one
// complete derivation, so phase 2 can prune without risk of
// inadvertently destroying the only valid parse.

import Foundation

// MARK: - Disambiguation Rule

protocol DisambiguationRule {
    func prune(_ yields: inout Set<BinarySpan>) -> Int
    /// The pass this rule runs in. Deliberately has NO default: a default (`isHardConstraint =
    /// true`) once filed five preferences into the wrong pass without anyone noticing.
    var pass: OraclePass { get }
}

/// The Oracle's rule passes, in run order. Each pass runs to a fixpoint and is followed by a
/// dead-wood sweep, so the next pass sees the previous one's kills propagated.
///
/// The order follows from ONE property of each rule — what happens to its decision if OTHER
/// yields disappear later:
///
/// - MONOTONE rules keep a yield only if some witness EXISTS (a same-line derivation, an
///   enclosing container, a raw-forest parse). Losing other yields can only make them stricter,
///   never invalidate a prune, so they are order-free. They go first.
/// - ANTI-MONOTONE rules prune a yield BECAUSE a rival exists (a preferred sibling, a longer
///   extent, "production p completed at this child's span"). If that rival is removed later the
///   prune was wrong, and prunes are irreversible. Such a rule must run after everything that can
///   still remove its rivals.
///
/// That gives a dependency order, and every edge in it was a measured bug:
///
///     filter → sameSpan      `var x: Int = foo()⏎{ didSet {} }`: a preference ran interleaved
///                            with the lookahead predicate and deleted the only legal reading.
///     sameSpan → structure   `f(1) {}⏎{}`: `@prefer` removes the parenless reading of `f(1) {}`;
///                            before it does, the `@right` filter takes `f(1) {}` for an
///                            instance of itself and kills the chain.
///     structure → extent     `x.map { [$0] }⏎{…}(&y[0])`: `@longest` chose the chained
///                            initializer, the filter then removed the chain, and nothing was
///                            left.
enum OraclePass: Int, CaseIterable {
    /// Monotone language constraints: `@canParse`/`@cannotParse`, `@sameLineOutsideBrackets`.
    case filter
    /// Same-span choice among sibling alternates: `@prefer`, `@avoid` (explicit siblings).
    case sameSpan
    /// Parent/child-shape filters that ask WHICH production occupies a span: `@left`/`@right`.
    /// That question only has an answer once `sameSpan` has settled each span's alternate.
    case structure
    /// Different-extent choice: `@longest`, `@shortest`, `@avoid` against an optional's skip.
    /// Last, because it ranks the extents that the passes before it remove.
    case extent
}

struct LongestMatchRule: DisambiguationRule {
    var pass: OraclePass { .extent }
    let input: String
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByExtent(yields: &yields, input: input, keepLongest: true)
    }
}

struct ShortestMatchRule: DisambiguationRule {
    var pass: OraclePass { .extent }
    let input: String
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        pruneByExtent(yields: &yields, input: input, keepLongest: false)
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
    /// Extent, not same-span: the rivals share `(i, j)` but differ in how much the optional
    /// consumed, which is the inner bracket's extent.
    var pass: OraclePass { .extent }
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
    var pass: OraclePass { .sameSpan }
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
/// `Ambiguity.md`). Anchored on the alternate's FIRST body symbol,
/// whose yield start `i` is the alternate start. For each such yield, ask the Way-1 BSR
/// question "does `N` derive at `i`?" (`∃` a target yield with `.i == i`) and prune when the
/// predicate fails: negative (`@cannotParse`) fails where `N` DOES derive here; positive
/// (`@canParse`) fails where it does NOT. Removal cascades to the whole alternate via the
/// dead-wood sweep.
struct LookaheadPredicateRule: DisambiguationRule {
    var pass: OraclePass { .filter }
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

/// Containment predicate `@within(N…)` on an alternate (see `Ambiguity.md`). Anchored on the alternate's first body symbol: keep a yield `[i,j]` only where
/// `@left` / `@right` on an ALTERNATE — associativity as an SDF-style production attribute:
/// this production may not occur as its own right (`@left`) / own left (`@right`) child.
///
/// A body SLOT's BSR triple is `(alternate start i, start of this symbol k, end j)`, measured on
/// `E = E "+" E | number` over `1 + 2 + 3` (slot numbers from that dump):
///
///     #2 N 'E'   first body symbol → (0,0,2) (0,0,6) (4,4,6)
///     #4 N 'E'   last  body symbol → (0,4,6) (0,4,9) (0,8,9) (4,8,9)
///     #5 END ''                    → (none)        ← END slots carry no yields
///
/// So on the LAST body symbol `[k, j]` is the right child and `[i, j]` is the whole alternate;
/// on the FIRST, `k == i` and `[i, j]` is the left child. `(0,4,9)` is exactly `1 + (2 + 3)` and
/// `(0,0,6)` is exactly `(1 + 2) + 3`, which is what each direction has to remove.
///
/// For bare `@left`/`@right` the forbidden extents are the `[i, j]` of the LAST body symbol — the
/// spans at which THIS production completed, excluding spans reached through a sibling
/// alternate (`1`, `2`, `3` via `number` are absent, which is what keeps the correct reading
/// alive). With operands they are the named nonterminals' extents.
///
/// They are read LIVE, once per `prune` call, never snapshotted. The question "does production p
/// occupy this span?" only has an answer after same-span ambiguity is settled, which is why this
/// rule runs in `.structure`, after `.sameSpan` (see `OraclePass`).
///
/// Reaches NESTED instances at different spans, which a pivot preference cannot: in
/// `x.map {} {}` the inner and outer closure-calls co-start but end differently, so no single
/// span has two pivots to rank. swift-syntax states the same rule procedurally —
/// `parsePostfixExpressionSuffix`, "We only allow a single trailing closure on a call".
struct AssociativityFilterRule: DisambiguationRule {
    /// A language constraint, but an anti-monotone one: it prunes because a witness EXISTS. Run
    /// before `@prefer` settles `f(1) {}` (paren alternate vs. parenless with callee `f(1)`), it
    /// takes `f(1) {}` for an instance of itself and wrongly breaks `f(1) {}`⏎`{}`.
    var pass: OraclePass { .structure }
    /// `[i, j]` spans the forbidden child occupies, read when the rule runs. Bare `@left`/`@right`
    /// passes the spans at which the annotated alternate itself completed; with operands it passes
    /// the spans of the named nonterminals.
    let forbiddenExtents: () -> Set<BinarySpanExtent>
    /// `@left` reads the right child `[k, j]`; `@right` reads the left child `[i, j]`.
    let childIsRightmost: Bool
    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        let extents = forbiddenExtents()
        guard !extents.isEmpty else { return 0 }
        var pruned = 0
        for span in yields {
            let child = childIsRightmost ? BinarySpanExtent(from: span.k, to: span.j)
                                         : BinarySpanExtent(from: span.i, to: span.j)
            if extents.contains(child) { yields.remove(span); pruned += 1 }
        }
        return pruned
    }
}

/// A plain `[from, to)` span — the extent of a BSR triple with its pivot dropped.
struct BinarySpanExtent: Hashable {
    let from: CharPosition
    let to: CharPosition
}

/// `@sameLineOutsideBrackets`. Prunes a yield unless at least one surviving derivation of that
/// yield crosses no line break in token-to-token trivia outside brackets: inside a body that opens
/// with `(`, `[` or `{` and closes with the matching token, every gap up to the closer may break the
/// line. Newlines INSIDE token content (a multiline string, a block comment) are never in a gap. A
/// trailing newline after the annotated span is also legal: only gaps before another token in the
/// same span are crossed.
///
/// Models swift-syntax's `ExprFlavor.poundIfDirective`. That flavor checks `atStartOfLine` only
/// along the expression spine — before a binary operator, its right operand and a postfix suffix
/// (`Expressions.swift` 160/181/201/780) — and every delimited form re-parses its contents as
/// `.basic` (1439, 2840). So `#if os(⏎macOS)` is clean and `#if A⏎|| B` is not.
///
/// The check is derivation-local. It tiles the candidate yield over the current BSR forest and, for
/// each terminal tile, reads that exact commit's trailing-trivia facts. It never asks "what commits
/// ended at this cursor?" globally, so dead or competing derivations cannot make a live same-line
/// derivation look as if it crossed a newline.
struct SameLineSpanRule: DisambiguationRule {
    var pass: OraclePass { .filter }
    /// Which token-to-token gaps of a sub-derivation may hold a line break.
    private enum Gaps: Hashable {
        case none       // no gap, not even the trailing one
        case trailing   // only the gap after the sub-derivation's last token
        case any        // every gap (inside brackets)
    }
    private struct NodeSpanMode: Hashable {
        let id: ObjectIdentifier
        let from: CharPosition
        let to: CharPosition
        let gaps: Gaps
    }

    let parser: MessageParser
    let node: GrammarNode

    /// Literal terminal names keep their quotes: the `"("` terminal is named `"("`.
    private static let closers: [String: String] = [#""(""#: #"")""#, #""[""#: #""]""#, #""{""#: #""}""#]

    /// The number of leading body symbols whose gaps are free: an opener up to (excluding) its
    /// matching closer. The closer and anything after it keep the enclosing policy.
    private func bracketedPrefix(_ body: [GrammarNode]) -> Int {
        guard let open = body.first, open.kind.isTerminal,
              let close = Self.closers[open.name],
              let c = body.lastIndex(where: { $0.kind.isTerminal && $0.name == close }), c > 0
        else { return 0 }
        return c
    }

    func prune(_ yields: inout Set<BinarySpan>) -> Int {
        let navigator = YieldNavigator(parser: parser)
        var nodeMemo: [NodeSpanMode: Bool] = [:]
        var nodeStack = Set<NodeSpanMode>()
        var symbolMemo: [NodeSpanMode: Bool] = [:]
        var closureMemo: [NodeSpanMode: Bool] = [:]
        // Cycle cuts. Re-entering an in-progress `(node, span)` answers `false` PROVISIONALLY: the
        // outer frame may still find a derivation. A `false` computed beneath such a cut is not a
        // fact and must not be memoised, or a same-span unit chain (`expression → … →
        // postfixExpression → … → expression`) caches "no derivation" for every node on the chain.
        // `true` is always a fact. So: memoise `false` only when no cut happened while computing it.
        var cycleCuts = 0
        func memoise(_ memo: inout [NodeSpanMode: Bool], _ key: NodeSpanMode, _ result: Bool, cutsBefore: Int) {
            if result || cycleCuts == cutsBefore { memo[key] = result }
        }

        func validNode(_ nt: GrammarNode, from: CharPosition, to: CharPosition, gaps: Gaps) -> Bool {
            let key = NodeSpanMode(id: ObjectIdentifier(nt), from: from, to: to, gaps: gaps)
            if let cached = nodeMemo[key] { return cached }
            guard nodeStack.insert(key).inserted else {
                cycleCuts += 1
                return false
            }
            defer { nodeStack.remove(key) }
            guard navigator.hasSpan(nt, i: from, j: to) else {
                nodeMemo[key] = false
                return false
            }
            let cutsBefore = cycleCuts
            var alt = nt.alt
            while let a = alt {
                defer { alt = a.alt }
                let body = a.bodySymbols.filter { $0.kind != .EPS }
                if body.isEmpty {
                    if from == to {
                        nodeMemo[key] = true
                        return true
                    }
                } else if validBody(body[...], from: from, to: to, gaps: gaps, freeCount: bracketedPrefix(body)) {
                    nodeMemo[key] = true
                    return true
                }
            }
            memoise(&nodeMemo, key, false, cutsBefore: cutsBefore)
            return false
        }

        func validSymbol(_ sym: GrammarNode, from: CharPosition, to: CharPosition, gaps: Gaps) -> Bool {
            let key = NodeSpanMode(id: ObjectIdentifier(sym), from: from, to: to, gaps: gaps)
            if let cached = symbolMemo[key] { return cached }
            let cutsBefore = cycleCuts
            let result: Bool
            switch sym.kind {
            case .T, .TI, .C:
                guard navigator.hasPivotSpan(sym, k: from, j: to) else {
                    result = false
                    break
                }
                guard gaps == .none,
                      let id = sym.nameID,
                      let gap = parser.terminalGapFacts(terminalID: id, triviaStart: from, triviaEnd: to) else {
                    result = true
                    break
                }
                result = !gap.contains(.lineBreak)
            case .B:
                result = navigator.hasPivotSpan(sym, k: from, j: to)
            case .EPS:
                result = from == to
            case .N:
                guard navigator.hasPivotSpan(sym, k: from, j: to), let lhs = sym.alt else {
                    result = false
                    break
                }
                result = validNode(lhs, from: from, to: to, gaps: gaps)
            case .DO, .OPT:
                if from == to, sym.kind == .OPT {
                    result = true
                } else {
                    result = validBracket(sym, from: from, to: to, gaps: gaps)
                }
            case .KLN, .POS:
                if from == to, sym.kind == .KLN {
                    result = true
                } else {
                    result = validClosure(sym, from: from, to: to, gaps: gaps)
                }
            default:
                result = true
            }
            memoise(&symbolMemo, key, result, cutsBefore: cutsBefore)
            return result
        }

        /// `freeCount`: how many leading symbols lie inside a bracket pair (`bracketedPrefix`) and so
        /// may break the line anywhere.
        func validBody(_ symbols: ArraySlice<GrammarNode>, from: CharPosition, to: CharPosition, gaps: Gaps,
                       freeCount: Int = 0) -> Bool {
            guard let first = symbols.first else { return from == to }
            let rest = symbols.dropFirst()
            let restFree = max(freeCount - 1, 0)
            for mid in navigator.endPositions(first, from: from).sorted() where mid <= to {
                // The head's trailing gap IS the span's trailing gap whenever the rest matches zero
                // width — not only when the head is syntactically last. `A⏎` in `expression` is
                // followed by empty `{ postfixSuffix }` etc.; no token follows, so nothing is crossed.
                let headGaps: Gaps = gaps == .any || freeCount > 0 ? .any : (mid == to ? gaps : .none)
                // SUFFIX FIRST. Validating the head before knowing the rest fits made a left-recursive
                // alternate visit its head over the WHOLE span — `explicitMemberExpression [a..b]`
                // checked `postfixExpression [a..b]`, which recursed straight back into the
                // in-progress `explicitMemberExpression [a..b]`. The cycle guard answered `false`, that
                // answer was MEMOISED for `postfixExpression [a..b]`, and the real derivation that
                // needed it later (`a.b<C>` as the base of `.d` in `"\(a.b<C>.d)"`) was pruned.
                // A split whose suffix cannot tile is never part of a derivation, so skip it before
                // recursing into the head.
                guard validBody(rest, from: mid, to: to, gaps: gaps, freeCount: restFree),
                      validSymbol(first, from: from, to: mid, gaps: headGaps) else {
                    continue
                }
                return true
            }
            return false
        }

        func validBracket(_ bracket: GrammarNode, from: CharPosition, to: CharPosition, gaps: Gaps) -> Bool {
            var alt = bracket.alt
            while let a = alt {
                defer { alt = a.alt }
                let body = a.bodySymbols.filter { $0.kind != .EPS }
                if body.isEmpty {
                    if from == to { return true }
                } else if validBody(body[...], from: from, to: to, gaps: gaps, freeCount: bracketedPrefix(body)) {
                    return true
                }
            }
            return false
        }

        func validClosure(_ bracket: GrammarNode, from: CharPosition, to: CharPosition, gaps: Gaps) -> Bool {
            let key = NodeSpanMode(id: ObjectIdentifier(bracket), from: from, to: to, gaps: gaps)
            if let cached = closureMemo[key] { return cached }
            let cutsBefore = cycleCuts
            if from == to {
                let result = bracket.kind == .KLN
                closureMemo[key] = result
                return result
            }
            for end in navigator.iterationEndPositions(bracket, from: from).sorted() where end > from && end <= to {
                let isLast = end == to
                if validBracket(bracket, from: from, to: end,
                                gaps: isLast || gaps == .any ? gaps : .none),
                   (isLast || validClosure(bracket, from: end, to: to, gaps: gaps)) {
                    closureMemo[key] = true
                    return true
                }
            }
            memoise(&closureMemo, key, false, cutsBefore: cutsBefore)
            return false
        }

        var pruned = 0
        for span in yields where !validNode(node, from: span.i, to: span.j, gaps: .trailing) {
            yields.remove(span)
            pruned += 1
        }
        return pruned
    }
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

    /// Per-phase checkpoint: is the root's full-span yield still present?
    ///
    /// This used to be asserted as an invariant ("pruning may reduce the number of derivations,
    /// never to zero"). That premise is false for this grammar: rejecting invalid input by removing
    /// its LAST reading is a deliberate mechanism — hard constraints (`@cannotParse`,
    /// `@sameLineOutsideBrackets`, …) and preferences such as literal munch do exactly that for every reject
    /// fixture. Once the assert ran in every configuration (2026-09-25) it fired on ~60 correct
    /// rejections per run. It is now a TRACE only: with `APUS_TRACE_ORACLE=1` the phase that
    /// removed the root is printed, which is what localises a genuine over-prune on VALID input
    /// (those still surface as `Advent failed to parse` in the accept suites).
    private func logRootStatus(_ phase: String) {
        guard traceRulePrunes else { return }
        let alive = parser.yield(of: grammar.root).contains {
            $0.i == input.startIndex && $0.j == input.endIndex
        }
        print("oracle-trace: after \(phase): root full-span yield \(alive ? "ALIVE" : "*** GONE ***")")
    }

    /// `@sameLineOutsideBrackets` — anchored on the LHS, whose completion yields have `i == k` and `j` =
    /// the true end, i.e. the exact span of the construct. A body-symbol anchor cannot work: its yield is
    /// `(i = production start, k = symbol start, j = SYMBOL end)`, so the first symbol gives too
    /// little and the last gives an extent that measured wrong in practice (6 valid inputs pruned).
    ///
    /// The prune removes LHS yields, so it applies to EVERY alternate of the annotated nonterminal.
    /// Put `@sameLineOutsideBrackets` only on a nonterminal whose alternates all need the rule.
    /// (An earlier "exactly one alternate" assertion was a proxy for this and is gone.)
    private func registerSameLine(nonTerminal nt: GrammarNode) {
        guard nt.sameLineOutsideBrackets else { return }
        rules.append((nt, SameLineSpanRule(parser: parser, node: nt)))
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
        for nt in grammar.allProductions {
            // Node-level extent (@longest/@shortest),
            // read off the owner node — for a nonterminal that is the production-start
            // form `@longest X = …` stored on `nt.disambiguation`.
            registerNodeDisambiguation(owner: nt)
            // Alternate-level @prefer / @avoid on the nonterminal's own alt chain.
            registerPrefer(altChainHead: nt.alt)
            // `@sameLineOutsideBrackets` — anchored on the LHS, see below.
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
                let targets = grammar.instances(of: predicate.targetName)
                if !targets.isEmpty, let anchor = node.bodySymbols.first {
                    // Snapshot RAW target starts NOW (Oracle init runs before dead-wood) — canParseAsXxx.
                    // Every parser-mode instance of the target counts: the question is whether `N`
                    // derives here at all, in whatever mode the parse reached it.
                    let targetStarts = Set(targets.flatMap { parser.yield(of: $0).map(\.i) })
                    rules.append((anchor, LookaheadPredicateRule(negated: predicate.negated,
                                                                 targetStarts: targetStarts)))
                } else {
                    reportInvariantViolation("lookahead predicate: unresolved target '\(predicate.targetName)' or empty alternate", once: true)
                }
            }
            // `@left`/`@right` on this alternate — the child-position FILTER. The ANCHOR is the
            // slot holding the forbidden child: the last body symbol for `@left`, the first for
            // `@right`.
            for filter in node.associativityFilters {
                let body = node.bodySymbols
                guard let last = body.last, let first = body.first else {
                    reportInvariantViolation("child-position filter on an empty alternate", once: true)
                    continue
                }
                let p = parser
                let extents: () -> Set<BinarySpanExtent>
                if filter.targets.isEmpty {
                    // Associativity. Extents come from the LAST body symbol — the only slot
                    // carrying both the alternate's own extent `[i, j]` and the right child's.
                    extents = { Set(p.yield(of: last).map { BinarySpanExtent(from: $0.i, to: $0.j) }) }
                } else {
                    // Argument-indexed priority. A nonterminal node's triples are `(i, i, j)`,
                    // so `[i, j]` is that nonterminal's extent.
                    let targets = filter.targets.flatMap { name -> [GrammarNode] in
                        let instances = grammar.instances(of: name)
                        if instances.isEmpty {
                            reportInvariantViolation("child-position filter: unknown nonterminal '\(name)'", once: true)
                        }
                        return instances
                    }
                    extents = {
                        Set(targets.flatMap { p.yield(of: $0).map { BinarySpanExtent(from: $0.i, to: $0.j) } })
                    }
                }
                rules.append((filter.direction == .left ? last : first,
                              AssociativityFilterRule(forbiddenExtents: extents,
                                                      childIsRightmost: filter.direction == .left)))
            }
            // `@sameLineOutsideBrackets` is registered per nonterminal, not here — it must
            // anchor on LHS completion yields to get the construct's exact span.
            // Every production is a root below, so an RHS reference (`.alt` → its LHS) is not
            // followed: that would make the recursion as deep as the whole grammar graph.
            if node.kind != .END { walk(node.seq) }
            if !node.isRHS { walk(node.alt) }
        }
        for nt in grammar.allProductions { walk(nt) }
    }

    /// Register node-level extent for an ALT-bearing `owner` (a
    /// nonterminal LHS or an inline `( )`/`[ ]`/`{ }`/`< >` cluster), reading the pragma
    /// off `owner.disambiguation` (set before the LHS in `production()` or before the
    /// bracket in `factor()`):
    ///   - extent (`@longest`/`@shortest`): register on the owner itself. Its yields from
    ///     a common start are what an extent rule prunes, and `endPositions` reads those
    ///     yields for `.N` nonterminals AND (now) `.OPT` brackets, so the prune propagates
    ///     through both the phase-1 cascade and the DerivationBuilder. (Closures still
    ///     recompute their transitive extent from the body, so extent on a `{ }`/`< >`
    ///     closure is not yet honored — a separate carrier problem.)
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
            // Unreachable: `production()`/`factor()` reject node-level `@left`/`@right`; they are
            // alternate-level child-position filters (`associativityFilters`).
            reportInvariantViolation("node-level @\(d.rawValue) reached the Oracle", once: true)
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
        // One pass per `OraclePass`, in order, each followed by a dead-wood sweep so the next pass
        // sees the previous one's kills propagated. Prunes are irreversible, so a rule that prunes
        // BECAUSE a rival exists must run after every pass that can still remove that rival — see
        // `OraclePass` for the order and the measured case behind each edge.
        var disambiguated = 0
        var interDead = 0
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
        for pass in OraclePass.allCases {
            let selected = rules.filter { $0.rule.pass == pass }
            guard !selected.isEmpty else { continue }
            let before = disambiguated
            runPass(selected)
            logRootStatus("\(pass) pass")
            // A pass that pruned nothing left the forest as the last sweep found it, so its sweep
            // would be a full-forest no-op. Skipping it is what keeps four passes at the cost of two.
            guard disambiguated > before else { continue }
            while true {
                let pruned = pruneUnsupported() + pruneUnproductive(endPosition: n)
                interDead += pruned
                if pruned == 0 { break }
            }
            logRootStatus("\(pass) dead-wood")
        }
        let total = deadYields + interDead + disambiguated
        if total > 0, parseReports {
            print("oracle: removed \(deadYields)+\(interDead) dead + \(disambiguated) disambiguated yields")
        }
        checkInvariant(isUnambiguous(endPosition: n), "Oracle postcondition violated: residual ambiguity remains")
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
            if !node.isRHS { collect(node.alt) }    // productions are all roots below
        }
        for nt in grammar.allProductions { collect(nt) }
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
/// Memo key for the `pruneUnproductive` walk: a body-symbol sequence over a span.
private struct TileKey: Hashable {
    let symbols: [ObjectIdentifier]
    let from, to: CharPosition
}

private struct IJPair: Hashable {
    let i: CharPosition
    let j: CharPosition
}

    // MARK: - Phase 1: Prune Unproductive Yields

    private func pruneUnproductive(endPosition n: CharPosition) -> Int {
        var reachable = Set<NodeSpan>()
        var expanding = Set<NodeSpan>()
        // Shared, indexed BSR navigation (`YieldNavigator.swift`) — a fresh snapshot per pass, since
        // the sweep at the end of this function mutates the yields.
        let navigator = YieldNavigator(parser: parser)
        func endPositions(_ sym: GrammarNode, from: CharPosition) -> Set<CharPosition> {
            navigator.endPositions(sym, from: from)
        }
        func iterEndPositions(_ bracket: GrammarNode, from: CharPosition) -> Set<CharPosition> {
            navigator.iterationEndPositions(bracket, from: from)
        }
        // Memo tables for the walk (2026-09-27). Without them `tileBody`, `bodyTiles` and
        // `visitBracket` re-derived the same (symbols, from, to) once per enclosing split point, which
        // made the walk ~cubic in the length of a statement or member list (200 statements: 30 s).
        // All three are safe to memoise unconditionally. `bodyTiles` is pure. The RETURN value of
        // `tileBody` is pure too (feasibility from `endPositions`/`bodyTiles`, never from `visit`),
        // and its marking side effects are idempotent: the only marks a cycle cut in `visit` skips
        // are those of the key currently being expanded, which its outer frame marks when it
        // completes. (A first version memoised only cut-free calls; cuts are so frequent that the
        // memo never engaged.)
        var bodyTilesMemo = [TileKey: Bool]()
        var tileBodyMemo = [TileKey: Bool]()
        var visitedBrackets = Set<NodeSpan>()
        func tileKey(_ symbols: [GrammarNode], _ from: CharPosition, _ to: CharPosition) -> TileKey {
            TileKey(symbols: symbols.map { ObjectIdentifier($0) }, from: from, to: to)
        }




        // Walk the BSR graph top-down. Returns true if any valid tiling
        // of `node`'s alternates covers [from, to].
        @discardableResult
        func visit(_ node: GrammarNode, from: CharPosition, to: CharPosition) -> Bool {
            let key = NodeSpan(id: ObjectIdentifier(node), from: from, to: to)
            if reachable.contains(key) { return true }
            guard expanding.insert(key).inserted else { return false }
            defer { expanding.remove(key) }

            guard navigator.hasSpan(node, i: from, j: to) else { return false }

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
            let key = tileKey(symbols, from, to)
            if let hit = bodyTilesMemo[key] { return hit }
            let result = bodyTilesUncached(symbols, from: from, to: to)
            bodyTilesMemo[key] = result
            return result
        }

        func bodyTilesUncached(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> Bool {
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
            let key = tileKey(symbols, from, to)
            if let hit = tileBodyMemo[key] { return hit }
            let result = tileBodyUncached(symbols, from: from, to: to)
            tileBodyMemo[key] = result
            return result
        }

        func tileBodyUncached(_ symbols: [GrammarNode], from: CharPosition, to: CharPosition) -> Bool {
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
            if navigator.hasSpan(sym, i: from, j: to) || navigator.hasPivotSpan(sym, k: from, j: to) {
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
            let key = NodeSpan(id: ObjectIdentifier(bracket), from: from, to: to)
            if from == to {
                // A zero-width span. For a closure it is the skip: there is no iteration to walk.
                // A `( … )` / `[ … ]` is one pass, and that pass may legitimately consume nothing
                // through a zero-width alternate — `( clause | >-> ( openAngle ) )`. Returning
                // early here (as it once did for every bracket) left that alternate's gate yield
                // unmarked, the sweep deleted it, and `pruneUnsupported` cascaded the loss to the
                // root: every type in the grammar underaccepted (2026-10-04).
                guard !bracket.kind.isClosure, visitedBrackets.insert(key).inserted else { return }
                if visitAlternates(bracket, from: from, to: to) { reachable.insert(key) }
                return
            }
            guard visitedBrackets.insert(key).inserted else { return }
            // For a non-closure bracket, iterate the bracket's OWN (Oracle-pruned) end
            // positions — so an extent prune on the bracket is honored by the reachability
            // walk and dead sibling/prefix yields get removed ("walk the rest of the
            // sequence to kill dead paths"). Using `iterEndPositions` (body recompute) here
            // re-marked extent-pruned spans reachable, leaving stale readings that kept an
            // enclosing pivot ambiguous. Closures still step per-iteration (their own ends
            // are transitive, not single-step) and recurse below.
            //
            // A NON-closure bracket (`X?`, `( … )`) is ONE iteration, so only `end == to` belongs to a
            // derivation of [from, to] (2026-09-27). Visiting every `end <= to` walked and marked
            // prefixes in no derivation — for `statements?` in `codeBlock`, `statements(from, j)` for
            // every statement boundary j: O(n²) on an n-statement block (400 statements: 187 s → 4.5 s).
            // CLOSURE iterations deliberately still visit every iteration end, even ones from which
            // `to` is unreachable: the dead extents this keeps alive are what `@longest` compares
            // against (maximal munch, e.g. `value as A<B>??x` must see the dead `as A<B>??`). Pruning
            // them made those casts accepted. TODO.md / whole-file parsing: make that dependency
            // explicit instead of relying on the walk's over-marking.
            let ends = bracket.kind.isClosure
                ? iterEndPositions(bracket, from: from)
                : endPositions(bracket, from: from)
            for end in ends where end <= to && end > from {
                if !bracket.kind.isClosure, end != to { continue }
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
            if !node.isRHS { collect(node.alt) }    // productions are all roots below
        }

        for nt in grammar.allProductions {
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
