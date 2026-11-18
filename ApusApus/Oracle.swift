//
//  Oracle.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.05.04.
//

// Post-parse disambiguator operating entirely on BSR yield sets, in the three phases of
// Bend/SPEC.bend: admissible (lookahead, @left, @right), unbeaten (@prefer, @avoid), selected
// (@longest, @shortest). The rules are yield filters; dead wood is handled by one graph of the
// yields (`YieldGraph`): support from below and reachability from the root, both linear.

import Foundation

// MARK: - Disambiguation Rule

protocol DisambiguationRule {
    func prune(_ yields: inout Set<BinarySpan>) -> Int
    /// The pass this rule runs in. Deliberately has NO default: a default (`isHardConstraint =
    /// true`) once filed five preferences into the wrong pass without anyone noticing.
    var pass: OraclePass { get }
}

/// The Oracle's rule passes, in run order: the phases of Bend/SPEC.bend. Phase 1 (admissible)
/// is `filter`, phase 2 (unbeaten) is `sameSpan`; phase 3 (`@longest`,
/// `@shortest`) is not a rule pass but `YieldGraph.extent`, on genuine readings only. Each pass
/// is followed by support from below (`YieldGraph.support`), so the next pass sees genuine
/// rivals. The hard rules come first because they never look at a rival; `@prefer`/`@avoid` and
/// extent prune BECAUSE a rival exists, so they run after everything that can remove it.
enum OraclePass: Int, CaseIterable {
    /// Language constraints read off the raw forest at init: `>?>`/`>!>`, and `@left`/`@right`.
    case filter
    /// Same-span choice among sibling alternates: `@prefer`, `@avoid` (explicit siblings).
    case sameSpan
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

private struct SpanKey: Hashable {
    let i: CharPosition
    let j: CharPosition
}

/// Parse predicate `>!>(N)` / `>?>(N)` with a nonterminal operand (see
/// `Ambiguity.md`). Anchored on the alternate's FIRST body symbol,
/// whose yield start `i` is the alternate start. For each such yield, ask the Way-1 BSR
/// question "does `N` derive at `i`?" (`∃` a target yield with `.i == i`) and prune when the
/// predicate fails: negative (`>!>`) fails where `N` DOES derive here; positive
/// (`>?>`) fails where it does NOT. Removal cascades to the whole alternate via the
/// dead-wood sweep.
struct LookaheadPredicateRule: DisambiguationRule {
    var pass: OraclePass { .filter }
    let negated: Bool
    /// Start positions where the target derives a prefix of the rest (Bend/SPEC.bend: plain derives,
    /// the target's own predicates do not count), SNAPSHOT from the RAW forest at Oracle registration
    /// (before dead-wood); the parser probed the target at every start of the alternate
    /// (`MessageParser.probe`). This is swift-syntax's `canParseAsXxx`: a SPECULATIVE "could N parse
    /// here?", independent of whether the enclosing parse survives — so a target that lexes/parses
    /// but whose enclosing parse fails still counts (e.g. `/foo/` in `_ = /foo/ {}`, C3). The
    /// resulting prune cascades to a reject through support from below (`YieldGraph.support`).
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
/// With operands (`@right(literalExpression …)`) the forbidden extents are the named
/// nonterminals' extents, read from the RAW forest at Oracle init (Bend/SPEC.bend `EdgeOk`: "no
/// listed nonterminal derives the edge child's tokens"), so the rule does not depend on what other
/// passes remove. Bare `@left`/`@right` forbids the alternate's own raw completions the same way
/// (`EdgeOk`: plain derives, its own filters do not count).
///
/// Reaches NESTED instances at different spans, which a pivot preference cannot: in
/// `x.map {} {}` the inner and outer closure-calls co-start but end differently, so no single
/// span has two pivots to rank. swift-syntax states the same rule procedurally —
/// `parsePostfixExpressionSuffix`, "We only allow a single trailing closure on a call".
struct AssociativityFilterRule: DisambiguationRule {
    var pass: OraclePass { .filter }
    /// `[i, j]` spans of the named nonterminals in the raw forest.
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
    // Read once (as `parseReports`): reading the environment per rule was half the Oracle's
    // time on small inputs.
    private static let traceRulePrunesEnabled = ProcessInfo.processInfo.environment["APUS_TRACE_ORACLE"] == "1"
    private var traceRulePrunes: Bool { Oracle.traceRulePrunesEnabled }

    private func describe(_ span: BinarySpan) -> String {
        // Character offsets, as before positions became UTF-8 offsets: these appear in reports.
        let i = input[positions: 0..<span.i].count
        let j = input[positions: 0..<span.j].count
        let text = input[positions: span.i..<span.j].replacingOccurrences(of: "\n", with: "⏎")
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
    /// its LAST reading is a deliberate mechanism — hard constraints such as `>!>` and
    /// preferences such as literal munch do exactly that for every reject
    /// fixture. Once the assert ran in every configuration (2026-09-25) it fired on ~60 correct
    /// rejections per run. It is now a TRACE only: with `APUS_TRACE_ORACLE=1` the phase that
    /// removed the root is printed, which is what localises a genuine over-prune on VALID input
    /// (those still surface as `Advent failed to parse` in the accept suites).
    private func logRootStatus(_ phase: String) {
        guard traceRulePrunes else { return }
        let alive = !parser.acceptingEnds(of: parser.currentParseRoot ?? grammar.root, from: 0).isEmpty
        print("oracle-trace: after \(phase): root reading \(alive ? "ALIVE" : "*** GONE ***")")
    }


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
        var seen = Set<ObjectIdentifier>()
        func walk(_ node: GrammarNode?) {
            guard let node, seen.insert(ObjectIdentifier(node)).inserted else { return }
            if node.kind.isBracket {
                registerNodeDisambiguation(owner: node)
                registerPrefer(altChainHead: node.alt)
            }
            // Leading parse predicate on an ALT node (`>!>(N)`/`>?>(N)`, N a
            // nonterminal). Anchor the prune on the alternate's first body symbol.
            // Repeatable: each predicate becomes its own rule on the same anchor, so they compose as
            // a CONJUNCTION (every rule prunes independently).
            for predicate in node.forwardPredicates {
                if let target = predicate.target, let anchor = node.bodySymbols.first {
                    // The parser probed the target at every start of this alternate
                    // (`MessageParser.probe`), so its raw completions say exactly where it derives
                    // a prefix of the rest. Snapshot NOW, before dead wood is removed.
                    rules.append((anchor, LookaheadPredicateRule(negated: predicate.negated,
                                                                 targetStarts: Set(parser.yield(of: target).map(\.i)))))
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
                    // Bare: the alternate itself, as the parser probed it where the edge child
                    // starts (`slotProbes`; for `@right` it is parsed there anyway). Its raw
                    // completions are its body yields chained by `(i, k)`.
                    var reached = Set<BinarySpanExtent>()
                    for (m, sym) in body.enumerated() {
                        var next = Set<BinarySpanExtent>()
                        for y in p.yield(of: sym) where m == 0 || reached.contains(BinarySpanExtent(from: y.i, to: y.k)) {
                            next.insert(BinarySpanExtent(from: y.i, to: y.j))
                        }
                        reached = next
                    }
                    let raw = reached
                    extents = { raw }
                } else {
                    // Argument-indexed priority. A nonterminal node's triples are `(i, i, j)`,
                    // so `[i, j]` is that nonterminal's extent.
                    // The targets as the parser probed them where the edge child starts
                    // (`slotProbes`), so their raw yields say exactly what they derive there.
                    if filter.targetNodes.count != filter.targets.count {
                        reportInvariantViolation("child-position filter: unknown nonterminal in \(filter.targets)", once: true)
                    }
                    let raw = Set(filter.targetNodes.flatMap { p.yield(of: $0).map { BinarySpanExtent(from: $0.i, to: $0.j) } })
                    extents = { raw }
                }
                rules.append((filter.direction == .left ? last : first,
                              AssociativityFilterRule(forbiddenExtents: extents,
                                                      childIsRightmost: filter.direction == .left)))
            }
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
            break   // `YieldGraph.extent` finds the marked occurrences itself.
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
    ///   - `@avoid` names a LOSER: it is the dual — an avoided alternate is pruned where a
    ///     sibling that is not avoided covers the same `(i, j)`, i.e. `@avoid A` ≡ `@prefer`
    ///     on all of A's siblings (in a chain without `@prefer`). Inside `[ … ]` or `{ … }` the skip is not a sibling:
    ///     `@avoid` never ranks taking the bracket against skipping it (that is `@shortest`).
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

        // @avoid (alt-prefix): an avoided alternate loses to its siblings that are not avoided.
        // Two avoided siblings have the same rank and both stay (Bend/SPEC.bend, `outranks`):
        // letting each lose to the other made the survivor depend on rule order.
        for a in alts where a.isAvoided {
            let siblingsLast = alts.filter { !$0.isAvoided }.compactMap { $0.bodySymbols.last }
            if let last = a.bodySymbols.last, !siblingsLast.isEmpty {
                rules.append((last, PreferRule(preferredLastSymbols: siblingsLast,
                                               yieldsOf: { p.yield(of: $0) })))
            }
        }
    }

    @discardableResult
    func disambiguate() -> Int {
        // The readings the callers accept (`MessageParser.acceptingEnds`): of the root the parse ran
        // (a sub-grammar root in some tests), ending at the input's end or before trailing trivia.
        let root = parser.currentParseRoot ?? grammar.root
        let origin: CharPosition = 0
        let ends = parser.acceptingEnds(of: root, from: origin)
        guard !ends.isEmpty else {
            // No reading, so the result is empty: what the parse left is dead ends and probe calls
            // (a `>!>` the parser already applied can remove the last reading itself).
            var removed = 0
            for num in parser.yields.indices where !parser.yields[num].isEmpty {
                removed += parser.yields[num].count
                parser.yields[num].removeAll()
            }
            return removed
        }

        // The phases of Bend/SPEC.bend over one graph of the yields (`YieldGraph`), built once.
        // Dead wood may stay between phases (each Bend phase's law is "embeds exactly"); what a
        // phase reads is made genuine first: support from below before every rule pass, and
        // reachability from the root before extent, which ranks whole readings (Bend `prunedFrom`).
        let graph = YieldGraph(grammar: grammar, parser: parser, input: input)
        let before = graph.liveCount
        var disambiguated = 0
        for p in OraclePass.allCases {
            let selected = rules.filter { $0.rule.pass == p }
            var changedNodes = Set<Int>()
            var changed = !selected.isEmpty
            while changed {
                changed = false
                for (node, rule) in selected {
                    // Copy out / write back: a rule's `yieldsOf` closure reads other nodes' yields
                    // out of `parser.yields` (law of exclusivity).
                    var spans = parser.yields[node.number]
                    let old = traceRulePrunes ? spans : []
                    let pruned = rule.prune(&spans)
                    guard pruned > 0 else { continue }
                    parser.yields[node.number] = spans
                    if traceRulePrunes { logRulePrune(rule: rule, node: node, removed: old.subtracting(spans)) }
                    disambiguated += pruned
                    changedNodes.insert(node.number)
                    changed = true
                }
            }
            logRootStatus("\(p) pass")
            guard !changedNodes.isEmpty else { continue }
            graph.exclude(missingFrom: changedNodes)
            graph.support()
            graph.write(reachableOnly: false)
            logRootStatus("\(p) support")
        }
        // Phase 3 on genuine readings, then the result: exactly the yields on complete readings.
        graph.support()
        graph.reach(from: root, origin: origin, ends: ends)
        // Marks of one sequence left to right: each rank among the readings the earlier ranks kept.
        var rank = 0
        while true {
            let (removed, more) = graph.extent(rank: rank)
            if removed > 0 {
                graph.support()
                graph.reach(from: root, origin: origin, ends: ends)
            }
            guard more else { break }
            rank += 1
        }
        graph.write(reachableOnly: true)
        logRootStatus("extent and dead wood")
        let total = before - graph.liveCount
        if total > 0, parseReports {
            print("oracle: removed \(total) yields (\(disambiguated) by rules)")
        }
        // Residual ambiguity is not checked here: an ambiguous grammar without pragmas leaves it on
        // purpose. `DerivationBuilder.diagnostics` reports every ambiguous choice of the result.
        return total
    }
}

// MARK: - The yield graph

/// The BSR yields as the AND-OR graph they form, built once per Oracle.
///
/// A KEY (OR-node) is a symbol occurrence with a span, `(node, i, j)`: the occurrence ends at `j`
/// in a sequence that starts at `i` (for a left-hand nonterminal: a completion over `[i, j]`).
/// A YIELD `(i, k, j)` (AND-node) belongs to the key `(node, i, j)` and stands on two
/// requirements:
///   - its prefix: the previous body symbol's key `(pred, i, k)`; nothing for the first symbol,
///     except a later loop round, which needs the round before it: `(group, i, k)`;
///   - its content: for a nonterminal reference the left-hand key `(X, k, j)`; for a bracket the
///     key of some alternative's last symbol `(last, k, j)`; for a loop its round group
///     `(group, k, j)`; for a completion some alternative's last symbol `(last, i, j)`; nothing for
///     a token, a gate, a skip or an empty alternative.
/// A key stands when one of its yields does. Support from below is the least fixpoint of that
/// (counters, one forward pass); reachability from the root follows required keys down. A yield
/// that is both is on a complete reading, so the two passes leave exactly the parse's yields.
private final class YieldGraph {
    private struct Key: Hashable { let node: Int; let i, j: CharPosition }
    private let parser: MessageParser
    private let input: String

    // Grammar shape, by node number.
    private var nodeOf: [GrammarNode?]
    private var body: [[Int]] = []                 // every alternative's body symbols
    private var altOf: [Int]                       // body symbol → index into `body`
    private var posOf: [Int]                       // body symbol → position in its body
    private var lastsOf: [[Int]]                   // definition → its alternatives' last symbols
    private var emptyAlt: [Bool]                   // definition has an alternative that reads nothing
    private var roundOf: [Int]                     // loop → its round group
    private var isRound: [Bool]                    // a loop's round group

    // Yields.
    private var yNode: [Int] = []
    private var ySpan: [BinarySpan] = []
    private var yKey: [Int] = []
    private var yPrefix: [Int] = []                // a key, or `free`, or `never`
    private var yContent: [[Int]] = []             // some key of these, unless `yFree`
    private var yFree: [Bool] = []
    private var excluded: [Bool] = []
    private var alive: [Bool] = []
    private var reached: [Bool] = []
    private var yieldsOfNode: [[Int]]

    // Keys.
    private var keyIndex: [Key: Int] = [:]
    private var members: [[Int]] = []
    private var users: [[Int]] = []                // 2·yield (+1 for content) of the yields needing it
    private var liveMembers: [Int] = []
    private var keysOfNode: [[Int]]

    private static let free = -1, never = -2

    var liveCount: Int { parser.yields.reduce(0) { $0 + $1.count } }

    init(grammar: Grammar, parser: MessageParser, input: String) {
        self.parser = parser
        self.input = input
        let count = parser.yields.count
        nodeOf = Array(repeating: nil, count: count)
        altOf = Array(repeating: -1, count: count)
        posOf = Array(repeating: -1, count: count)
        lastsOf = Array(repeating: [], count: count)
        emptyAlt = Array(repeating: false, count: count)
        roundOf = Array(repeating: -1, count: count)
        isRound = Array(repeating: false, count: count)
        yieldsOfNode = Array(repeating: [], count: count)
        keysOfNode = Array(repeating: [], count: count)

        // The grammar's nodes, and every definition's alternatives.
        var nodes: [GrammarNode] = []
        func collect(_ node: GrammarNode?) {
            guard let node, node.number < count, nodeOf[node.number] == nil else { return }
            nodeOf[node.number] = node
            nodes.append(node)
            if node.kind != .END { collect(node.seq) }
            if !node.isRHS { collect(node.alt) }
        }
        for nt in grammar.allProductions { collect(nt) }
        collect(grammar.root)
        for def in nodes where def.isLHS || def.kind.isBracket {
            if def.kind == .OPT || def.kind == .KLN { emptyAlt[def.number] = true }
            var alt = def.alt
            while let a = alt {
                defer { alt = a.alt }
                let symbols = a.bodySymbols
                guard !symbols.isEmpty else { continue }
                if symbols.allSatisfy({ $0.kind == .EPS }) { emptyAlt[def.number] = true }
                lastsOf[def.number].append(symbols[symbols.count - 1].number)
                for (m, sym) in symbols.enumerated() where sym.number < count {
                    altOf[sym.number] = body.count
                    posOf[sym.number] = m
                }
                body.append(symbols.map(\.number))
            }
        }
        for node in nodes where node.isLoopRound {
            isRound[node.number] = true
            if let loop = node.seq?.seq, loop.number < count { roundOf[loop.number] = node.number }
        }

        // Yields and their keys.
        for node in nodes where !parser.yields[node.number].isEmpty {
            for y in parser.yields[node.number] {
                let id = yNode.count
                yNode.append(node.number)
                ySpan.append(y)
                let k = key(node.number, y.i, y.j, create: true)
                yKey.append(k)
                members[k].append(id)
                yieldsOfNode[node.number].append(id)
            }
        }
        // Their requirements.
        for id in yNode.indices {
            let num = yNode[id], y = ySpan[id], node = nodeOf[num]!
            var prefix = YieldGraph.free
            var content: [Int] = []
            var isFree = true
            func need(_ node: Int, _ i: CharPosition, _ j: CharPosition) {
                isFree = false
                let k = key(node, i, j, create: false)
                if k >= 0 { content.append(k) }
            }
            // The alternatives' last symbols; an empty alternative's ε counts too, so that
            // reachability reaches it, but over an empty span the content needs nothing.
            func lasts(of def: Int, _ i: CharPosition, _ j: CharPosition) {
                isFree = i == j && emptyAlt[def]
                for last in lastsOf[def] {
                    let k = key(last, i, j, create: false)
                    if k >= 0 { content.append(k) }
                }
            }
            if !node.isLHS, posOf[num] >= 0 {
                let m = posOf[num]
                if m > 0 {
                    prefix = key(body[altOf[num]][m - 1], y.i, y.k, create: false)
                    if prefix < 0 { prefix = YieldGraph.never }
                } else if isRound[num], y.k != y.i {
                    prefix = key(num, y.i, y.k, create: false)
                    if prefix < 0 { prefix = YieldGraph.never }
                }
            }
            // No removable empty rounds (Bend/SPEC.bend `roundsOk`): a round that reads nothing is
            // in a parse tree only as the first, and then only, round of a `< >`. The parser still
            // predicts later empty `< >` rounds (`addDescriptorsForAlternates`); without this rule
            // such a round's key supported itself, an SPPF cycle of repeated nothing.
            if isRound[num], y.k == y.j, !(node.seq?.seq?.kind == .POS && y.k == y.i) {
                prefix = YieldGraph.never
            }
            switch node.kind {
            case .N where node.isLHS:
                lasts(of: num, y.i, y.j)
            case .N:
                if let lhs = node.alt, lhs.number < count { need(lhs.number, y.k, y.j) }
            case .OPT where y.k == y.j:
                break                          // `[ ]` over nothing is a skip, not an empty pick
            case .DO, .OPT:
                lasts(of: num, y.k, y.j)
            case .KLN, .POS:
                if node.kind == .KLN, y.k == y.j { break }
                if roundOf[num] >= 0 { need(roundOf[num], y.k, y.j) }
            default:
                break                          // tokens, gates, ε: nothing below
            }
            yPrefix.append(prefix)
            yContent.append(content)
            yFree.append(isFree)
            if prefix >= 0 { users[prefix].append(2 * id) }
            for k in content { users[k].append(2 * id + 1) }
        }
        excluded = Array(repeating: false, count: yNode.count)
        alive = Array(repeating: true, count: yNode.count)
        reached = Array(repeating: true, count: yNode.count)
        liveMembers = members.map(\.count)
    }

    private func key(_ node: Int, _ i: CharPosition, _ j: CharPosition, create: Bool) -> Int {
        let k = Key(node: node, i: i, j: j)
        if let id = keyIndex[k] { return id }
        guard create else { return -1 }
        let id = members.count
        keyIndex[k] = id
        members.append([])
        users.append([])
        keysOfNode[node].append(id)
        return id
    }

    /// Takes out the yields a rule removed from `parser.yields` on these nodes.
    func exclude(missingFrom nodes: Set<Int>) {
        for num in nodes {
            let kept = parser.yields[num]
            for id in yieldsOfNode[num] where !excluded[id] && !kept.contains(ySpan[id]) {
                excluded[id] = true
            }
        }
    }

    /// Support from below: the least fixpoint, by counters. A yield stands when its prefix key and
    /// one of its content keys stand; a key stands when one of its yields does.
    func support() {
        alive = Array(repeating: false, count: yNode.count)
        liveMembers = Array(repeating: 0, count: members.count)
        var waiting = [UInt8](repeating: 0, count: yNode.count)
        var contentMet = [Bool](repeating: false, count: yNode.count)
        var ready: [Int] = []
        for id in yNode.indices where !excluded[id] {
            if yPrefix[id] == YieldGraph.never || (!yFree[id] && yContent[id].isEmpty) { continue }
            waiting[id] = (yPrefix[id] >= 0 ? 1 : 0) + (yFree[id] ? 0 : 1)
            if waiting[id] == 0 { ready.append(id) }
        }
        while let id = ready.popLast() {
            alive[id] = true
            let k = yKey[id]
            liveMembers[k] += 1
            guard liveMembers[k] == 1 else { continue }
            for use in users[k] {
                let user = use >> 1
                if excluded[user] || alive[user] || waiting[user] == 0 { continue }
                if use & 1 == 1 {
                    if yFree[user] || contentMet[user] { continue }
                    contentMet[user] = true
                }
                waiting[user] -= 1
                if waiting[user] == 0 { ready.append(user) }
            }
        }
        reached = alive
    }

    /// Reachability from the root's accepted readings, through the keys the standing yields need.
    func reach(from root: GrammarNode, origin: CharPosition, ends: Set<CharPosition>) {
        reached = Array(repeating: false, count: yNode.count)
        var keyReached = [Bool](repeating: false, count: members.count)
        var stack: [Int] = []
        func push(_ k: Int) {
            guard k >= 0, !keyReached[k], liveMembers[k] > 0 else { return }
            keyReached[k] = true
            stack.append(k)
        }
        for end in ends { push(key(root.number, origin, end, create: false)) }
        while let k = stack.popLast() {
            for id in members[k] where alive[id] {
                reached[id] = true
                push(yPrefix[id])
                for c in yContent[id] { push(c) }
            }
        }
    }

    /// The extent mark of a body symbol: a marked bracket, or a reference to a marked nonterminal
    /// (`@longest X = …` marks every reference of X).
    private func extentMark(_ s: GrammarNode) -> Disambiguation? {
        let mark = s.kind.isBracket ? s.disambiguation : (s.kind == .N && !s.isLHS ? s.alt?.disambiguation : nil)
        return mark == .longest || mark == .shortest ? mark : nil
    }

    /// `@longest`/`@shortest` of rank `rank`, on the reached yields (Bend/EXTENT.bend): the
    /// `rank`-th marked item of every sequence, counted from 0, left to right. In every reading of
    /// its sequence over `[i, e]` the item takes its best length among the readings of that same
    /// sequence; a reading of the item that is best in no reading of its sequence is removed.
    /// Returns how many yields it removed, and whether any sequence has a mark of a higher rank.
    ///
    /// Several marks in one sequence are served left to right (Bend/SPEC.bend, phase 3): the caller
    /// runs rank 0, removes what no longer stands, then rank 1 among the readings that are left, and
    /// so on. Applying them all at once could keep a different reading for each mark, and no reading
    /// for the sequence (`S = A A . @longest A = { a } .` on `a a`).
    func extent(rank: Int) -> (removed: Int, more: Bool) {
        var removed = 0, more = false
        for case let s? in nodeOf where posOf[s.number] >= 0 {
            guard let d = extentMark(s) else { continue }
            let seq = body[altOf[s.number]]
            var before = 0
            for m in seq.prefix(posOf[s.number]) where nodeOf[m].flatMap(extentMark) != nil { before += 1 }
            if before == rank { removed += extent(of: s.number, longest: d == .longest) }
            else if before > rank { more = true }
        }
        return (removed, more)
    }

    private func extent(of s: Int, longest: Bool) -> Int {
        let seq = body[altOf[s]], at = posOf[s]
        func length(_ id: Int) -> Int { ySpan[id].j - ySpan[id].k }
        // The lengths the occurrence can have in the readings that reach each key from `at` on.
        var lengths: [Int: Set<Int>] = [:]
        func lengthsAt(_ k: Int) -> Set<Int> {
            if let known = lengths[k] { return known }
            var result = Set<Int>()
            for id in members[k] where reached[id] {
                if posOf[yNode[id]] == at { result.insert(length(id)) }
                else if yPrefix[id] >= 0 { result.formUnion(lengthsAt(yPrefix[id])) }
            }
            lengths[k] = result
            return result
        }
        var best = Set<Int>()                       // occurrence yields that are best somewhere
        var visited = Set<[Int]>()
        func keep(_ k: Int, _ target: Int) {
            guard visited.insert([k, target]).inserted else { return }
            for id in members[k] where reached[id] {
                if posOf[yNode[id]] == at {
                    if length(id) == target { best.insert(id) }
                } else if yPrefix[id] >= 0, lengthsAt(yPrefix[id]).contains(target) {
                    keep(yPrefix[id], target)
                }
            }
        }
        for c in keysOfNode[seq[seq.count - 1]] {
            let options = lengthsAt(c)
            guard let target = longest ? options.max() : options.min() else { continue }
            keep(c, target)
        }
        var removed = 0
        for id in yieldsOfNode[s] where reached[id] && !best.contains(id) {
            excluded[id] = true
            removed += 1
        }
        return removed
    }

    /// Writes the standing (and, with `reachableOnly`, reached) yields back to `parser.yields`.
    func write(reachableOnly: Bool) {
        for (num, ids) in yieldsOfNode.enumerated() where !ids.isEmpty {
            var kept = Set<BinarySpan>(minimumCapacity: ids.count)
            for id in ids where !excluded[id] && (reachableOnly ? reached[id] : alive[id]) {
                kept.insert(ySpan[id])
            }
            parser.yields[num] = kept
        }
    }
}
