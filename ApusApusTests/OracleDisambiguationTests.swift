//
//  OracleDisambiguationTests.swift
//  AdventTests
//
//  Oracle disambiguation pragmas (`@left`, `@right`, `@longest`, `@shortest`,
//  `@prefer`, `@avoid`). Two groups:
//
//  1. `TopLevel` — the pre-existing tests, extracted verbatim from
//     `CoreGrammarTests.OracleDisambiguation`. They lock in the behaviour of a
//     pragma attached to a *nonterminal* (or an OPT/POS immediately under one).
//
//  2. `NestedCluster` — the NEW capability being built on this branch: the same
//     pragmas working when attached inside an inline alternate cluster
//     `( a | b )` / `[ … ]` / `{ … }` / `< … >`, not just at the top level of a
//     nonterminal. See `Ambiguity.md`.
//
//     All pragmas attach to an ALT node (an alternate) as a prefix — `@prefer`
//     via `isPreferred`, the others via `alt.disambiguation`, both parsed in
//     `sequence()`. Since a nonterminal AND every bracket own an alternate chain,
//     the Oracle reads these annotations off any chain uniformly
//     (`registerPrefer` + `registerAltDisambiguation`), so no pragma is special
//     about "top level". The legacy production-start form (`@longest X = …`) still
//     works via `nt.disambiguation`.
//
//     Tier A — `@prefer` inside a `( a | b )` selection group.
//     Tier B — `@longest`/`@shortest`/`@left`/`@right` attached to a cluster,
//     e.g. `( @left E "+" E | n )`, `< @longest word >`, `{ @longest word }`.
//     Both tiers are implemented; these tests assert them directly.
//

import Testing
import Foundation

@Suite("Oracle Disambiguation", .serialized)
struct OracleDisambiguationTests {


    // MARK: - Top-level pragmas (extracted, behaviour lock)

    @Suite("Top-level pragmas", .serialized)
    struct TopLevel {

        @Test("@left prunes ambiguous expression")
        func leftAssocPrunes() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . E = @left E "+" E | number ."#,
                message: "1 + 2 + 3"
            )
            #expect(matches, "1 + 2 + 3 should parse")
            #expect(pruned > 0, "Oracle should prune right-associative derivation")
        }

        @Test("@right prunes ambiguous expression")
        func rightAssocPrunes() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . E = @right E "+" E | number ."#,
                message: "1 + 2 + 3"
            )
            #expect(matches, "1 + 2 + 3 should parse")
            #expect(pruned > 0, "Oracle should prune left-associative derivation")
        }

        @Test("no annotation means no pivot pruning")
        func noAnnotationNoPrune() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . E = E "+" E | number ."#,
                message: "1 + 2 + 3"
            )
            #expect(matches, "1 + 2 + 3 should parse")
            #expect(pruned == 0, "Oracle should not prune without annotation")
        }

        @Test("unambiguous input needs no pruning")
        func unambiguousNoPrune() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . E = @left E "+" E | number ."#,
                message: "1 + 2"
            )
            #expect(matches, "1 + 2 should parse")
            #expect(pruned == 0, "Unambiguous input should not need pruning")
        }

        @Test("@left with four operands")
        func leftAssocFourOperands() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . E = @left E "+" E | number ."#,
                message: "1 + 2 + 3 + 4"
            )
            #expect(matches, "1 + 2 + 3 + 4 should parse")
            #expect(pruned > 0, "Oracle should prune non-left-associative derivations")
        }

        @Test("@longest still works (extent disambiguation)")
        func longestExtent() throws {
            let (matches, _) = try parseAndDisambiguate(
                grammar: #"word - /[a-z]+/ . @longest S = < word > ."#,
                message: "hello world foo"
            )
            #expect(matches)
            // Longest keeps only the maximum extent for each start position
        }

        // A `@prefer` alternate nested inside an `?` OPT must NOT over-prune: the
        // multi-element reading has to survive disambiguation. (Regression: a Swift.apus
        // subscript `a[0, 1]` was thought to hit a `@prefer`+OPT engine limitation; a
        // minimal repro proved `@prefer` under an OPT is sound — this locks that in.)
        @Test("@prefer under an OPT keeps empty / single / multi (flat)")
        func preferUnderOptFlat() throws {
            let g = #"item - /[a-z]/ . S = "[" list? "]" . list = @prefer item | item "," list ."#
            for msg in ["[]", "[a]", "[a, b]", "[a, b, c]"] {
                let r = try parsePostOracle(grammar: g, message: msg)
                #expect(r.postMatch, "@prefer under OPT dropped a valid parse for '\(msg)'")
            }
        }

        @Test("@prefer under an OPT keeps multi under left recursion")
        func preferUnderOptLeftRecursive() throws {
            let g = #"atom - /[a-z]/ . S = atom | S "[" list? "]" . list = @prefer item | item "," list . item = atom ."#
            for msg in ["a[]", "a[b]", "a[b, c]", "a[b][c, d]"] {
                let r = try parsePostOracle(grammar: g, message: msg)
                #expect(r.postMatch, "@prefer under left-recursive OPT dropped a valid parse for '\(msg)'")
            }
        }
    }

    // MARK: - Nested cluster pragmas (new capability)

    @Suite("Nested cluster pragmas", .serialized)
    struct NestedCluster {

        // ---- Tier A: @prefer inside a ( a | b ) selection group ----------------
        //
        // Minimal analogue of the factored `keyPathExpression` that motivated this
        // work: a single token `x` is ambiguous between a "root" reading and a
        // "component" reading, so `[x]` parses two ways that cover the exact same
        // span. `@prefer` on the first alternate of the group keeps only the root
        // reading. The Oracle's registration walk now scans bracket alternate chains
        // (`registerPrefer` per bracket node), so the same `PreferRule` fires here.

        @Test("@prefer in ( a | b ) selection group — acceptance preserved, ambiguity removed")
        func preferInSelectionGroup() throws {
            let g = #"x - /x/ . S = "[" ( @prefer root comps? | comps ) "]" . root = x . comps = x ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "[x]")
            #expect(r.postMatch, "@prefer in a selection group must not drop the valid parse")
            #expect(r.isUnambiguous, "@prefer in the group should collapse the root/component ambiguity")
        }

        // The multi-element reading under a nested prefer must still survive — the
        // group analogue of `preferUnderOptFlat`. `list` here is inlined into a
        // ( a | b ) group instead of a nonterminal top level.
        @Test("@prefer in ( a | b ) keeps single and multi element readings")
        func preferInGroupKeepsReadings() throws {
            let g = #"item - /[a-z]/ . S = "[" ( @prefer item | item "," S2 )? "]" . S2 = item | item "," S2 ."#
            for msg in ["[]", "[a]", "[a, b]", "[a, b, c]"] {
                let r = try parsePostOracle(grammar: g, message: msg)
                #expect(r.postMatch, "@prefer in a group dropped a valid parse for '\(msg)'")
            }
        }

        // ---- Tier B: extent / associativity pragmas ON a cluster node ----------
        //
        // Node-level pragmas attach BEFORE the group (mirroring `@longest X = …`
        // before a LHS): `@left ( … )`, `@longest < … >`, `@longest { … }`.
        // `factor()` parses the prefix onto the bracket node's `.disambiguation`; the
        // Oracle's `registerNodeDisambiguation` reads it off the owner (nonterminal or
        // bracket) uniformly.

        // `@left` moved one level down: E's body is a single ( … ) cluster holding
        // both alternates, and `@left` annotates the group. Mirrors the top-level
        // `leftAssocPrunes` on "1 + 2 + 3".
        @Test("@left on a ( … ) cluster prunes to left-associative")
        func leftOnCluster() throws {
            let g = #"n - /[0-9]+/ . S = E . E = ( @left E "+" E | n ) ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "1 + 2 + 3")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@left on the cluster should leave a single left-assoc tree")
        }

        // Used to assert only `pruned > 0`: the old node-level `RightAssocRule` (keep-min-pivot)
        // under-pruned on 3+ operands and left a residual ambiguity. `@right` is now the
        // alternate-level child-position filter ("this production may not be its own leftmost
        // child"), which removes every left-nested reading, so it must leave ONE tree, exactly like
        // `leftOnCluster`.
        @Test("@right on a ( … ) cluster leaves one right-associative tree")
        func rightOnCluster() throws {
            let g = #"n - /[0-9]+/ . S = E . E = ( @right E "+" E | n ) ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "1 + 2 + 3")
            #expect(r.postMatch)
            #expect(r.pruned > 0, "@right on the cluster should prune the non-right-assoc pivot(s)")
            #expect(r.isUnambiguous, "@right on the cluster should leave a single right-assoc tree")
        }

        // `@longest` on a POS closure `< … >`. Faithful nested analogue of the
        // top-level `longestExtent` (which annotates the nonterminal wrapping the
        // POS); here the annotation moves onto the closure itself.
        @Test("@longest on a < … > POS closure")
        func longestOnPOSClosure() throws {
            let g = #"word - /[a-z]+/ . S = @longest < word > ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "hello world foo")
            #expect(r.postMatch)
        }

        // `@longest` on a KLN closure `{ … }`. Distinct from the POS case because
        // KLN/POS re-entry reuses a SINGLE shared CRF cluster ("cluster index is a
        // node ref, not a position") — the yield-identity hazard called out in the
        // plan. This test is the tripwire for verifying repetition yields don't
        // conflate distinct occurrences before we prune them.
        @Test("@longest on a { … } KLN closure (yield-identity hazard probe)")
        func longestOnKLNClosure() throws {
            let g = #"word - /[a-z]+/ . S = @longest { word } ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "hello world foo")
            #expect(r.postMatch)
        }
    }

    // MARK: - Epsilon watertightness & the @avoid model

    // Stress `@prefer`/`@avoid` against empty derivations. Grounded in Scott/Johnstone/van Binsbergen,
    // "Derivation representation using binary subtree sets" (SCICO 2019): an empty
    // derivation is a real degenerate BSR element `(X ::= ε, j, j, j)` (§3.1 rule 1),
    // and the paper explicitly PUNTS on the nullable `X ::= BBβ` case, which yields a
    // multigraph because `(BB,i,i)` has two children `(B,i,i)` (§1.1 p4, §3.2 p8:
    // "we have not added the treatment of the special case … easy to add if required").
    // That punt is exactly our KLN/POS shared-cluster yield-identity hazard. `apus`
    // spells ε as `""` (empty) or `ε`.
    @Suite("Epsilon & @avoid model", .serialized)
    struct EpsilonAndAvoidModel {

        // A group alternate that is ONLY a lookaround consumes nothing. The reachability walk used
        // to skip every zero-width bracket span, so the gate's yield was swept and the parse died —
        // which, in `typeIdentifier`, made every Swift type underaccept (2026-10-04).
        @Test("zero-width lookaround-only group alternate survives the Oracle")
        func lookaroundOnlyAlternate() throws {
            let g = #"S = "a" ( "b" | >-> ( "c" ) ) T . T = "d" | "c" "e" ."#
            let (plain, _) = try parseAndDisambiguate(grammar: g, message: "a d")
            #expect(plain, "the gate passes before `d`, so 'a d' must parse")
            let (taken, _) = try parseAndDisambiguate(grammar: g, message: "a b d")
            #expect(taken, "the consuming alternate must still parse 'a b d'")
            let (blocked, _) = try parseAndDisambiguate(grammar: g, message: "a c e")
            #expect(!blocked, "the gate rejects a following `c`, so 'a c e' must not parse")
        }

        // A `< … >` has no skip, so over a zero-width span it is one empty round. The reachability
        // walk treated it like a `{ … }`, as the skip, marked nothing, and the sweep removed the
        // only parse of "" (found by the Bend check, 2026-10-26).
        @Test("zero-width < … > keeps its one empty round")
        func zeroWidthPositiveClosure() throws {
            for (g, msg) in [(#"S = < "x" | "" >."#, ""), (#"S = "a" < "x" | "" > "b"."#, "a b"),
                             (#"S = < A >. A = "x" | ""."#, "")] {
                let r = try parsePostOracle(grammar: g, message: msg)
                #expect(r.rawMatch, "'\(msg)' must parse with \(g)")
                #expect(r.postMatch, "the Oracle removed the only parse of '\(msg)' with \(g)")
            }
        }

        // The reachability walk tiled alternates with their EPS symbols filtered out, so an `""`
        // next to other symbols was never marked and the sweep removed the only parse (found by
        // the Bend check, 2026-10-26).
        @Test("EPS inside a longer body keeps its parse")
        func epsilonInsideSequence() throws {
            for (g, msg) in [(#"S = "a" ""."#, "a"), (#"S = "" "" "x"."#, "x"), (#"S = "a" "" "b"."#, "a b")] {
                let r = try parsePostOracle(grammar: g, message: msg)
                #expect(r.rawMatch, "'\(msg)' must parse with \(g)")
                #expect(r.postMatch, "the Oracle removed the only parse of '\(msg)' with \(g)")
            }
        }

        // A) Same-span `@prefer` where the PREFERRED alternate ends in a nonterminal
        // that derived ε. Its last-symbol BSR yield is the degenerate (i,i) element,
        // so PreferRule can still key on it: alt1 (`"a" B`, B→"") and alt2 (`"a"`)
        // both span (0,1) → @prefer collapses them.
        @Test("@prefer keys through an explicit-ε tail")
        func preferThroughEpsilonTail() throws {
            let g = #"S = ( @prefer "a" B | "a" ) . B = "b" | "" ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch, "must still parse 'a'")
            #expect(r.isUnambiguous, "@prefer should collapse the ε-tail tie")
        }

        // B) Same, but the tail is a skipped OPT (nullable-over-span, not explicit ε).
        @Test("@prefer keys through a skipped OPT tail")
        func preferThroughSkippedOptTail() throws {
            let g = #"b - /b/ . S = ( @prefer "a" b? | "a" ) ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@prefer should collapse the skipped-OPT tie")
        }

        // C) Multi-alt same-span: mark 3 of 4 alternates `@prefer`; the 4th (D) is
        // pruned wherever any preferred sibling covers its span. PreferRule does NOT
        // rank winners, so A/B/C stay mutually ambiguous → pruned>0 but NOT unambiguous.
        @Test("three @prefer siblings prune the fourth (winners unranked)")
        func threePreferPruneFourth() throws {
            let g = #"t - /t/ . S = @prefer A | @prefer B | @prefer C | D . A = t . B = t . C = t . D = t ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "t")
            #expect(r.postMatch)
            #expect(r.pruned > 0, "D should be pruned by the preferred siblings")
            #expect(!r.isUnambiguous, "A/B/C remain mutually ambiguous (prefer doesn't rank winners)")
        }

        // D) The equivalence you posed: marking the 4th `@avoid` equals marking the
        // other three `@prefer` (C). `@avoid` is now an alt-prefix on any alt chain
        // (parsed in `sequence()`, compiled as "prefer the siblings" in
        // `registerPrefer`), so this behaves exactly like C.
        @Test("one @avoid sibling ≡ three @prefer")
        func oneAvoidEqualsThreePrefer() throws {
            let g = #"t - /t/ . S = A | B | C | @avoid D . A = t . B = t . C = t . D = t ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "t")
            #expect(r.postMatch)
            #expect(r.pruned > 0, "the avoided D should be pruned by its siblings")
            #expect(!r.isUnambiguous, "A/B/C remain mutually ambiguous — same as three @prefer")
        }

        // Ranks: @prefer above unmarked above @avoid (Bend/SPEC.bend, `outranks`). Two avoided
        // siblings have the same rank, so both stay. Each once lost to the other, and which one
        // survived depended on the order the rules ran.
        @Test("two @avoid siblings have the same rank — both stay")
        func twoAvoidedSiblingsStay() throws {
            for g in [#"t - /t/ . S = @avoid A | @avoid B . A = t . B = t ."#,
                      #"t - /t/ . S = @avoid B | @avoid A . A = t . B = t ."#] {
                let r = try parseOracleAmbiguity(grammar: g, message: "t")
                #expect(r.postMatch, "must parse 't' with \(g)")
                #expect(!r.isUnambiguous, "A and B are both avoided, so neither outranks the other: \(g)")
            }
        }

        // An unmarked sibling still beats both avoided ones.
        @Test("an unmarked sibling beats two @avoid siblings")
        func unmarkedBeatsTwoAvoided() throws {
            let g = #"t - /t/ . S = @avoid A | @avoid B | C . A = t . B = t . C = t ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "t")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "only C is left")
        }

        // Three ranks in one chain: A beats B and C, B beats C.
        @Test("@prefer, unmarked and @avoid in one chain")
        func threeRanks() throws {
            for (g, msg) in [(#"t - /t/ . S = @prefer A | B | @avoid C . A = t . B = t . C = t ."#, "t"),
                             (#"t - /t/ . u - /u/ . S = @prefer A | B | @avoid C . A = u . B = t . C = t ."#, "t")] {
                let r = try parseOracleAmbiguity(grammar: g, message: msg)
                #expect(r.postMatch, "must parse '\(msg)' with \(g)")
                #expect(r.isUnambiguous, "one alternative of the highest rank that matches is left: \(g)")
            }
        }

        // `@prefer` among a loop's alternatives compares ROUNDS. Each B round reads one `a`; A
        // cannot, so no round has a rival and both readings stay. Before loops were built as
        // `{ ( τ ) }` (`ApusParser.loopRound`), a round's own start was not in the BSR and the
        // rule compared loop prefixes: the second B round "lost" to the A round ending at the same
        // place, and `[B, B]` was removed.
        @Test("@prefer among loop alternatives compares rounds, not loop prefixes")
        func preferInLoopComparesRounds() throws {
            for g in [#"a - /a/ . S = { @prefer A | B } . A = a a . B = a ."#,
                      #"a - /a/ . S = < @prefer A | B > . A = a a . B = a ."#,
                      #"a - /a/ . S = { @prefer A | B } "x" . A = a a . B = a ."#] {
                let msg = g.contains("\"x\"") ? "a a x" : "a a"
                let r = try parseOracleAmbiguity(grammar: g, message: msg)
                #expect(r.postMatch, "must parse '\(msg)' with \(g)")
                #expect(!r.isUnambiguous, "[A] and [B, B] both stay: no round has a rival, with \(g)")
            }
        }

        // Same-span rounds still compete: on `a`, the preferred A round beats the B round.
        @Test("@prefer among loop alternatives still ranks a round against a same-span rival")
        func preferInLoopRanksSameSpanRounds() throws {
            let g = #"a - /a/ . S = { @prefer A | B } . A = a . B = a ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a a")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "every round is A: each B round has the same-span rival A")
        }

        @Test("@prefer and @avoid on one alternative is a grammar error")
        func preferAndAvoidConflict() throws {
            for g in [#"t - /t/ . S = @prefer @avoid A | B . A = t . B = t ."#,
                      #"t - /t/ . S = @avoid @prefer A | B . A = t . B = t ."#] {
                #expect(throws: (any Error).self, "\(g) must be rejected") { _ = try parseGrammar(g) }
            }
        }

        // E) Scott's punt: `A A` with A nullable. On "a" there are two distinct trees
        // (the 'a' under the first vs. second A). The engine must REPRESENT that as a
        // genuine ambiguity (not conflate the two (i,i) ε-elements into one tree).
        //
        // GREEN since Sep 3 2026 (TODO.md 23). It regressed to
        // `(postMatch: false, isUnambiguous: true)` — the Oracle pruned away the ONLY
        // derivation — because the dead-wood passes were blind to ε in two separate ways.
        // Keep this test: it is the canonical guard that the punt stays closed.
        @Test("nullable A A represents the ambiguity, no ε-conflation")
        func nullableRepetitionAmbiguity() throws {
            let g = #"S = A A . A = "a" | "" ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch, "must parse 'a'")
            #expect(!r.isUnambiguous, "two distinct trees (a·ε vs ε·a) — must not conflate to one")
        }

        // F) `@shortest [ X ]` is the canonical "skip the optional when possible" —
        // node-level extent that keeps the empty (i,i) reading. Both directions:
        //   - skip is viable → @shortest keeps it, prunes the take reading;
        //   - skip is NOT viable → phase-1 already removed the (i,i) yield, so take survives.
        @Test("@shortest [X] skips the optional when skipping still parses")
        func shortestOptionalSkipWins() throws {
            let g = #"mod - /m/ . id - /[a-z]/ . S = @shortest [ mod ] id id? ."#
            let r = try parsePostOracle(grammar: g, message: "m x")
            #expect(r.postMatch, "must still parse 'm x'")
            #expect(r.pruned > 0, "@shortest on the OPT should prune the take reading (skip is shorter)")
        }

        @Test("@shortest [X] keeps the taken reading when skipping cannot parse")
        func shortestOptionalForcedTake() throws {
            let g = #"op - /-/ . id - /[a-z]+/ . S = @shortest [ op ] id ."#
            let r = try parsePostOracle(grammar: g, message: "-x")
            #expect(r.postMatch, "phase-1 removes the skip; @shortest must keep the forced take")
        }

        // S1/S2 — extent on an OPT whose start is fixed (S1) or moved by a variable-length
        // prefix (S2). S1 resolves: extent compares interval length (not just the end), and the
        // OPT reads its own prunable yields so the kill propagates along the sequence.
        // S2 also resolves: the Oracle compares the annotated bracket's extent across complete
        // body tilings, so a variable-length prefix moving the bracket start no longer hides the
        // empty reading.
        @Test("@shortest [X] [X] — first is kept empty (fixed-start extent)")
        func shortestTwoOptionalsFirst() throws {
            let r = try parseOracleAmbiguity(grammar: #"x - /x/ . S = @shortest [ x ] [ x ] ."#, message: "x")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@shortest on the first OPT should force it empty → unambiguous")
        }

        @Test("[X] @shortest [X] — second is kept empty (moved-start extent)")
        func shortestTwoOptionalsSecond() throws {
            let r = try parseOracleAmbiguity(grammar: #"x - /x/ . S = [ x ] @shortest [ x ] ."#, message: "x")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@shortest on the second OPT (start moved by [x]) should still resolve")
        }

        // Closures now honor extent (the shared cluster's accumulated pops give the
        // transitive end set on the closure node, which endPositions reads and the extent
        // rule prunes). S3 = baseline massive ambiguity; S5 @longest greedily forces the
        // first closure to consume all → unambiguous; S4 @shortest only forces the first
        // closure empty, so { x }{ x } over "xxx" stays (legitimately) ambiguous.
        @Test("{X}{X}{X} is massively ambiguous (baseline)")
        func closuresBaselineAmbiguous() throws {
            let r = try parseOracleAmbiguity(grammar: #"x - /x/ . S = { x } { x } { x } ."#, message: "xxx")
            #expect(r.postMatch)
            #expect(!r.isUnambiguous)
        }

        @Test("@longest {X}{X}{X} → greedy first closure, unambiguous")
        func longestClosuresUnambiguous() throws {
            let r = try parseOracleAmbiguity(grammar: #"x - /x/ . S = @longest { x } { x } { x } ."#, message: "xxx")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@longest forces the first closure to consume all → single parse")
        }

        @Test("@shortest {X}{X}{X} → first closure empty, still ambiguous (fewer parses)")
        func shortestClosuresReduced() throws {
            let r = try parseOracleAmbiguity(grammar: #"x - /x/ . S = @shortest { x } { x } { x } ."#, message: "xxx")
            #expect(r.postMatch)
            #expect(r.pruned > 0, "@shortest prunes the non-empty first-closure readings")
            #expect(!r.isUnambiguous, "only the first closure is constrained; { x }{ x } over xxx stays ambiguous")
        }

    }

    // MARK: - @avoid inside brackets
    //
    // `@avoid`/`@prefer` annotate the ALT node, also inside a bracket: `[ @avoid A | B ]` marks
    // A, not the bracket. `@avoid` only loses to SIBLINGS over the same span. The skip of a
    // `[ … ]` or `{ … }` is not a sibling: preferring the skip is `@shortest`'s job. (A
    // separate follower-pivot rule once ranked the skip too; it was removed on 2026-10-26.)
    @Suite("@avoid inside brackets", .serialized)
    struct AvoidInsideBrackets {

        // A lone `[ @avoid X ]` has no sibling to lose to, so it ranks nothing: skip and take
        // both stay. `@shortest [ X ]` is the way to prefer the skip.
        @Test("[ @avoid X ] alone ranks nothing — skip and take both stay")
        func avoidAloneRanksNothing() throws {
            let g = #"mod - /m/ . id - /[a-z]/ . S = [ @avoid mod ] id id? ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "m x")
            #expect(r.postMatch, "must still parse 'm x'")
            #expect(!r.isUnambiguous, "the skip is not a sibling: '[ mod ] id' and 'id id' both stay")
        }

        // The FIX for the silent-theft trap: `[ @avoid A | B ]` now marks the FIRST
        // alternate A (not the bracket). On "a c" both A and B tile the same span, so the
        // same-span PreferRule prunes A and keeps B → unambiguous. (Under the old parse,
        // the leading @avoid was stolen onto the bracket and A stayed un-annotated.)
        @Test("[ @avoid A | B ] marks A — same-span sibling prune keeps B")
        func avoidFirstAlternateInBracket() throws {
            let g = #"a - /a/ . c - /c/ . S = [ @avoid A | B ] c . A = a . B = a ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a c")
            #expect(r.postMatch, "must parse 'a c'")
            #expect(r.pruned > 0, "@avoid A is pruned by its sibling B (same span)")
            #expect(r.isUnambiguous, "only B survives → single tree")
        }

        // Mixed group, sibling B shadows A same-span (A=B=a on "a"). "A loses to B" fires
        // (same-span PreferRule) → A pruned. But @avoid A does NOT rank B against the skip,
        // so B-take vs skip stays (legitimately) ambiguous: the skip is not a sibling.
        @Test("mixed [ @avoid A | B ], sibling shadows A — A pruned, B-vs-skip stays ambiguous")
        func mixedAvoidSiblingShadows() throws {
            let g = #"a - /a/ . S = [ @avoid A | B ] a? . A = a . B = a ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch, "must parse 'a'")
            #expect(r.pruned > 0, "the avoided A is pruned by its same-span sibling B")
            #expect(!r.isUnambiguous, "B-take vs skip is unranked by @avoid A → residual ambiguity (correct)")
        }
    }

    // A preference on a cycle that reads no input can remove every parse: in
    // `A = @prefer A | "a"` every tree ends in `"a"`, which `A → A` outranks over the same
    // tokens. `diagnosePreferenceCycles` finds such alternatives, and grammar loading refuses
    // the grammar.
    @Suite("Preference cycles", .serialized)
    struct PreferenceCycles {

        @Test("a grammar with a preferred alternative on an input-free cycle is refused")
        func reported() throws {
            for g in [#"S = A . A = @prefer A | "a" ."#,
                      #"S = A . A = A | @avoid "a" ."#,
                      #"S = A . A = @prefer B | "a" . B = A ."#,
                      #"S = A . A = @prefer N A | "a" . N = "n" | "" ."#,
                      #"S = A . A = ( @prefer A | "a" ) ."#] {
                do {
                    _ = try parseGrammar(g)
                    Issue.record("\(g) must be refused")
                } catch ApusParserError.preferenceCycle(let findings) {
                    #expect(!findings.isEmpty, "\(g): the error names the alternative")
                } catch {
                    Issue.record("\(g) must be refused for its preference cycle, not: \(error)")
                }
            }
        }

        @Test("a cycle through an alternative that outranks nothing is not reported")
        func notReported() throws {
            for g in [#"S = A . A = @prefer "a" | A ."#,
                      #"S = A . A = A | "a" ."#,
                      #"S = A . A = @prefer "x" A | "a" ."#,
                      #"S = A . A = @prefer B | C . B = "b" . C = "b" ."#] {
                let findings = try parseGrammar(g).diagnosePreferenceCycles()
                #expect(findings.isEmpty, "\(g) must not be reported: \(findings)")
            }
        }

        @Test("Swift.apus has no preference on an input-free cycle")
        func swiftGrammarClean() throws {
            let findings = try loadGrammarFile(named: "Swift.apus").diagnosePreferenceCycles()
            #expect(findings.isEmpty, "\(findings)")
        }
    }

    @Suite("Parse predicates", .serialized)
    struct ParsePredicates {

        // MARK: Predicate targets
        //
        // `LookaheadPredicateRule` answers "does N derive here?" from N's yields where the parse
        // called N at the anchor, and from a speculative recogniser where it did not, so a target
        // need not be predicted there. `diagnosePredicateTargets` reports only undefined targets.

        @Test("an undefined predicate target is reported")
        func undefinedTargetIsReported() throws {
            let g = #"a - /a/ . S = @cannotParse(Missing) "a" ."#
            let findings = try parseGrammar(g).diagnosePredicateTargets()
            #expect(findings.contains { $0.contains("'Missing'") }, "expected a finding for 'Missing', got: \(findings)")
        }

        @Test("a defined predicate target is not reported")
        func definedTargetIsClean() throws {
            let g = #"a - /a/ . S = @cannotParse(A) "a" . A = "a" ."#
            let findings = try parseGrammar(g).diagnosePredicateTargets()
            #expect(findings.isEmpty, "expected no findings, got: \(findings)")
        }

        @Test("the Swift grammar's predicate targets are all defined")
        func swiftGrammarHasNoBlindPredicates() throws {
            let findings = try loadGrammarFile(named: "Swift.apus").diagnosePredicateTargets()
            #expect(findings.isEmpty, "Swift.apus has undefined predicate targets: \(findings)")
        }

        @Test("a predicate target the parse never calls is answered by a recogniser")
        func uncalledPredicateTargetIsRecognised() throws {
            // `X` appears in no production body, so the parse never calls it; the predicate must
            // still see that `X` derives at the start of "a b".
            let g = #"S = @cannotParse(X) "a" B | "a" "c" . B = "b" . X = "a" "b" ."#
            let accepted = try parseOracleAmbiguity(grammar: g, message: "a c")
            #expect(accepted.postMatch)
            let rejected = try parseOracleAmbiguity(grammar: g, message: "a b")
            #expect(rejected.rawMatch)
            #expect(!rejected.postMatch)
        }

        @Test("@canParse is the positive Oracle predicate spelling")
        func canParseKeepsAlternate() throws {
            let g = #"a - /a/ . S = @canParse(A) B | "b" . B = A . A = "a" ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch)
            #expect(r.isUnambiguous)
        }

        @Test("leading symbolic lookaround is not an Oracle predicate")
        func symbolicLookaheadIsNotAlternatePredicate() throws {
            let g = #"a - /a/ . S = >->(A) "a" | A . A = "a" ."#
            #expect(throws: (any Error).self) {
                let parser = try ApusParser(fromString: "whitespace : /\\s+/.\n" + g)
                _ = try parser.parse(explicitStartSymbol: "")
            }
        }

        @Test("alternate annotations are order-independent")
        func alternateAnnotationsAreOrderIndependent() throws {
            let g = #"a - /a/ . S = @cannotParse(B) @prefer A | B . A = "a" . B = "b" ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch)
            #expect(r.isUnambiguous)
        }
    }
}
