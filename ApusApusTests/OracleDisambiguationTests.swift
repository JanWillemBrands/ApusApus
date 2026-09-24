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
//     nonterminal. See `Oracle Disambiguation Unification.md`.
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
                grammar: #"number - /[0-9]+/ . @left E = E "+" E | number ."#,
                message: "1 + 2 + 3"
            )
            #expect(matches, "1 + 2 + 3 should parse")
            #expect(pruned > 0, "Oracle should prune right-associative derivation")
        }

        @Test("@right prunes ambiguous expression")
        func rightAssocPrunes() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . @right E = E "+" E | number ."#,
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
                grammar: #"number - /[0-9]+/ . @left E = E "+" E | number ."#,
                message: "1 + 2"
            )
            #expect(matches, "1 + 2 should parse")
            #expect(pruned == 0, "Unambiguous input should not need pruning")
        }

        @Test("@left with four operands")
        func leftAssocFourOperands() throws {
            let (matches, pruned) = try parseAndDisambiguate(
                grammar: #"number - /[0-9]+/ . @left E = E "+" E | number ."#,
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

        // Bracket-level `[ @avoid X ]` — the optional-skip: prefer NOT taking the optional
        // when skipping still parses. Compiled to a follower-pivot rule (keep-min pivot on
        // the symbol after the bracket). Here `m` is BOTH modifier `mod` and an `id`, so
        // `m x` parses two ways; @avoid keeps the SKIP reading.
        @Test("@avoid skips the optional when skipping still parses")
        func avoidSkipsOptional() throws {
            let g = #"mod - /m/ . id - /[a-z]/ . S = [ @avoid mod ] id id? ."#
            let r = try parsePostOracle(grammar: g, message: "m x")
            #expect(r.postMatch, "@avoid grammar should still parse 'm x'")
            #expect(r.pruned > 0, "@avoid should prune the take-modifier reading")
        }

        // When skipping does NOT lead to a complete parse, the lone "taken" reading must
        // survive: phase-1 removes the skip pivot before @avoid runs. Here `id` can't start
        // at the leading `-`, so the `op` prefix is forced.
        @Test("@avoid keeps the taken reading when skipping cannot parse")
        func avoidKeepsTakenWhenSkipFails() throws {
            let g = #"op - /-/ . id - /[a-z]+/ . S = [ @avoid op ] id ."#
            let r = try parsePostOracle(grammar: g, message: "-x")
            #expect(r.postMatch, "@avoid must keep the forced 'op' reading for '-x'")
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
            let g = #"n - /[0-9]+/ . S = E . E = @left ( E "+" E | n ) ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "1 + 2 + 3")
            #expect(r.postMatch)
            #expect(r.isUnambiguous, "@left on the cluster should leave a single left-assoc tree")
        }

        // NOTE the asymmetry with `leftOnCluster`: we assert `pruned > 0`, not
        // `isUnambiguous`. `@right` (RightAssocRule, keep-min-pivot) under-prunes on
        // 3+ operands and leaves a residual ambiguity — verified to be PRE-EXISTING
        // and level-independent: the top-level `@right E = E "+" E | n` on "1 + 2 + 3"
        // gives the same `isUnambiguous: false` (probe, 2026-08-09). This test asserts
        // the cluster path reaches parity with the top-level path (the rule fires),
        // not that it fixes that separate Oracle limitation. Mirrors the top-level
        // `rightAssocPrunes` assertion (matches && pruned > 0).
        @Test("@right on a ( … ) cluster prunes right-associative (parity with top level)")
        func rightOnCluster() throws {
            let g = #"n - /[0-9]+/ . S = E . E = @right ( E "+" E | n ) ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "1 + 2 + 3")
            #expect(r.postMatch)
            #expect(r.pruned > 0, "@right on the cluster should prune the non-right-assoc pivot(s)")
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

    // Stress `@prefer`/`@avoid` against empty derivations, and probe the
    // `@avoid ≡ @shortest [X]` conjecture. Grounded in Scott/Johnstone/van Binsbergen,
    // "Derivation representation using binary subtree sets" (SCICO 2019): an empty
    // derivation is a real degenerate BSR element `(X ::= ε, j, j, j)` (§3.1 rule 1),
    // and the paper explicitly PUNTS on the nullable `X ::= BBβ` case, which yields a
    // multigraph because `(BB,i,i)` has two children `(B,i,i)` (§1.1 p4, §3.2 p8:
    // "we have not added the treatment of the special case … easy to add if required").
    // That punt is exactly our KLN/POS shared-cluster yield-identity hazard. `apus`
    // spells ε as `""` (empty) or `ε`.
    @Suite("Epsilon & @avoid model", .serialized)
    struct EpsilonAndAvoidModel {

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
        // node-level extent that keeps the empty (i,i) reading. This replaces the retired
        // `[ @avoid X ]` hybrid. Both directions:
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

    // MARK: - Optional-skip unification (@avoid always on the ALT node)
    //
    // `@avoid`/`@prefer` ALWAYS annotate the ALT node now — there is no separate
    // bracket-level `@avoid`. `[ @avoid X ]` marks the body alternate `X`; its rival is
    // the OPT's implicit empty (skip) branch, keyed by the follower-pivot rule
    // (`registerOptionalSkip`). This removes the old silent-theft trap where the first
    // `@avoid` after `[` was stolen from the first alternate onto the bracket.
    @Suite("Optional-skip unification", .serialized)
    struct OptionalSkipUnification {

        // Canonical single-body skip still works after the ALT-node re-routing — the
        // annotation now sits on the alternate, but the follower-pivot behaviour is identical.
        @Test("[ @avoid X ] still prefers the skip (regression under the ALT-node model)")
        func avoidSingleBodySkip() throws {
            let g = #"mod - /m/ . id - /[a-z]/ . S = [ @avoid mod ] id id? ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "m x")
            #expect(r.postMatch, "must still parse 'm x'")
            #expect(r.pruned > 0, "the take-modifier reading is pruned; skip wins")
        }

        // KLN analogue: `{ @avoid X }` (zero-or-more, prefer zero). Same follower-pivot.
        @Test("{ @avoid X } prefers zero iterations")
        func avoidKlnSkip() throws {
            let g = #"a - /a/ . S = { @avoid a } a? a ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a a")
            #expect(r.postMatch, "must still parse 'a a'")
            #expect(r.pruned > 0, "the closure prefers zero iterations (skip)")
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
        // so B-take vs skip stays (legitimately) ambiguous. This is CORRECT, not a gap.
        @Test("mixed [ @avoid A | B ], sibling shadows A — A pruned, B-vs-skip stays ambiguous")
        func mixedAvoidSiblingShadows() throws {
            let g = #"a - /a/ . S = [ @avoid A | B ] a? . A = a . B = a ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch, "must parse 'a'")
            #expect(r.pruned > 0, "the avoided A is pruned by its same-span sibling B")
            #expect(!r.isUnambiguous, "B-take vs skip is unranked by @avoid A → residual ambiguity (correct)")
        }

        // Mixed bracket whose non-avoided sibling `other` does NOT match, so only the avoided
        // `mod`-take and the skip compete. `@avoid mod` prefers the skip. Nonterminal follower
        // `id`, so the follower-pivot prune propagates; the alternate-aware exemption leaves the
        // (viable) sibling untouched.
        @Test("mixed [ @avoid mod | other ], sibling not viable — mod-take loses to skip")
        func mixedAvoidSkipResolves() throws {
            let g = #"mod - /m/ . other - /o/ . id - /[a-z]/ . S = [ @avoid mod | other ] id id? ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "m x")
            #expect(r.postMatch, "must still parse 'm x'")
            #expect(r.pruned > 0, "the mod-take reading is pruned in favour of the skip (sibling 'other' doesn't match)")
        }
    }

    @Suite("Parse predicates", .serialized)
    struct ParsePredicates {

        // MARK: Blind-target diagnostic (TODO.md / Make trivia handling principled)
        //
        // `LookaheadPredicateRule` answers "does N derive here?" from N's yields, and an empty
        // answer is ambiguous: N failed (a real false) or N was never attempted (blind). Blind
        // resolves to the PERMISSIVE verdict, so `@cannotParse(N)` silently becomes `true` and the
        // guarded alternate is unguarded. `diagnosePredicateTargets` raises the unconditionally
        // blind cases as the "specification error" the design doc already calls them.

        @Test("a predicate target referenced by no production body is reported as blind")
        func blindTargetNotReferenced() throws {
            // `A` is defined and named by the predicate, but no production body mentions it, so it
            // is never predicted and `@cannotParse(A)` can never fire.
            let g = #"a - /a/ . S = @cannotParse(A) "a" . A = "a" ."#
            let findings = try parseGrammar(g).diagnosePredicateTargets()
            #expect(findings.contains { $0.contains("BLIND PREDICATE") && $0.contains("'A'") },
                    "expected a blind-predicate finding for 'A', got: \(findings)")
        }

        @Test("a predicate target reachable from a production body is not reported")
        func reachableTargetIsClean() throws {
            // Same predicate, but `A` now appears in a body, so it is predicted and the query is
            // authoritative. This is the guard against the diagnostic crying wolf.
            let g = #"a - /a/ . S = @cannotParse(A) "a" | A . A = "a" ."#
            let findings = try parseGrammar(g).diagnosePredicateTargets()
            #expect(findings.isEmpty, "expected no findings, got: \(findings)")
        }

        @Test("the Swift grammar has no blind predicate targets")
        func swiftGrammarHasNoBlindPredicates() throws {
            // Regression lock for the `@cannotParse(accessorBlockBrace)` class of bug: that guard was
            // dead because the target was never predicted at a variable brace. This asserts the
            // statically-detectable half stays clean as predicates are added.
            let findings = try loadGrammarFile(named: "Swift.apus").diagnosePredicateTargets()
            #expect(findings.isEmpty, "Swift.apus has blind predicate targets: \(findings)")
        }

        @Test("@cannotParse is the Oracle predicate spelling")
        func cannotParsePrunesAlternate() throws {
            let g = #"a - /a/ . S = @cannotParse(A) "a" | A . A = "a" ."#
            let r = try parseOracleAmbiguity(grammar: g, message: "a")
            #expect(r.postMatch)
            #expect(r.pruned > 0)
            #expect(r.isUnambiguous)
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
