# The Oracle

The Oracle (`ApusApus/Oracle.swift`) runs after the parse. The parser keeps every derivation of
the input as BSR yields. The Oracle removes yields until only the readings that the grammar's
annotations select are left. It builds no trees; `DerivationBuilder` does that afterwards.

What the Oracle must compute is specified in the Bend twin: `Bend/GUARD.bend`, `Bend/PREFER.bend`
and `Bend/EXTENT.bend` define the phases on the BNF core, `Bend/LAWS.bend` states what the oracles
hand out, and `Bend/ORACLE.bend` and `Bend/EXTENT.bend` are the proven oracles. `BendCheck` compares
Swift's yields with the twin's sets on hand-written cases, and `BendDifferential` on random
grammars (TESTING.md).

For the annotations themselves, see `apus.md`; for how to choose one, see `Ambiguity.md`.

## 1. Input and result

- **Input:** the raw yields of the parse, per grammar node.
- **The readings:** the root the parse ran (`MessageParser.currentParseRoot`; a test may parse
  from a sub-grammar root) from the start of the input to an accepting end
  (`MessageParser.acceptingEnds`): the end of the input, or an end followed only by trivia. This is
  the one definition of "the parse accepts", shared with the parse count, `DerivationBuilder` and the
  tests.
- **Result:** exactly the yields on the selected readings, written back to `parser.yields`. When no
  reading exists at all, the result is empty. (A `>!>` that the parser already applied can remove the
  last reading; what is left then is dead ends and probe calls.)

## 2. The phases

The phases are those of the Bend twin, in its order. A later phase only sees what the earlier
ones kept.

| Phase | Annotations | Swift pass | What decides |
|---|---|---|---|
| 1. admissible | `>?>( N )`, `>!>( N, … )` | `filter` | the parser's probe of `N` at the alternate's start |
| | `@left( N, … )`, `@right( N, … )` | `filter` | what the named nonterminals derive where the edge child starts (probed) |
| | bare `@left`, `@right` | `filter` | what the alternate itself derives there (plain derives; probed for `@left`) |
| 2. unbeaten | `@prefer`, `@avoid` | `sameSpan` | a genuine sibling of higher rank over the same span |
| 3. selected | `@longest`, `@shortest` | `YieldGraph.extent` | the best length among genuine readings |

Each rule is a filter on one node's yields (`DisambiguationRule`). The rules are registered once
per Oracle, from the grammar. After each pass that removed something, support from below
(section 3) removes what no longer stands, so the next pass sees only genuine rivals. Between the
passes, dead wood above the removals may stay: every Bend law is "embeds exactly", so the phases
allow it. Reachability from the root runs once before phase 3, which ranks whole readings, and
once more if phase 3 removed anything.

## 3. The yield graph

`YieldGraph` is the BSR set with its links written down: the binarised SPPF that the set
encodes. It is built once per Oracle and has the size of the set.

- A **key** `(node, i, j)` is a symbol occurrence over a span: an intermediate or symbol node of
  the SPPF. For a left-hand nonterminal it is a completion over `[i, j]`.
- A **yield** `(i, k, j)` is a packed node. It belongs to the key `(node, i, j)` and needs:
  - its **prefix**: the previous body symbol's key `(pred, i, k)`; for a later loop round, the
    round before it, `(group, i, k)`;
  - its **content**: for a nonterminal reference the key `(X, k, j)`; for a bracket some
    alternative's last symbol `(last, k, j)`; for a loop its round group `(group, k, j)`; for a
    completion some alternative's last symbol; nothing for a token, a gate or ε.
- **Support from below** is the least fixpoint of "a yield stands when its prefix and one of its
  contents stand; a key stands when one of its yields does", computed with counters in one pass.
- **Reachability from the root** follows the keys that standing yields need, from every accepted
  reading. A yield that stands and is reached is on a complete reading, so the two passes leave
  exactly the yields of the parse trees.
- **No removable empty rounds** (`Bend/EBNF.bend`, the needs on rounds): a loop round that reads nothing
  stands only as the first, and then only, round of a `< >`; a `[ ]` over nothing is a skip, not an
  empty pick. The parser still predicts later empty `< >` rounds; without this rule such a round's
  key would support itself, an SPPF cycle of repeated nothing.

## 4. Parse predicates in the parser

`>?>( N )` and `>!>( N, … )` ask whether `N` derives a prefix of the rest of the input from the
alternate's start. The meaning is the spec's (`Ahead`/`NotAhead`): plain derives, so `N`'s own
predicates do not count, and it does not matter whether the parse needed `N` there.

- **Probe.** When the parse reaches the first slot of an alternate with predicates, it calls each
  target there (`slotProbes`, `MessageParser.probe`): a call without return edges. If the parse called `N` there
  anyway, the call is shared and the probe costs one lookup. `N` derives here exactly when its call
  at this position returned (`leave` records every pop).
- **No early drop.** The Oracle's filter decides; the parser does not stop a `>!>` alternate
  whose target has already returned (that would save a few descriptors but no measurable time).
- **Followed by anything.** A target derives a PREFIX, so its call may be followed by any token. A
  target and whatever can end one are `followedByAnything`, and `viable` predicts their nullable
  alternates whatever follows. FOLLOW itself is unchanged; the LL(1) diagnostics read it.
- **Flavors.** The probe calls the flavor instance that a reference at the alternate's start would
  get, and predicate targets count toward flavor relevance (`specializeFlavors`).
- **Placement.** Only at the start of an alternate, among the zero-width items there; in any order
  with `@prefer`/`@avoid`/`@left`/`@right`.

**The same for `@left`/`@right`.** They too ask about the language: does a listed
nonterminal, or (bare) the alternate itself, derive the edge child's tokens? So the parser probes
where the edge child starts, with the same `slotProbes`: the targets of
`@right( N, … )` on the first body symbol, those of `@left( N, … )` and, for a bare `@left`, the
alternate's own owner on the last body symbol. A bare `@right` needs no probe: the alternate itself
is being parsed from where its first child starts. Listed targets are `followedByAnything`, and
resolve to the flavor instance a reference would get, as predicate targets do.

## 5. Design choices

These meanings were chosen, not derived. `OracleDisambiguationTests`, suite "Decided semantics",
has a test for each. When one changes, update this section and `Bend/README.md` ("Design choices").

1. **Bare `@left`/`@right` means plain "derives"**, as the spec does (`Bend/GUARD.bend`). The
   alternate may not be its own edge child where its items derive the edge child's tokens; its
   own filters do not count. So `f(1) {}⏎{}` does not chain: the parenless trailing-closure
   alternate derives `f(1) {}` with a callee `f(1)`, although its own `@right(argumentCall)`
   forbids that callee. swift-syntax accepts the chain; its test fails visibly (TODO.md,
   "Grammar rework for the Oracle").
2. **`@longest`/`@shortest` are local, for brackets and nonterminals alike**, as the spec does
   (`Bend/EXTENT.bend`): a marked occurrence loses only to a longer (shorter) reading of the same
   enclosing sequence over the same tokens. A mark on a nonterminal marks every reference of it;
   several marks in one sequence are served left to right. So a grammar states which sequence
   decides: in Swift.apus, `codeBlockItems` is right-recursive with a `@longest codeBlockItem`,
   so that a statement reads as far as it can (a loop would put the split between rounds outside
   any one sequence, where a local mark cannot see it).
3. **Predicates mean the language** (section 4), as the spec does.
4. **Preference cycles are refused at load.** An alternate that outranks a sibling may not lie on a
   cycle that reads no input (`diagnosePreferenceCycles`; virtual tokens such as `>>|` read
   nothing). This is the spec's well-formedness rule (`Bend/PREFER.bend`, `noPreferenceCycle`),
   so the Oracle needs no rule for rivals that come back to their own choice.
5. **Residual ambiguity is not an Oracle invariant.** A grammar without annotations is ambiguous on
   purpose. `DerivationBuilder.diagnostics` reports every ambiguous choice of the result, and the
   suites assert on it.

## 6. Cost

Release, per file, on the four large sources of `DecisionStatisticsTests`:

| Stage | Time |
|---|---|
| Parse (GLL, lexing, probes) | 0.64–0.87 s |
| `Oracle.init` | about 1 ms |
| `Oracle.disambiguate` | 0.10–0.14 s |
| `DerivationBuilder.buildAST` | 0.16–0.20 s |

On small inputs (Release, the 1,599 enabled snippets of the accept corpus) the
Oracle costs more than the parse: per snippet, parse 2.64 ms, `Oracle.init` 1.00 ms (rule
registration, which depends only on the grammar), `disambiguate` 2.19 ms.

Inside `disambiguate`, building the graph takes about 40%, support and reachability about 45%, and
the rule passes almost nothing. Most of the rest is hashing; a shared forest index built during the
parse would save an estimated 8% of the total, which was judged not worth an engine change.
