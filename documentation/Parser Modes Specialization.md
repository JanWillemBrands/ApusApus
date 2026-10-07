# Parser Modes as Grammar Specialization

Design note for TODO #1 (parser-mode overhead). Status: implemented 2026-10-07 (specialization +
declared scopes with `@carries`); see Findings and Decision below.
Follows `Parser Modes Migration Plan.md`, which introduced the runtime mode bitset.

## The question

The runtime design widens `Descriptor` (24 → 32 bytes) and CRF `ParsePosition` with a
`UInt64 mode`. Every descriptor and CRF hash pays for the mode, but only a small part of
the Swift grammar uses modes (15 `@setMode`, 6 `@clearMode`, 6 `@requiresMode`,
9 `@rejectsMode`). The full suite went from about 110s to about 151s. Should we
(1) make that overhead smaller, or (2) use modes much more widely so the overhead pays
for itself?

Short answer: neither. A finite set of inherited mode bits is not runtime state. It is
part of which nonterminal you are in. Compile it into the grammar (each nonterminal gets
one copy per mode combination that actually matters) and the runtime cost is zero. Copies
are made only where modes matter. That removes the overhead (1) and fixes a correctness
gap. Point (2) then becomes a separate question: which existing mechanisms are really
"context" problems? That question has a clear answer (see below). It is not "use modes for
ambiguity in general".

## Observation 1: modes are finite inherited attributes, so they are a CFG

`@setMode`/`@clearMode` compute the child's mode from the parent's mode with a fixed
function per occurrence: `(m | add) & ~remove`. `@requiresMode`/`@rejectsMode` are fixed
tests on `m`. A CFG with finitely many inherited attribute values is the same as a plain
CFG with indexed nonterminals `X⟨m⟩`. This is the parameterized-nonterminal construction
(Happy-GLL, `articles/Happy-GLL- …pdf`; SDF/Rascal parameterized sorts). swift-syntax's
`ExprFlavor` is the same idea in handwritten form: a parameter passed down explicitly.

Carrying `m` in descriptors is the interpreted form of this construction. Specialization
is the compiled form.

## Observation 2: the runtime design is incomplete. BSR is mode-blind.

Mode is part of descriptor identity and CRF identity, but `addYield(L:i:k:j:)` stores
yields under `L.number` without the mode (`BinarySubtreeRepresentation.swift:28`).
Suppose the same `(X, i, j)` is derived under two modes, and a gated alternative is valid
in only one of them (`@requiresMode(ifConfigBody)` on `ifDirectiveClause`,
`@requiresMode(optionalBinding) "self"`, `@requiresMode(initializerBodyMode)` on
`statement`). Then the yields merge. The DerivationBuilder, the Oracle and the converter
can attach the gated reading under a parent from the other mode. The possible symptoms are
spurious residual ambiguity or a wrong tree. No concrete reproducer is known yet. The
hazard comes from the representation itself. Closing it at runtime means widening the BSR
as well, which adds more overhead. With specialization it cannot happen: each clone has
its own `number`.

## Observation 3: the overhead is probably not only hashing width

A mode splits CRF clusters even for nonterminals whose language does not depend on it. For
example, `identifier` at position `i` under `stmtCondition` and under `0` are two clusters
with two descriptor sets. Some bits also leak far beyond their intended scope:

- `trailingClosure` is set in `trailingClosures` and never cleared. So the whole body of
  every trailing closure runs in a different mode from the same text parsed another way.
  GLL often explores both readings of `{` after an expression (trailing closure vs. a
  separate statement), and the body is then parsed twice instead of shared.
- `ifConfigBody` is cleared only between statements. It still applies inside closures that
  are nested in the first statement of an `#if` body. (Check whether this ever changes
  acceptance.)

Hypothesis: a real part of the 110s → 151s increase is duplicated work, not the extra 8
bytes. **Step 0** below measures this before any redesign.

## Design: compile-time specialization with relevance projection

### Relevance

`rel(X)` is the set of mode bits that can change the language of nonterminal or bracket
`X`. It is the least fixpoint of:

```text
rel(X) = tests(X)                                   // require/reject bits on X's alternates and body nodes
       ∪ ⋃ over occurrences Y in X's bodies:  rel(Y) & ~(add_Y | remove_Y)
```

A bit that an occurrence sets or clears is fixed for that child. So that child never makes
the parent depend on the bit. Brackets (`DO/OPT/KLN/POS`) are handled like nonterminals.
Terminals and layout nodes contribute only their own tests.

### Expansion

Start a worklist at `root⟨0⟩`. Every sub-parse root (structured tokens, `@preempt`
sub-parses) also starts at `⟨0⟩`.

```text
X⟨m⟩ with m ⊆ rel(X):
  drop alternates whose require/reject tests fail statically under m
  for each occurrence Y (add A, remove R):
      link the occurrence to Y⟨((m | A) & ~R) & rel(Y)⟩      // enqueue if new
```

- If `rel(X) = ∅`, there is exactly one instance, and it is the original node graph. Any
  grammar without modes, and most of the Swift grammar, is left as it is. This is what
  TODO #1 asks for: no tax on grammars or regions that do not use modes.
- Only reachable instances are created.
- Each clone keeps `name` and gets an `origin: GrammarNode` link. Anything keyed on names
  (SwiftSyntax converter, `@builder`, messages, diagnostics) keeps working.
- The pass runs after `ApusParser` builds the graph and before `assignNameIDs`,
  `propagateExcludeSets`, `populateBitSets` and first/follow. Later passes and Oracle
  registration then see the clones as ordinary nodes. Their FIRST/FOLLOW sets are more
  precise (for example, `closureExpression⟨stmtCondition, trailingClosure⟩` has no
  newline-opened alternative). That improves `testSelect`/`continuationViable` pruning,
  so this is likely faster than before modes existed, not just as fast.

### What is copied

Yes: specialization makes real copies of `GrammarNode`s, once, at grammar load. A copy is
made per **(nonterminal, projected mode)** pair. Copying `X` for mode `m` deep-copies its
production subgraph: the LHS node, its ALT chain, each alternate's `.seq` chain (terminal
slots, layout nodes, lookarounds, inline brackets `DO/OPT/KLN/POS`, END nodes). Copied
terminals keep their `nameID`, so the scanner and lex cache stay shared. Each copy keeps
`name` and gets an `origin` link back to the original.

Inside the copy, two things change:

1. **Mode tests are decided statically.** An alternate whose `@requiresMode`/`@rejectsMode`
   fails under `m` is left out of the copy.
2. **Nonterminal occurrences are relinked.** An occurrence's `.alt` (pointing to the callee
   LHS) is redirected to `Y⟨((m | add) & ~remove) & rel(Y)⟩`. If that projects to `0`,
   it points at the original `Y`.

The `& rel(Y)` projection makes call sites whose modes differ only in irrelevant bits share
one instance. Anything with `rel = ∅` (`identifier`, literals, most of the grammar) is
never copied.

### Recursion

The pass is a memo table keyed by `(X, m)` plus a worklist:

```text
instance(X, m):
    m = m & rel(X)
    if m == 0: return X                    // original nodes, never copied
    if table[(X, m)] exists: return it     // recursion closes here
    shell = copy of X's LHS node           // register BEFORE copying the body
    table[(X, m)] = shell
    worklist.append((shell, X, m))
    return shell

while worklist not empty:
    (shell, X, m) = pop
    copy X's alternates into shell, dropping alternates whose tests fail under m
    for each nonterminal occurrence Y (add A, remove R) in the copied body:
        occurrence.alt = instance(Y, (m | A) & ~R)
```

The empty shell goes into the table before its body is copied. When the body reaches `X`
again, directly or through a cycle, the lookup finds the shell and links back to it. A
recursive production becomes a cycle between copies, just as the original grammar has a
cycle between originals. This is how a compiler handles a recursive generic function when
it makes a type-specific copy (keyed by function and type arguments), and it is how the
NFA→DFA subset construction works.

It always terminates: there are at most `|N| × 2^|rel|` keys. With today's modes a
nonterminal has 2–4 possible subsets at most.

### Worked example

Simplified from `Swift.apus` (`trailingClosure` left out):

```apus
statements            = statement { statement } .
statement             = expression | ifStatement .
ifStatement           = "if" condition codeBlock .
condition             = @setMode(stmtCondition) expression .
expression            = primary { "." identifier } .
primary               = identifier | "(" expression ")" | closureExpression .
closureExpression     = samelineOpenedClosure | @rejectsMode(stmtCondition) newlineOpenedClosure .
newlineOpenedClosure  = "{" <n> @clearMode(stmtCondition) statements? "}" .
samelineOpenedClosure = "{" >n< @clearMode(stmtCondition) statements? "}" .
```

Relevance of `stmtCondition` (`sc`):

| Nonterminal | `rel` | Why |
| --- | --- | --- |
| `closureExpression` | `{sc}` | tests it directly |
| `primary` | `{sc}` | reaches `closureExpression` without changing `sc` |
| `expression` | `{sc}` | reaches `primary` without changing `sc` |
| `statement` | `{sc}` | reaches `expression` without changing `sc` |
| `statements` | `{sc}` | reaches `statement` without changing `sc` |
| `condition` | `∅` | sets `sc` itself, so the caller's `sc` does not matter |
| `ifStatement` | `∅` | only reaches `sc` through `condition` |
| `samelineOpenedClosure` | `∅` | clears `sc` before `statements` |
| `newlineOpenedClosure` | `∅` | clears `sc` before `statements` |
| `identifier` | `∅` | no mode tests below it |

`statements` and `statement` have relevant bits but are only ever reached with `sc = 0`, so
no copy of them is created. Only reachable instances are made.

Expansion from `statements⟨0⟩` (the originals):

1. `statement → ifStatement → condition`. `condition` sets `sc` and calls
   `instance(expression, {sc})`, creating **`expression⟨sc⟩`**.
2. `expression⟨sc⟩ → primary` creates **`primary⟨sc⟩`**.
3. In `primary⟨sc⟩`: `identifier` links to the original. `"(" expression ")"` finds the
   `(expression, {sc})` shell from step 1 and links back to it (recursion closes).
   `closureExpression` creates **`closureExpression⟨sc⟩`**.
4. `closureExpression⟨sc⟩` keeps only the `samelineOpenedClosure` alternate; the
   newline-opened alternate fails `@rejectsMode` statically.
5. `samelineOpenedClosure` has `rel = ∅`, so the original is used. Its body clears `sc` and
   links to the original `statements`. The recursion leaves condition mode and returns to
   the original grammar.

```text
statements ─► statement ─► expression ─► primary ─► closureExpression ─► {sameline | newline}
                  │            ▲                                              │
                  ▼            └──────────── statements ◄─────────────────────┘
             ifStatement ─► condition ─► expression⟨sc⟩ ─► primary⟨sc⟩ ─► closureExpression⟨sc⟩ ─► {sameline}
                                               ▲             │   │                                    │
                                               └─ "(" … ")" ─┘   └─► identifier (shared)              │
                                                                                                      ▼
                                                                                   statements (original)
```

Three productions are copied once each; everything else exists once.

### Consequences for the rest of APUS

- **Parser:** unchanged algorithm. A descriptor's slot already says which mode it is in,
  because `expression⟨sc⟩`'s slots are different objects with different `number`s.
- **BSR:** yields are keyed by `L.number`, so readings from different modes cannot merge
  (Observation 2 is closed with no extra code).
- **First/follow, exclude sets, `nameID`s, Oracle registration:** run after the pass and
  treat copies as ordinary nodes.
- **SwiftSyntax converter, `@builder`:** keyed on `name`, which copies keep.
- **Tooling and diagnostics** (HTML/MD dumps, ambiguity reports): show copies; print
  `name⟨mode⟩` or collapse by `origin`.

### What gets deleted

- `Descriptor.mode`, `ParsePosition.mode`, `cMode`, the `mode:` parameters on
  `addDescriptor`, `addDescriptorsForAlternates` and `continuationViable`
- `modeForOccurrence`, `modeAllows`, and the per-descriptor `hasModeAnnotation` check in the
  parse loop
- `GrammarNode.hasModeAnnotation`. TODO #1 says to remove optimizations that add more
  complexity than speedup, and this is one.

`Descriptor` goes back to 3 words. The GLL core goes back to the paper's algorithm. Modes
exist only in `ApusParser` (syntax), the new pass, and diagnostics.

### Cost made visible

Print at grammar load (verbose): for each mode, the nonterminals where it is live and the
number of clones it adds. This is the performance budget, and it is also a semantic lint:
the `trailingClosure` leak would show up as "live in `statements`, `codeBlock`, …". The
current 64-bit cap stays, since it bounds `rel` bitsets.

Worst case is `Σ 2^|rel(X)|` over reachable `X`. With today's five modes, mostly confined
to the expression grammar, expect about ×2–×3 on that subgrammar and ×1 everywhere else.
Add a load-time guard (for example, a warning above 2× total node count).

## Scoping discipline (independent of representation)

Inherited bits are dynamically scoped. They flow everywhere until something clears them.
swift-syntax resets the flavor at every island by default. Two rules:

1. A mode is justified only if it must pass through at least one intermediate nonterminal.
   `trailingClosure` does not: `trailingClosures` calls `closureExpression` directly. It is
   an occurrence marker, so it should be a grammar split, e.g.
   `trailingClosures = … ( samelineOpenedClosure | @rejectsMode(stmtCondition) newlineOpenedClosure ) …`.
   That removes the leak and one mode.
2. Every mode that remains gets its liveness reviewed through the diagnostic above.

## Point (2) revisited: what modes should take over

Once modes cost nothing where they are not used, "use them more to justify the cost" no
longer applies. The principle that does apply is a clean split of responsibilities:

- **Parse time (grammar + modes):** what is *valid* in this context.
- **Oracle:** which of several *valid* readings wins.

Candidates that are really context, ranked by payoff:

1. **`@sameLine` / `@sameLineOutsideBrackets` → a trivia mode.** `SameLineSpanRule` is a
   post-parse BSR walk with memo and cycle-cut subtleties (see the fixes in TODO #2). It
   models swift-syntax's `leadingTriviaLexingMode`, which is lexer state, i.e. context.
   With specialization, `@sameLine X` is `@setMode(noNewlineTrivia) X`, and
   `…OutsideBrackets` adds `@clearMode(noNewlineTrivia)` at bracket bodies. Terminal clones
   under that bit get a static "leading trivia may not contain a newline" flag. This
   removes an Oracle rule and prunes during the parse. It depends on specialization:
   runtime modes cannot cheaply reach the terminal matcher. Before switching, map the
   walk's edge cases (zero-width suffix allowance, committed multiline tokens).
2. **Postfix vs. statement `#if` lookbehinds** (`<-<( identifier … )`, `<+<( "#endif" )` on
   `ifDirectiveClause`). Being in postfix position is a structural fact, but it is
   approximated by token lookbehind. TODO #2 residual (a) is exactly where that
   approximation fails. Use a call-site split or a mode set at the postfix-expression
   occurrence.
3. **Per-use audit** of `@cannotParse` (23) and `@prefer` (32). Convert only uses that
   encode *position* rather than choose between two valid readings. No mass conversion.

Not candidates: `@longest`/`@shortest`, `@prefer` between valid readings, `@preempt`, and
scanner policies. `@left`/`@right` could in principle be compiled the same way (SDF
priorities → grammar), but they apply to immediate children, not to everything below.
Leave them alone.

## Findings from the first implementation (2026-10-07)

Implemented: the specialization pass (`ModeSpecialization.swift`), runtime mode machinery deleted
(`Descriptor`/`ParsePosition` back to the pre-mode layout), by-name yield queries widened to
`grammar.instances(of:)`, Oracle/diagnostic walks no longer follow RHS references. All 19,497
SwiftSyntax tests pass. But the grammar blows up:

| State | Copies | Nodes | Grammar load | SwiftSyntax suites (wall) |
| --- | --- | --- | --- | --- |
| Runtime modes (baseline) | 0 | — | < 1s | 67s |
| Specialization, grammar as is | 17,001 | 266,894 | 35s | 265s |
| + `@resetModes` on `codeBlock` and both closure productions | 7,857 | 128,572 | 16s | 294s |
| **Declared scopes (`@carries`), final** | **94** | **8,296** | **0.84s** | **43s** |

Full scheme (all suites, warm build): 177s with runtime modes → 111s with declared scopes, all
23,823 tests passing.

Most nonterminals get `2^k − 1` copies. The reason is semantic, not the pass. Modes are inherited
by default, and outside code blocks and closures the Swift grammar is one strongly connected
component: types reach attributes, attributes reach expressions, expressions reach postfix `#if`,
whose bodies reach `statements`, which reach everything. So every mode set anywhere is *relevant*
everywhere, and nesting makes almost every combination *reachable*. Relevance inference cannot
narrow this, because every nonterminal really is on some path from a set-site to a test.

The leaks are visible in intent too. Each mode is meant for a narrow region:

| Mode | Intended scope | Actually live in |
| --- | --- | --- |
| `stmtCondition` | expression chain from `conditionExpression` to `closureExpression` | everything |
| `trailingClosure` | the `closureExpression` directly under `trailingClosures` | fixed by `@resetModes` (2 copies) |
| `initializerBodyMode` | `statement`s directly in an initializer body, incl. statement-level `#if` | everything |
| `ifConfigBody` | first `statement` of an `#if` body | everything |
| `bindingIntroducer` | introduced binding *names* in `matchPattern` | everything, incl. type annotations |
| `optionalBinding` | the binding name of `if let`/`guard let` | everything, incl. types |
| `availableAttributeMode` | `@available(…)` arguments | its region (0 copies) |

The runtime design has the same leaks. It just pays for them per descriptor and hides them.

`@resetModes` (a production-level "fresh context" boundary) was an intermediate step. Declared
scopes made it unnecessary and it was removed.

### Decision: declared scope per production (`@carries`)

Option A, in the scope-per-production form. `@carries(m …)` at the start of a production declares
that `m` passes into that nonterminal; entering any other nonterminal drops it (swift-syntax
parameter semantics: a context exists only on the functions that forward it). The pass passes
`childMode & carries(callee)` to each callee, and relevance is computed within scopes. Grammar
load fails on an undeclared mode, a `@setMode(m) Y` whose `Y` does not carry `m`, and a test on a
mode that can never be present; it reports copy counts, ineffective `@clearMode`s and scope exits
(`Grammar.parserModeReport`). Syntax and rules: `apus.md` § Parser Modes.

Scopes in `Swift.apus`:

| Mode | Carried by | Copies |
| --- | --- | --- |
| `stmtCondition` | the expression chain from `conditionExpression` to `closureExpression` (40 productions, incl. parens, tuples, collection literals, member/call/subscript suffixes, `switch` expressions) | 41 |
| `trailingClosure` | `closureExpression` | 2 |
| `initializerBodyMode` | `codeBlock`, `statements`, `statement`, statement-level `#if` productions | 15 |
| `ifConfigBody` | `statements`, `statement`, statement-level `#if` productions | 10 |
| `bindingIntroducer` | match patterns plus the expression chain they parse through, including call arguments and tuples (swift-syntax forwards its `pattern:` context there) | 26 |
| `optionalBinding` | `bindingPattern` and its tuple/subpattern productions | 6 |

The only overlap is ⟨initializerBodyMode ifConfigBody⟩: an `#if` directly inside an initializer
body. Grammar changes that came with it:

- `@clearMode(stmtCondition)` on `functionCallArgument` and in the closure bodies: removed; those
  productions do not carry the mode.
- `availableAttributeMode`: removed. It never had an effect — `availabilityValue` reaches strings
  only through `availabilityStringLiteral`, which has no raw forms, so the `@rejectsMode` on
  `staticStringLiteral` could never fire. The specialization diagnostics (0 copies) exposed it.
- `bindingIntroducer` initially stopped at `functionCallArgument`, which wrongly accepted
  `case let Optional.some(Swift::decl1j)` (reject test). Extending the scope to call argument
  clauses, tuples and the infix chain fixed it.

Behavior change to keep in mind: the leaks are gone. `initializerBodyMode` no longer reaches nested
`if`/`do` bodies of an initializer (swift-syntax rejects `init(…)` there), and binding/optional-binding
modes no longer reach type annotations or enum-case qualifier types.

## Follow-up candidates, examined and set aside (2026-10-07)

The two "context in disguise" candidates from "Point (2) revisited" do not fit modes after all.

**`@sameLine` as a trivia mode.** A mode version would be: every terminal matched under the mode
checks its LEADING gap (`>n<` at its cursor), which is exactly swift-syntax's `.noNewlines`
leading-trivia lexing mode. The region's opener is placed outside the mode. That fits the shallow
`@sameLineOutsideBrackets` on `compilationCondition`. Its scope is the expression spine, and its
first gap is already `>n<`. Bracket openers would still need `@carries` with `@clearMode` on
contents and closer. It does not fit the deep `@sameLine` on
`singleLineInterpolatedStringLiteral`:

- swift-syntax keeps that lexer state at any depth, including inside closures and statements in
  the interpolation. The mode would have to be carried by almost every production, roughly
  doubling the grammar, and it would also combine with the other modes.
- The parse-time gap test is existential over commits ending at the cursor. `SameLineSpanRule`
  reads the exact commit of each tile of a derivation, and the per-derivation check is why it
  exists.

So the Oracle rule has to stay for the deep case. Converting only the shallow case would remove
just the bracket-prefix branch (`Gaps.any`, `bracketedPrefix`, about 25 lines). Not worth the risk.

**Structural postfix `#if` (TODO #2 residual a).** Whether a leading-dot `#if` is postfix depends
on the LEFT SIBLING: swift-syntax's postfix-suffix loop is still active when the previous statement
ends in an expression. Modes flow down to children, never sideways, so they cannot express this.
The realistic options:

- **A BSR lookbehind predicate,** "no `postfixExpression` yield ends here". This is the dual of
  `@cannotParse`, but raw yields include speculative ones. For example, `x { }` in
  `if x { }⏎#if A⏎.b⏎#endif` is a raw `postfixExpression` yield that would wrongly suppress the
  valid statement-level reading.
- **A grammar refactor** that classifies statements by how they end. This is invasive.

Both are grammar-design work for TODO #2a itself, not mode work.

## Remaining work

Grammar load still recomputes FIRST/FOLLOW over the copies with the whole-grammar fixpoint. That
is fine at 94 copies; revisit only if scopes grow.
