# Parser Flavors as Grammar Specialization

Design note for TODO #1 (flavor overhead). Status: implemented 2026-10-07 (specialization +
declared scopes with `@flavors`); see Findings and Decision below.
Follows `Parser Flavors Migration Plan.md`, which introduced the runtime flavor bitset.

Renamed 2026-10-21: "parser modes" are now **flavors** (`@modeScope` → `@flavors`, `@setMode` →
`@setFlavor`, and so on), after swift-syntax `ExprFlavor`. At the same time `trailingClosure` stopped
being a flavor: it is the `trailingClosure` nonterminal used by `trailingClosures`, which removed the
only test that needed two flavors at once. Measurements below predate both changes.

## The question

The runtime design widens `Descriptor` (24 → 32 bytes) and CRF `ParsePosition` with a
`UInt64 flavor`. Every descriptor and CRF hash pays for the flavor, but only a small part of
the Swift grammar uses flavors (15 `@setFlavor`, 6 `@clearFlavor`, 6 `@requiresFlavor`,
9 `@rejectsFlavor`). The full suite went from about 110s to about 151s. Should we
(1) make that overhead smaller, or (2) use flavors much more widely so the overhead pays
for itself?

Short answer: neither. A finite set of inherited flavor bits is not runtime state. It is
part of which nonterminal you are in. Compile it into the grammar (each nonterminal gets
one copy per flavor combination that actually matters) and the runtime cost is zero. Copies
are made only where flavors matter. That removes the overhead (1) and fixes a correctness
gap. Point (2) then becomes a separate question: which existing mechanisms are really
"context" problems? That question has a clear answer (see below). It is not "use flavors for
ambiguity in general".

## Observation 1: flavors are finite inherited attributes, so they are a CFG

`@setFlavor`/`@clearFlavor` compute the child's flavor from the parent's flavor with a fixed
function per occurrence: `(m | add) & ~remove`. `@requiresFlavor`/`@rejectsFlavor` are fixed
tests on `m`. A CFG with finitely many inherited attribute values is the same as a plain
CFG with indexed nonterminals `X⟨m⟩`. This is the parameterized-nonterminal construction
(Happy-GLL, `articles/Happy-GLL- …pdf`; SDF/Rascal parameterized sorts). swift-syntax's
`ExprFlavor` is the same idea in handwritten form: a parameter passed down explicitly.

Carrying `m` in descriptors is the interpreted form of this construction. Specialization
is the compiled form.

## Observation 2: the runtime design is incomplete. BSR is flavor-blind.

Flavor is part of descriptor identity and CRF identity, but `addYield(L:i:k:j:)` stores
yields under `L.number` without the flavor (`BinarySubtreeRepresentation.swift:28`).
Suppose the same `(X, i, j)` is derived under two flavors, and a gated alternative is valid
in only one of them (`@requiresFlavor(ifConfigBody)` on `ifDirectiveClause`,
`@requiresFlavor(optionalBinding) "self"`). Then the yields merge. The DerivationBuilder, the Oracle and the converter
can attach the gated reading under a parent from the other flavor. The possible symptoms are
spurious residual ambiguity or a wrong tree. No concrete reproducer is known yet. The
hazard comes from the representation itself. Closing it at runtime means widening the BSR
as well, which adds more overhead. With specialization it cannot happen: each clone has
its own `number`.

## Observation 3: the overhead is probably not only hashing width

A flavor splits CRF clusters even for nonterminals whose language does not depend on it. For
example, `identifier` at position `i` under `stmtCondition` and under `0` are two clusters
with two descriptor sets. Some bits also leak far beyond their intended scope:

- `trailingClosure` is set in `trailingClosures` and never cleared. So the whole body of
  every trailing closure runs in a different flavor from the same text parsed another way.
  GLL often explores both readings of `{` after an expression (trailing closure vs. a
  separate statement), and the body is then parsed twice instead of shared.
- `ifConfigBody` is cleared only between statements. It still applies inside closures that
  are nested in the first statement of an `#if` body. (Check whether this ever changes
  acceptance.)

Hypothesis: a real part of the 110s → 151s increase is duplicated work, not the extra 8
bytes. **Step 0** below measures this before any redesign.

## Design: compile-time specialization with relevance projection

### Relevance

`rel(X)` is the set of flavor bits that can change the language of nonterminal or bracket
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
  grammar without flavors, and most of the Swift grammar, is left as it is. This is what
  TODO #1 asks for: no tax on grammars or regions that do not use flavors.
- Only reachable instances are created.
- Each clone keeps `name` and gets an `origin: GrammarNode` link. Anything keyed on names
  (SwiftSyntax converter, `@builder`, messages, diagnostics) keeps working.
- The pass runs after `ApusParser` builds the graph and before `assignNameIDs`,
  `propagateExcludeSets`, `populateBitSets` and first/follow. Later passes and Oracle
  registration then see the clones as ordinary nodes. Their FIRST/FOLLOW sets are more
  precise (for example, `closureExpression⟨stmtCondition, trailingClosure⟩` has no
  newline-opened alternative). That improves `testSelect`/`continuationViable` pruning,
  so this is likely faster than before flavors existed, not just as fast.

### What is copied

Yes: specialization makes real copies of `GrammarNode`s, once, at grammar load. A copy is
made per **(nonterminal, projected flavor)** pair. Copying `X` for flavor `m` deep-copies its
production subgraph: the LHS node, its ALT chain, each alternate's `.seq` chain (terminal
slots, layout nodes, lookarounds, inline brackets `DO/OPT/KLN/POS`, END nodes). Copied
terminals keep their `nameID`, so the scanner and lex cache stay shared. Each copy keeps
`name` and gets an `origin` link back to the original.

Inside the copy, two things change:

1. **Flavor tests are decided statically.** An alternate whose `@requiresFlavor`/`@rejectsFlavor`
   fails under `m` is left out of the copy.
2. **Nonterminal occurrences are relinked.** An occurrence's `.alt` (pointing to the callee
   LHS) is redirected to `Y⟨((m | add) & ~remove) & rel(Y)⟩`. If that projects to `0`,
   it points at the original `Y`.

The `& rel(Y)` projection makes call sites whose flavors differ only in irrelevant bits share
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

It always terminates: there are at most `|N| × 2^|rel|` keys. With today's flavors a
nonterminal has 2–4 possible subsets at most.

### Worked example

Simplified from `Swift.apus` (`trailingClosure` left out):

```apus
statements            = statement { statement } .
statement             = expression | ifStatement .
ifStatement           = "if" condition codeBlock .
condition             = @setFlavor(stmtCondition) expression .
expression            = primary { "." identifier } .
primary               = identifier | "(" expression ")" | closureExpression .
closureExpression     = samelineOpenedClosure | @rejectsFlavor(stmtCondition) newlineOpenedClosure .
newlineOpenedClosure  = "{" <n> @clearFlavor(stmtCondition) statements? "}" .
samelineOpenedClosure = "{" >n< @clearFlavor(stmtCondition) statements? "}" .
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
| `identifier` | `∅` | no flavor tests below it |

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
   newline-opened alternate fails `@rejectsFlavor` statically.
5. `samelineOpenedClosure` has `rel = ∅`, so the original is used. Its body clears `sc` and
   links to the original `statements`. The recursion leaves condition flavor and returns to
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

- **Parser:** unchanged algorithm. A descriptor's slot already says which flavor it is in,
  because `expression⟨sc⟩`'s slots are different objects with different `number`s.
- **BSR:** yields are keyed by `L.number`, so readings from different flavors cannot merge
  (Observation 2 is closed with no extra code).
- **First/follow, exclude sets, `nameID`s, Oracle registration:** run after the pass and
  treat copies as ordinary nodes.
- **SwiftSyntax converter, `@builder`:** keyed on `name`, which copies keep.
- **Tooling and diagnostics** (HTML/MD dumps, ambiguity reports): show copies; print
  `name⟨flavor⟩` or collapse by `origin`.

### What gets deleted

- `Descriptor.flavor`, `ParsePosition.flavor`, `cFlavor`, the `flavor:` parameters on
  `addDescriptor`, `addDescriptorsForAlternates` and `continuationViable`
- `flavorForOccurrence`, `flavorAllows`, and the per-descriptor `hasFlavorAnnotation` check in the
  parse loop
- `GrammarNode.hasFlavorAnnotation`. TODO #1 says to remove optimizations that add more
  complexity than speedup, and this is one.

`Descriptor` goes back to 3 words. The GLL core goes back to the paper's algorithm. Flavors
exist only in `ApusParser` (syntax), the new pass, and diagnostics.

### Cost made visible

Print at grammar load (verbose): for each flavor, the nonterminals where it is live and the
number of clones it adds. This is the performance budget, and it is also a semantic lint:
the `trailingClosure` leak would show up as "live in `statements`, `codeBlock`, …". The
current 64-bit cap stays, since it bounds `rel` bitsets.

Worst case is `Σ 2^|rel(X)|` over reachable `X`. With today's five flavors, mostly confined
to the expression grammar, expect about ×2–×3 on that subgrammar and ×1 everywhere else.
Add a load-time guard (for example, a warning above 2× total node count).

## Scoping discipline (independent of representation)

Inherited bits are dynamically scoped. They flow everywhere until something clears them.
swift-syntax resets the flavor at every island by default. Two rules:

1. A flavor is justified only if it must pass through at least one intermediate nonterminal.
   `trailingClosure` does not: `trailingClosures` calls `closureExpression` directly. It is
   an occurrence marker, so it should be a grammar split, e.g.
   `trailingClosures = … ( samelineOpenedClosure | @rejectsFlavor(stmtCondition) newlineOpenedClosure ) …`.
   That removes the leak and one flavor.
2. Every flavor that remains gets its liveness reviewed through the diagnostic above.

## Point (2) revisited: what flavors should take over

Once flavors cost nothing where they are not used, "use them more to justify the cost" no
longer applies. The principle that does apply is a clean split of responsibilities:

- **Parse time (grammar + flavors):** what is *valid* in this context.
- **Oracle:** which of several *valid* readings wins.

Candidates that are really context, ranked by payoff:

1. **`@sameLine` / `@sameLineOutsideBrackets` → a trivia flavor.** `SameLineSpanRule` is a
   post-parse BSR walk with memo and cycle-cut subtleties (see the fixes in TODO #2). It
   models swift-syntax's `leadingTriviaLexingMode`, which is lexer state, i.e. context.
   With specialization, `@sameLine X` is `@setFlavor(noNewlineTrivia) X`, and
   `…OutsideBrackets` adds `@clearFlavor(noNewlineTrivia)` at bracket bodies. Terminal clones
   under that bit get a static "leading trivia may not contain a newline" flag. This
   removes an Oracle rule and prunes during the parse. It depends on specialization:
   runtime flavors cannot cheaply reach the terminal matcher. Before switching, map the
   walk's edge cases (zero-width suffix allowance, committed multiline tokens).
2. **Postfix vs. statement `#if` lookbehinds** (`<-<( identifier … )`, `<+<( "#endif" )` on
   `ifDirectiveClause`). Being in postfix position is a structural fact, but it is
   approximated by token lookbehind. TODO #2 residual (a) is exactly where that
   approximation fails. Use a call-site split or a flavor set at the postfix-expression
   occurrence.
3. **Per-use audit** of `@cannotParse` (23) and `@prefer` (32). Convert only uses that
   encode *position* rather than choose between two valid readings. No mass conversion.

Not candidates: `@longest`/`@shortest`, `@prefer` between valid readings, `@preempt`, and
scanner policies. `@left`/`@right` could in principle be compiled the same way (SDF
priorities → grammar), but they apply to immediate children, not to everything below.
Leave them alone.

## Findings from the first implementation (2026-10-07)

Implemented: the specialization pass (`FlavorSpecialization.swift`), runtime flavor machinery deleted
(`Descriptor`/`ParsePosition` back to the pre-flavor layout), by-name yield queries widened to
`grammar.instances(of:)`, Oracle/diagnostic walks no longer follow RHS references. All 19,497
SwiftSyntax tests pass. But the grammar blows up:

| State | Copies | Nodes | Grammar load | SwiftSyntax suites (wall) |
| --- | --- | --- | --- | --- |
| Runtime flavors (baseline) | 0 | — | < 1s | 67s |
| Specialization, grammar as is | 17,001 | 266,894 | 35s | 265s |
| + `@resetFlavors` on `codeBlock` and both closure productions | 7,857 | 128,572 | 16s | 294s |
| **Declared scopes (`@flavors`), final** | **94** | **8,296** | **0.84s** | **43s** |

Full scheme (all suites, warm build): 177s with runtime flavors → 111s with declared scopes, all
23,823 tests passing.

Most nonterminals get `2^k − 1` copies. The reason is semantic, not the pass. Flavors are inherited
by default, and outside code blocks and closures the Swift grammar is one strongly connected
component: types reach attributes, attributes reach expressions, expressions reach postfix `#if`,
whose bodies reach `statements`, which reach everything. So every flavor set anywhere is *relevant*
everywhere, and nesting makes almost every combination *reachable*. Relevance inference cannot
narrow this, because every nonterminal really is on some path from a set-site to a test.

The leaks are visible in intent too. Each flavor is meant for a narrow region:

| Flavor | Intended scope | Actually live in |
| --- | --- | --- |
| `stmtCondition` | expression chain from `conditionExpression` to `closureExpression` | everything |
| `trailingClosure` | the `closureExpression` directly under `trailingClosures` | fixed by `@resetFlavors` (2 copies) |
| `ifConfigBody` | first `statement` of an `#if` body | everything |
| `bindingIntroducer` | introduced binding *names* in `matchPattern` | everything, incl. type annotations |
| `optionalBinding` | the binding name of `if let`/`guard let` | everything, incl. types |
| `availableAttributeFlavor` | `@available(…)` arguments | its region (0 copies) |

The runtime design has the same leaks. It just pays for them per descriptor and hides them.

`@resetFlavors` (a production-level "fresh context" boundary) was an intermediate step. Declared
scopes made it unnecessary and it was removed.

### Decision: declared scope per production (`@flavors`)

Option A, in the scope-per-production form. `@flavors(m …)` at the start of a production declares
that `m` passes into that nonterminal; entering any other nonterminal drops it (swift-syntax
parameter semantics: a context exists only on the functions that forward it). The pass passes
`childFlavor & carries(callee)` to each callee, and relevance is computed within scopes. Grammar
load fails on an undeclared flavor, a `@setFlavor(m) Y` whose `Y` does not carry `m`, and a test on a
flavor that can never be present; it reports copy counts, ineffective `@clearFlavor`s and scope exits
(`Grammar.parserFlavorReport`). Syntax and rules: `apus.md` § Parser Flavors.

Scopes in `Swift.apus`:

| Flavor | Carried by | Copies |
| --- | --- | --- |
| `stmtCondition` | the expression chain from `conditionExpression` to `closureExpression` (40 productions, incl. parens, tuples, collection literals, member/call/subscript suffixes, `switch` expressions) | 41 |
| `trailingClosure` | `closureExpression` | 2 |
| `ifConfigBody` | `statements`, `statement`, statement-level `#if` productions | 10 |
| `bindingIntroducer` | match patterns plus the expression chain they parse through, including call arguments and tuples (swift-syntax forwards its `pattern:` context there) | 26 |
| `optionalBinding` | `bindingPattern` and its tuple/subpattern productions | 6 |

Grammar changes that came with it:

- `@clearFlavor(stmtCondition)` on `functionCallArgument` and in the closure bodies: removed; those
  productions do not carry the flavor.
- `availableAttributeFlavor`: removed. It never had an effect — `availabilityValue` reaches strings
  only through `availabilityStringLiteral`, which has no raw forms, so the `@rejectsFlavor` on
  `staticStringLiteral` could never fire. The specialization diagnostics (0 copies) exposed it.
- `bindingIntroducer` initially stopped at `functionCallArgument`, which wrongly accepted
  `case let Optional.some(Swift::decl1j)` (reject test). Extending the scope to call argument
  clauses, tuples and the infix chain fixed it.

Behavior change to keep in mind: the leaks are gone. Binding/optional-binding flavors no longer reach
type annotations or enum-case qualifier types.

`initializerBodyFlavor` (removed 2026-10-11) let a bare `init(…)` call stand as a statement in an
initializer body. swiftc ParseDecl.cpp `isStartOfSwiftDecl` reads it that way only to diagnose a
missing `self.`, and the type checker always rejects it, so `Swift.apus` now treats a statement-start
`init` as a declaration everywhere and needs no flavor for it.

## Follow-up candidates, examined and set aside (2026-10-07)

The two "context in disguise" candidates from "Point (2) revisited" do not fit flavors after all.

**`@sameLine` as a trivia flavor.** A flavor version would be: every terminal matched under the flavor
checks its LEADING gap (`>n<` at its cursor), which is exactly swift-syntax's `.noNewlines`
leading-trivia lexing mode. The region's opener is placed outside the flavor. That fits the shallow
`@sameLineOutsideBrackets` on `compilationCondition`. Its scope is the expression spine, and its
first gap is already `>n<`. Bracket openers would still need `@flavors` with `@clearFlavor` on
contents and closer. It does not fit the deep `@sameLine` on
`singleLineInterpolatedStringLiteral`:

- swift-syntax keeps that lexer state at any depth, including inside closures and statements in
  the interpolation. The flavor would have to be carried by almost every production, roughly
  doubling the grammar, and it would also combine with the other flavors.
- The parse-time gap test is existential over commits ending at the cursor. `SameLineSpanRule`
  reads the exact commit of each tile of a derivation, and the per-derivation check is why it
  exists.

So the Oracle rule has to stay for the deep case. Converting only the shallow case would remove
just the bracket-prefix branch (`Gaps.any`, `bracketedPrefix`, about 25 lines). Not worth the risk.

**Structural postfix `#if` (TODO #2 residual a).** Whether a leading-dot `#if` is postfix depends
on the LEFT SIBLING: swift-syntax's postfix-suffix loop is still active when the previous statement
ends in an expression. Flavors flow down to children, never sideways, so they cannot express this.
The realistic options:

- **A BSR lookbehind predicate,** "no `postfixExpression` yield ends here". This is the dual of
  `@cannotParse`, but raw yields include speculative ones. For example, `x { }` in
  `if x { }⏎#if A⏎.b⏎#endif` is a raw `postfixExpression` yield that would wrongly suppress the
  valid statement-level reading.
- **A grammar refactor** that classifies statements by how they end. This is invasive.

Both are grammar-design work for TODO #2a itself, not flavor work.

## Remaining work

Grammar load still recomputes FIRST/FOLLOW over the copies with the whole-grammar fixpoint. That
is fine at 94 copies; revisit only if scopes grow.
