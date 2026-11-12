import Base

# THE SPECIFICATION: what parsing an EBNF grammar means, independent of any parser.
#
# Right-hand sides are regular expressions over symbols, after Scott and Johnstone,
# "GLL Syntax Analysers For EBNF Grammars", Definition 1: a sequence of items, where
# an item is a symbol, a bracket ( ) [ ] { } < > around alternatives, or ε. ε is
# notation for "nothing here", not a symbol: it stands at no position of a sentential
# form. As in Swift Apus, where "" and ε are EPS items, it records a step of its own.
# An empty sequence is also ε; its one step is at dot 0. Terminals are token kinds,
# nonterminals are ids, as before.

# A symbol of a grammar. A terminal is a token kind: the input is a list of token kinds,
# so the lexer stays outside the specification. A nonterminal is a number; the
# productions say what it derives.
type Symbol is Data:
  Terminal{kind: Nat}
  Nonterminal{id: Nat}

# The four kinds of bracket around alternatives τ = τ1 | .. | τn. ( τ ) is a group: τ
# exactly once. [ τ ] is an optional: τ at most once. { τ } is a closure: τ any number
# of times, also none. < τ > is a positive closure: τ at least once.
type Bracket is Data:
  Group{}
  Optional{}
  Closure{}
  Positive{}

# One item of a sequence: a symbol, a bracket around one or more alternatives, or ε. A
# right side, and every alternative inside a bracket, is a list of items. Brackets nest,
# so a right side is a small tree of items.
type Item is Data:
  Sym{symbol: Symbol}
  Brack{kind: Bracket, alts: +List<+List<Item>>}
  Eps{}

# One production `lhs = rhs`. Alternatives at the top are separate productions, so a
# nonterminal's rule A ::= τ1 | ... | τt is t productions. They are numbered by their
# place in the grammar, and a parse tree names the production it used by that number.
type Production is Data:
  Production{lhs: Nat, rhs: +List<Item>}

# PARSE TREES. A bracket gets a node of its own, as in Scott's "root-node based
# choice" (section 3.1): it groups what the bracket matched, which is what makes
# closures with nullable bodies come out right.
#   Leaf{kind}           a token
#   Node{index, ...}     a nonterminal, expanded by production `index`
#   Pick{alt, ...}       a bracket matched once, by its alternative number `alt`
#   Skip{}               an ε, or an optional [ τ ] that matched nothing (Scott's ε node)
#   Loop{rounds}         a closure { τ } or < τ >; each round is a Pick
type Tree is Data:
  Leaf{kind: Nat}
  Node{index: Nat, children: +List<Tree>}
  Pick{alt: Nat, children: +List<Tree>}
  Skip{}
  Loop{rounds: +List<Tree>}

# Is production number `index` a production of nonterminal `id`? A number past the end
# of the grammar names no production, so then the answer is no.
def lhsIs(+grammar: +List<Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Production{lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+i:
      lhsIs(rest, i, id)

# The right side of production number `index`: the items it expands to. Past the end of
# the grammar it is empty; that never matters, because `fits` asks `lhsIs` first.
def rhsOf(+grammar: +List<Production>, index: Nat) -> +List<Item>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Production{lhs, rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+i:
      rhsOf(rest, i)

# Alternative number `a` of a bracket, counting from 0. It is empty when there is no
# such alternative; `isAlt` guards every use, so that never matters.
def altOf(alts: +List<+List<Item>>, a: Nat) -> +List<Item>:
  match alts a:
    case Nil{} _:
      []
    case Con{alt, rest} 0n:
      alt
    case Con{alt, rest} 1n+b:
      altOf(rest, b)

# Is `a` the number of one of the bracket's alternatives, counting from 0?
def isAlt(alts: +List<+List<Item>>, +a: Nat) -> Bool:
  Nat.is_lt(a, List.length(&2, +List<Item>, alts))

# The tokens at the leaves of the forest, left to right: what the forest spells. A skip
# spells nothing; every other tree spells what its children spell.
def leaves(forest: +List<Tree>) -> +List<Nat>:
  match forest:
    case Nil{}:
      []
    case Con{Leaf{kind}, ts}:
      kind <> leaves(ts)
    case Con{Node{index, children}, ts}:
      List.append(&2, Nat, leaves(children), leaves(ts))
    case Con{Pick{a, children}, ts}:
      List.append(&2, Nat, leaves(children), leaves(ts))
    case Con{Skip{}, ts}:
      leaves(ts)
    case Con{Loop{rounds}, ts}:
      List.append(&2, Nat, leaves(rounds), leaves(ts))

# A tree consumes input when it has a leaf. A leaf is always a token: ε is matched by a
# Skip, which has no leaves (unlike Swift Apus, which counts an EPS node as a leaf). So a
# round of nothing but ε's, Pick{a, [Skip, Skip]}, consumes nothing. A tree without
# leaves matched the empty input; the rule on empty rounds below is about such trees.
def consumes(tree: Tree) -> Bool:
  Bool.not(List.is_empty(&2, Nat, leaves([tree])))

# Does every round of a loop consume input?
def allConsume(rounds: +List<Tree>) -> Bool:
  match rounds:
    case Nil{}:
      True{}
    case Con{+r, rest}:
      Bool.and(consumes(r), allConsume(rest))

# NO REMOVABLE EMPTY ROUNDS. Every bracket repeats its body: ( τ ) exactly once,
# [ τ ] at most once, { τ } any number of times, < τ > at least once. A round that
# consumes nothing is removable when the bracket keeps its minimum without it; trees
# that differ only in such rounds differ only in how often nothing was repeated, so
# they are one reading, not an ambiguity. A parse tree has none of them: a bracket has
# at least its minimum number of rounds, and an empty round only when it has exactly
# its minimum. So [ τ ] over nothing is a skip, { τ } over nothing has no rounds, and
# < τ > over nothing has one round, the τ of < τ > = ( τ ) { τ }. A choice between
# alternatives is never removable, even between empty ones: over nothing, ( ε | A )
# with a nullable A has two trees, one per alternative.
def minRounds(kind: Bracket) -> Nat:
  match kind:
    case Group{}:
      1n
    case Optional{}:
      0n
    case Closure{}:
      0n
    case Positive{}:
      1n

# The rule on empty rounds, for a bracket of this kind with these rounds: at least the
# minimum number of rounds, and an empty round only when there are exactly that many. So
# the one pick of a [ τ ] consumes; the rounds of a { τ } all consume; and the rounds of
# a < τ > all consume, or there is just one.
def roundsOk(+kind: Bracket, +rounds: +List<Tree>) -> Bool:
  +n = List.length(&2, Tree, rounds)
  +least = minRounds(kind)
  Bool.and(Bool.not(Nat.is_lt(n, least)), Bool.or(allConsume(rounds), Nat.is_eq(n, least)))

# n copies of the same item. Each round of a loop matches the bracket once, as a group,
# so a loop with n rounds fits n copies of ( τ ).
def times(n: Nat, +item: Item) -> +List<Item>:
  match n:
    case 0n:
      []
    case 1n+m:
      item <> times(m, item)

# Does the forest fit the items, one tree per item? This is the heart of the
# specification: a parse tree of the input is a tree that fits the start symbol and
# spells the input. A leaf fits a terminal of its kind; a node fits a nonterminal
# through one of its productions; a pick fits ( τ ) or [ τ ] when its children fit the
# chosen alternative; a skip fits ε and [ τ ]; a loop fits { τ } and < τ > when each
# round fits ( τ ); and no pick or loop has a removable empty round (roundsOk).
def fits(forest: +List<Tree>, +grammar: +List<Production>, items: +List<Item>) -> Bool:
  match forest items:
    case Nil{} Nil{}:
      True{}
    case Con{Leaf{kind}, ts} Con{Sym{Terminal{k}}, rest}:
      Bool.and(Nat.is_eq(kind, k), fits(ts, grammar, rest))
    case Con{Node{+index, children}, ts} Con{Sym{Nonterminal{id}}, rest}:
      Bool.and(Bool.and(lhsIs(grammar, index, id), fits(children, grammar, rhsOf(grammar, index))), fits(ts, grammar, rest))
    case Con{Pick{+a, children}, ts} Con{Brack{Group{}, +alts}, rest}:
      Bool.and(Bool.and(isAlt(alts, a), fits(children, grammar, altOf(alts, a))), fits(ts, grammar, rest))
    case Con{Pick{+a, +children}, ts} Con{Brack{Optional{}, +alts}, rest}:
      Bool.and(Bool.and(Bool.and(roundsOk(Optional{}, [Pick{a, children}]), isAlt(alts, a)), fits(children, grammar, altOf(alts, a))), fits(ts, grammar, rest))
    case Con{Skip{}, ts} Con{Eps{}, rest}:
      fits(ts, grammar, rest)
    case Con{Skip{}, ts} Con{Brack{Optional{}, alts}, rest}:
      fits(ts, grammar, rest)
    case Con{Loop{+rounds}, ts} Con{Brack{Closure{}, +alts}, rest}:
      Bool.and(Bool.and(roundsOk(Closure{}, rounds), fits(rounds, grammar, times(List.length(&2, Tree, rounds), Brack{Group{}, alts}))), fits(ts, grammar, rest))
    case Con{Loop{+rounds}, ts} Con{Brack{Positive{}, +alts}, rest}:
      Bool.and(Bool.and(roundsOk(Positive{}, rounds), fits(rounds, grammar, times(List.length(&2, Tree, rounds), Brack{Group{}, alts}))), fits(ts, grammar, rest))
    case _ _:
      False{}

# The items derive the input when some forest fits them and spells the input. This is
# the language of a sequence of items; the rewriting laws in LAWS.bend show that it
# agrees with the usual BNF rewritings.
def Derives(+grammar: +List<Production>, +items: +List<Item>, +inputTokens: +List<Nat>) -> Type:
  &forest: +List<Tree> -> {fits(forest, grammar, items) == True{} : Bool} & {leaves(forest) == inputTokens : +List<Nat>}

# BINARY SUBTREE SETS.
#
# A slot is a position in a production's right side: `path` leads through nested
# brackets to a dot. [d] is the dot after d items of the right side; [m, a, d] is the
# dot after d items of alternative a of the bracket at item m; and so on, deeper.
type Slot is Data:
  Slot{index: Nat, path: +List<Nat>}

# One element of a binary subtree set: one step of a parse tree. The slot names a
# position in a right side. i is where the sequence of that slot starts, k is where its
# item just before the slot starts (the pivot), and j is where that item ends. So the
# element says: from its start up to this slot, the sequence reads the input from i to
# j, and its last item reads the part from k to j.
type Bsr is Data:
  Bsr{slot: Slot, i: Nat, k: Nat, j: Nat}

# Are two paths equal? Slots are compared by their production number and their path.
def pathEq(xs: +List<Nat>, ys: +List<Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Nat.is_eq(x, y), pathEq(xr, yr))
    case _ _:
      False{}

# Is the element in the set? Two elements are equal when their slots and their three
# positions are.
def bsrMember(+element: Bsr, set: +List<Bsr>) -> Bool:
  match element set:
    case _ Nil{}:
      False{}
    case Bsr{Slot{+p, +path}, +i, +k, +j} Con{Bsr{Slot{p2, path2}, i2, k2, j2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(p, p2), Bool.and(pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), bsrMember(Bsr{Slot{p, path}, i, k, j}, rest))

# The element for the slot after `dot` items of the sequence at (index, prefix), with
# positions i, k and j.
def at(+index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bsr:
  Bsr{Slot{index, List.append(&2, Nat, prefix, [dot])}, i, k, j}

# The step of an empty sequence: its slot is dot 0, and it reads nothing, so k = j. Only
# an empty sequence has it; a sequence with items records one step per item instead.
def emptyStep(dot: Nat, +index: Nat, +prefix: +List<Nat>, +i: Nat, +k: Nat) -> +List<Bsr>:
  match dot:
    case 0n:
      [at(index, prefix, 0n, i, k, k)]
    case 1n+d:
      []

# The steps of a forest, with Swift Apus's conventions:
# - in a sequence (rounds = False), child number `dot` + 1 completes the slot after it,
#   from the sequence start i, with pivot at its own start; every child does, the
#   first one too, an ε item too (as a skip); an empty sequence has one ε step;
# - a nonterminal, a ( ) or a [ ] starts a sequence of its own at its start, like an
#   anonymous nonterminal;
# - the rounds of a loop (rounds = True) each run the body from the loop's start, so
#   later rounds chain on to earlier ones, as in Scott and Johnstone's closures.
# A loop is written { ( τ ) }, as Swift Apus builds it: its one alternative is a group.
# Each round is then one item, whose step (the round's link step) records the loop's
# start, the round's start and its end, and the group's own sequence starts where the
# round starts. So every round's span is in the set. (A loop written { τ } with several
# items in an alternative still has parse trees and steps; only its rounds' starts are
# then in no step.)
def walk(forest: +List<Tree>, rounds: Bool, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match forest rounds:
    case Nil{} False{}:
      emptyStep(dot, index, prefix, i, k)
    case Con{Leaf{kind}, +ts} False{}:
      at(index, prefix, 1n+dot, i, k, 1n+k) <> walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k)
    case Con{Node{+q, +children}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      at(index, prefix, 1n+dot, i, k, end) <> List.append(&2, Bsr, walk(children, False{}, q, [], 0n, k, k), walk(ts, False{}, index, prefix, 1n+dot, i, end))
    case Con{Pick{+a, +children}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      at(index, prefix, 1n+dot, i, k, end) <> List.append(&2, Bsr, walk(children, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), walk(ts, False{}, index, prefix, 1n+dot, i, end))
    case Con{Skip{}, +ts} False{}:
      at(index, prefix, 1n+dot, i, k, k) <> walk(ts, False{}, index, prefix, 1n+dot, i, k)
    case Con{Loop{+rs}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(rs)))
      at(index, prefix, 1n+dot, i, k, end) <> List.append(&2, Bsr, walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), walk(ts, False{}, index, prefix, 1n+dot, i, end))
    case Nil{} True{}:
      []
    case Con{Pick{+a, +children}, +ts} True{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      List.append(&2, Bsr, walk(children, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), walk(ts, True{}, index, prefix, 0n, i, end))
    case Con{other, ts} True{}:
      []

# All steps of a tree that starts at position i. Only a node has steps of its own: a
# parse tree of a nonterminal is a node.
def steps(tree: Tree, +i: Nat) -> +List<Bsr>:
  match tree:
    case Node{+index, +children}:
      walk(children, False{}, index, [], 0n, i, i)
    case _:
      []

# Is every element of xs in the set?
def allIn(xs: +List<Bsr>, +set: +List<Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(bsrMember(x, set), allIn(rest, set))

# Do the two lists hold the same elements, in any order and with any repeats?
def sameSet(+xs: +List<Bsr>, +ys: +List<Bsr>) -> Bool:
  Bool.and(allIn(xs, ys), allIn(ys, xs))

# EXACT BSR SETS: what every parser must produce, for any EBNF grammar. As for BNF:
# a set is the exact BSR set of an input when it holds exactly the steps of the parse
# trees of the input. Every element is a step of some parse tree (no dead wood), and
# no step of a parse tree is missing. The set is a list read only by membership: its
# order means nothing, and an element listed twice says nothing more. A step shared by
# several trees is one element; the set does not count trees.

# No dead wood: every element of the set is a step of some parse tree of the input. A
# parser whose set has this property never offers an oracle a step that leads nowhere.
def OnlyParseSteps(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @element: Bsr -> {bsrMember(element, set) == True{} : Bool} ->
    &tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} & {leaves([tree]) == inputTokens : +List<Nat>} & {bsrMember(element, steps(tree, 0n)) == True{} : Bool}

# Nothing missing: every step of every parse tree of the input is in the set. A parser
# whose set has this property never hides a reading from an oracle.
def EveryParseStep(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> @element: Bsr ->
    {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} -> {bsrMember(element, steps(tree, 0n)) == True{} : Bool} ->
    {bsrMember(element, set) == True{} : Bool}

# The exact BSR set of an input: no dead wood, and nothing missing. `gll_bsr_exact` in
# LAWS.bend says the exact parser's set is one.
def IsExactBsr(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  OnlyParseSteps(grammar, start, inputTokens, set) & EveryParseStep(grammar, start, inputTokens, set)

# DISAMBIGUATION IN THREE PHASES. A grammar's annotations choose among its parse trees;
# they never add one. This is a disambiguation filter in the sense of Klint and Visser
# (1994): it maps the parse trees of an input to a subset of them. The filter works in
# three phases, each on what the one before it left:
#
#   1. ADMISSIBLE (lookahead, @left, @right): hard rules on single nodes. A node that
#      breaks one is out. AdmissibleTree, EmbedsAdmissible.
#   2. UNBEATEN (@prefer, @avoid): among the admissible trees, none of whose nodes is
#      outranked by an admissible rival. UnbeatenTree, SomeUnbeaten, EmbedsUnbeaten.
#   3. SELECTED (@longest, @shortest): among the admissible, unbeaten trees, the ones
#      no sequence of which has a better reading of its marked items. ExtentBestTree,
#      EmbedsExtentBest, and Selected for all three phases together.
#
# Each phase has its own oracle and its own laws in LAWS.bend; the final answer is the
# selected trees. The phases are joined: phase 2's rivals must be admissible, and phase
# 3's rivals admissible and unbeaten, so each phase chooses among what the earlier ones
# keep.

# PHASE 1, ADMISSIBLE TREES: LOOKAHEAD (>?>, >!>), @left AND @right.
#
# These annotations are hard rules on single nodes, not rankings between siblings: a node
# that breaks one is out, whether or not a sibling could take its place. So they come
# first. A parse tree is admissible when every node, pick and round keeps the rules of the
# alternative it chose. The rules don't depend on each other, so the order in which they
# are checked doesn't matter.
#
# A rule looks at more than the node's own tokens. A lookahead looks into the rest of
# the input, from where the node starts. @left and @right look at what
# the annotated alternative, or a listed nonterminal, could derive. So the walk carries
# the tokens that follow the forest, up to the end of the input.

# One rule. N... is a list of nonterminals. Ahead{N...}: every N derives some prefix of
# the input from where the alternative starts; Swift Apus's >?>( N ) is Ahead{[N]}, and
# several are written as several >?>. NotAhead{N...}: no N does; >!>( N, ... ).
# LeftAssoc{[]} is a bare @left: the
# alternative may not have, as its last child, something the alternative itself derives.
# A tree that reads a + b + c as a + (b + c) under E ::= @left E "+" E is out, because
# its last child, b + c, is again E "+" E. LeftAssoc{N...} is @left(N...): the last child may not
# spell tokens that some listed N derives. RightAssoc is the same for the first child.
#
# Three things to note. (1) This is about the language, not about the tree's shape. The
# last child is out when the alternative can derive its tokens, even if the child itself
# took another path, for example through a unit chain like postfixExpression ->
# functionCallExpression. (2) So @left is stricter than a check on the shape: under
# E ::= @left E "+" E | E "+" F | number, it also removes a tree whose last child is an
# E that went through E "+" F, because E "+" E can derive those tokens as well. (3) Ahead
# means the language: N derives a prefix, whether or not GLL predicted N there. Swift
# Apus asks the parse itself: it probes N wherever the rule is asked, so it means the
# same; the comparison with Swift checks this (BendCheck, "unpredicted target").
#
# On the names. The literature calls Ahead and NotAhead positive and negative lookahead
# (the and- and not-predicates of PEG, Ford 2004; ANTLR's syntactic predicates). Apus
# writes them >?>( N ) and >!>( N, ... ), at the start of an alternative; its token
# lookaround >+>( ... ) and >->( ... ) is the case where every N derives just single
# tokens. The two notations stay apart because a predicate is a parse and a lookaround
# tests one token.
type Guard is Data:
  Ahead{ids: +List<Nat>}
  NotAhead{ids: +List<Nat>}
  LeftAssoc{ids: +List<Nat>}
  RightAssoc{ids: +List<Nat>}

# Where a rule sits, as in Mark. ProdGuard: on production `index`. AltGuard: on
# alternative `alt` of the bracket at (index, path). An alternative may have any number
# of rules, and all of them must hold, unlike ranks, where the first one counts.
type GuardMark is Data:
  ProdGuard{index: Nat, guard: Guard}
  AltGuard{index: Nat, path: +List<Nat>, alt: Nat, guard: Guard}

# The rule in front of the others, when it applies.
def consIf(hit: Bool, g: Guard, +rest: +List<Guard>) -> +List<Guard>:
  match hit:
    case True{}:
      g <> rest
    case False{}:
      rest

# The rules on production q, in order.
def prodGuards(marks: +List<GuardMark>, +q: Nat) -> +List<Guard>:
  match marks:
    case Nil{}:
      []
    case Con{ProdGuard{p, g}, rest}:
      consIf(Nat.is_eq(p, q), g, prodGuards(rest, q))
    case Con{AltGuard{p, bp, b, g}, rest}:
      prodGuards(rest, q)

# The rules on alternative a of the bracket at (index, path), in order.
def altGuards(marks: +List<GuardMark>, +index: Nat, +path: +List<Nat>, +a: Nat) -> +List<Guard>:
  match marks:
    case Nil{}:
      []
    case Con{ProdGuard{p, g}, rest}:
      altGuards(rest, index, path, a)
    case Con{AltGuard{p, bp, b, g}, rest}:
      consIf(Bool.and(Nat.is_eq(p, index), Bool.and(pathEq(bp, path), Nat.is_eq(b, a))), g, altGuards(rest, index, path, a))

# Nonterminal x is ahead: it derives some prefix of the tokens from here on.
def DerivesAhead(+grammar: +List<Production>, +x: Nat, +ahead: +List<Nat>) -> Type:
  &pre: +List<Nat> -> &post: +List<Nat> -> {List.append(&2, Nat, pre, post) == ahead : +List<Nat>} & Derives(grammar, [Sym{Nonterminal{x}}], pre)

# Each of the nonterminals is ahead.
def AllAhead(+grammar: +List<Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, rest}:
      DerivesAhead(grammar, x, ahead) & AllAhead(grammar, rest, ahead)

# None of the nonterminals is ahead.
def NoneAhead(+grammar: +List<Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, rest}:
      (DerivesAhead(grammar, x, ahead) -> Empty) & NoneAhead(grammar, rest, ahead)

# None of the nonterminals derives exactly these tokens.
def NoneDerive(+grammar: +List<Production>, xs: +List<Nat>, +w: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, rest}:
      (Derives(grammar, [Sym{Nonterminal{x}}], w) -> Empty) & NoneDerive(grammar, rest, w)

# The tokens of the first and of the last child, when there are children.
def firstSpell(children: +List<Tree>) -> Maybe<&2, +List<Nat>>:
  match children:
    case Nil{}:
      None{}
    case Con{+t, ts}:
      Some{leaves([t])}

def lastOf(ts: +List<Tree>, +t: Tree) -> Tree:
  match ts:
    case Nil{}:
      t
    case Con{+u, us}:
      lastOf(us, u)

def lastSpell(children: +List<Tree>) -> Maybe<&2, +List<Nat>>:
  match children:
    case Nil{}:
      None{}
    case Con{+t, ts}:
      Some{leaves([lastOf(ts, t)])}

# The items don't derive these tokens.
def NotDerives(+grammar: +List<Production>, +items: +List<Item>, +w: +List<Nat>) -> Type:
  Derives(grammar, items, w) -> Empty

# The child at the edge spells w. Bare (no nonterminals listed): the alternative's own
# items must not derive w. With a list: no listed nonterminal may.
def EdgeOk(+grammar: +List<Production>, ids: +List<Nat>, +items: +List<Item>, +w: +List<Nat>) -> Type:
  match ids:
    case Nil{}:
      NotDerives(grammar, items, w)
    case Con{x, rest}:
      NoneDerive(grammar, {x <> rest : +List<Nat>}, w)

# The child at the edge, which spells `edge`, is allowed (EdgeOk). Without children
# there is nothing to check.
def EdgeFree(+grammar: +List<Production>, +ids: +List<Nat>, +items: +List<Item>, edge: Maybe<&2, +List<Nat>>) -> Type:
  match edge:
    case None{}:
      Unit
    case Some{w}:
      EdgeOk(grammar, ids, items, w)

# One rule holds for a node, pick or round: it chose the alternative `items`, its
# children are `children`, and `ahead` are the tokens from where it starts to the end of
# the input.
def Holds(+grammar: +List<Production>, guard: Guard, +items: +List<Item>, +children: +List<Tree>, +ahead: +List<Nat>) -> Type:
  match guard:
    case Ahead{ids}:
      AllAhead(grammar, ids, ahead)
    case NotAhead{ids}:
      NoneAhead(grammar, ids, ahead)
    case LeftAssoc{ids}:
      EdgeFree(grammar, ids, items, lastSpell(children))
    case RightAssoc{ids}:
      EdgeFree(grammar, ids, items, firstSpell(children))

# Every rule in the list holds.
def AllHold(+grammar: +List<Production>, guards: +List<Guard>, +items: +List<Item>, +children: +List<Tree>, +ahead: +List<Nat>) -> Type:
  match guards:
    case Nil{}:
      Unit
    case Con{g, rest}:
      Holds(grammar, g, items, children, ahead) & AllHold(grammar, rest, items, children, ahead)

# Every node, pick and round of the forest keeps its rules. The walk is the same as in
# Unbeaten: the forest fits the items from the dot on in the sequence at (index, prefix).
# `after` are the tokens that follow the whole forest, up to the end of the input. So a
# tree t in front of ts starts with leaves(t), then leaves(ts), then `after`, and its
# children are followed by leaves(ts) and `after`.
def Admissible(+grammar: +List<Production>, +guards: +List<GuardMark>, forest: +List<Tree>, items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +after: +List<Nat>) -> Type:
  match forest items:
    case Con{Node{+q, +children}, +ts} Con{Sym{Nonterminal{x}}, +rest}:
      +next = List.append(&2, Nat, leaves(ts), after)
      +ahead = List.append(&2, Nat, leaves(children), next)
      AllHold(grammar, prodGuards(guards, q), rhsOf(grammar, q), children, ahead) & Admissible(grammar, guards, children, rhsOf(grammar, q), q, [], 0n, next) & Admissible(grammar, guards, ts, rest, index, prefix, 1n+dot, after)
    case Con{Pick{+a, +children}, +ts} Con{Brack{kind, +alts}, +rest}:
      +next = List.append(&2, Nat, leaves(ts), after)
      +ahead = List.append(&2, Nat, leaves(children), next)
      +path = List.append(&2, Nat, prefix, [dot])
      AllHold(grammar, altGuards(guards, index, path, a), altOf(alts, a), children, ahead) & Admissible(grammar, guards, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, next) & Admissible(grammar, guards, ts, rest, index, prefix, 1n+dot, after)
    case Con{Loop{+rounds}, +ts} Con{Brack{kind, +alts}, +rest}:
      RoundsAdmissible(grammar, guards, rounds, alts, index, List.append(&2, Nat, prefix, [dot]), List.append(&2, Nat, leaves(ts), after)) & Admissible(grammar, guards, ts, rest, index, prefix, 1n+dot, after)
    case Con{t, +ts} Con{it, +rest}:
      Admissible(grammar, guards, ts, rest, index, prefix, 1n+dot, after)
    case _ _:
      Unit

# The rounds of a loop, each a pick of an alternative of the bracket at (index, path).
# `after` are the tokens that follow the whole loop. A round is followed by the rounds
# after it, and then `after`.
def RoundsAdmissible(+grammar: +List<Production>, +guards: +List<GuardMark>, rounds: +List<Tree>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +after: +List<Nat>) -> Type:
  match rounds:
    case Nil{}:
      Unit
    case Con{Pick{+a, +children}, +rest}:
      +next = List.append(&2, Nat, leaves(rest), after)
      +ahead = List.append(&2, Nat, leaves(children), next)
      AllHold(grammar, altGuards(guards, index, path, a), altOf(alts, a), children, ahead) & Admissible(grammar, guards, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, next) & RoundsAdmissible(grammar, guards, rest, alts, index, path, after)
    case Con{other, +rest}:
      RoundsAdmissible(grammar, guards, rest, alts, index, path, after)

# An admissible tree: a parse tree of the input whose every node keeps its rules.
def AdmissibleTree(+grammar: +List<Production>, +guards: +List<GuardMark>, +start: Nat, +inputTokens: +List<Nat>, +tree: Tree) -> Type:
  {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} & {leaves([tree]) == inputTokens : +List<Nat>} & Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [])

# A set that embeds exactly the admissible trees: a parse tree of the input uses only
# steps of the set when, and only when, it is admissible. As in phase 2, the set may hold
# steps that are in no admissible tree. There is no counterpart of SomeUnbeaten: a hard
# rule may leave no tree at all, and that is the grammar's doing, not the oracle's.
def EmbedsAdmissible(+grammar: +List<Production>, +guards: +List<GuardMark>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} ->
    ({allIn(steps(tree, 0n), set) == True{} : Bool} -> Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [])) &
    (Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, []) -> {allIn(steps(tree, 0n), set) == True{} : Bool})

# PHASE 2, UNBEATEN TREES: @prefer AND @avoid.
#
# A choice point is a nonterminal (its productions) or a bracket (its alternatives).
# Every alternative has a rank: @prefer is high, @avoid is low, unmarked is in between.
# A node that chose alternative x for the tokens it reads is outranked when a sibling of
# higher rank also derives exactly those tokens, admissibly: the sibling's own rules hold
# over those tokens and the tokens after them, and so do the rules of every node in the
# sibling's forest (phase 1). A rival that breaks a hard rule can't take the node's place,
# so it beats nothing. An unbeaten tree is a parse tree with no
# outranked node. The rival's own tree need not be unbeaten: grammars are context-free,
# so a subtree over the same tokens can always be swapped in. But it must not go round a
# cycle: it must not come back, over the same tokens, to this node's nonterminal or to a
# node above it that reads the same tokens. Such a rival only says "the same again", and
# counting it could leave no tree at all. Rivals are compared on
# tokens, not positions: should gates join the specification, they would add the tokens
# around the span (before and after), not positions in the input.

# The rank of an alternative: Avoided for @avoid, Plain without a mark, Preferred for
# @prefer. Alternatives of equal rank are not ranked against each other, so two
# Preferred siblings both stay.
type Rank is Data:
  Avoided{}
  Plain{}
  Preferred{}

# Ranks as numbers, to compare them: Avoided 0, Plain 1, Preferred 2.
def rankNat(r: Rank) -> Nat:
  match r:
    case Avoided{}:
      0n
    case Plain{}:
      1n
    case Preferred{}:
      2n

# Does rank a beat rank b? Only a strictly higher rank does.
def outranks(a: Rank, b: Rank) -> Bool:
  Nat.is_lt(rankNat(b), rankNat(a))

# The marks of a grammar, kept next to it. ProdMark: production `index` is marked.
# AltMark: alternative `alt` of the bracket at (index, path) is marked, where path is the
# path of the bracket's own item, as in a Slot ([m] for item m of the right side, [m, a, d]
# for item d of alternative a of the bracket at m, and so on). An alternative without a
# mark is Plain; with more than one, the first counts.
type Mark is Data:
  ProdMark{index: Nat, rank: Rank}
  AltMark{index: Nat, path: +List<Nat>, alt: Nat, rank: Rank}

# The rank that was found, or the given one when there is none.
def orRank(found: Maybe<&2, Rank>, +otherwise: Rank) -> Rank:
  match found:
    case Some{r}:
      r
    case None{}:
      otherwise

# The rank, when the mark applies.
def keepIf(hit: Bool, +r: Rank) -> Maybe<&2, Rank>:
  match hit:
    case True{}:
      Some{r}
    case False{}:
      None{}

# The rank this mark gives production q, when it marks q.
def prodMarkOf(m: Mark, +q: Nat) -> Maybe<&2, Rank>:
  match m:
    case ProdMark{index, +r}:
      keepIf(Nat.is_eq(index, q), r)
    case AltMark{index, path, alt, r}:
      None{}

# The rank this mark gives alternative a of the bracket at (index, path), when it marks
# that alternative.
def altMarkOf(m: Mark, +index: Nat, +path: +List<Nat>, +a: Nat) -> Maybe<&2, Rank>:
  match m:
    case ProdMark{q, r}:
      None{}
    case AltMark{p, bp, b, +r}:
      keepIf(Bool.and(Nat.is_eq(p, index), Bool.and(pathEq(bp, path), Nat.is_eq(b, a))), r)

# The rank of production q: from the first mark for it, and Plain without one.
def prodRank(marks: +List<Mark>, +q: Nat) -> Rank:
  match marks:
    case Nil{}:
      Plain{}
    case Con{m, rest}:
      orRank(prodMarkOf(m, q), prodRank(rest, q))

# The rank of alternative a of the bracket at (index, path): from the first mark for it,
# and Plain without one.
def altRank(marks: +List<Mark>, +index: Nat, +path: +List<Nat>, +a: Nat) -> Rank:
  match marks:
    case Nil{}:
      Plain{}
    case Con{m, rest}:
      orRank(altMarkOf(m, index, path, a), altRank(rest, index, path, a))

# The nonterminal of production number `index`. Only asked for productions that exist.
def lhsOf(+grammar: +List<Production>, index: Nat) -> Nat:
  match grammar index:
    case Nil{} _:
      0n
    case Con{Production{lhs, rhs}, rest} 0n:
      lhs
    case Con{p, rest} 1n+i:
      lhsOf(rest, i)

# Is production q a production of one of the nonterminals xs?
def lhsAmong(+grammar: +List<Production>, +q: Nat, xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(lhsIs(grammar, q, x), lhsAmong(grammar, q, rest))

# Does some node in the forest, at any depth, expand one of the nonterminals xs over
# exactly these tokens? A rival with such a node goes round a cycle back to where it
# started.
def revisits(+grammar: +List<Production>, forest: +List<Tree>, +xs: +List<Nat>, +tokens: +List<Nat>) -> Bool:
  match forest:
    case Nil{}:
      False{}
    case Con{Node{+q, +children}, ts}:
      Bool.or(Bool.or(Bool.and(lhsAmong(grammar, q, xs), pathEq(leaves(children), tokens)), revisits(grammar, children, xs, tokens)), revisits(grammar, ts, xs, tokens))
    case Con{Pick{a, children}, ts}:
      Bool.or(revisits(grammar, children, xs, tokens), revisits(grammar, ts, xs, tokens))
    case Con{Loop{rounds}, ts}:
      Bool.or(revisits(grammar, rounds, xs, tokens), revisits(grammar, ts, xs, tokens))
    case Con{Leaf{k}, ts}:
      revisits(grammar, ts, xs, tokens)
    case Con{Skip{}, ts}:
      revisits(grammar, ts, xs, tokens)

# The items, the sequence at (index, prefix) with the rules `own`, derive these tokens
# admissibly, followed by `after`, without a node of one of the nonterminals xs over the
# same tokens. Admissible because only an admissible forest could take a node's place:
# the rules of the sequence itself hold for the forest (AllHold), and so do those of every
# node, pick and round inside it (Admissible). The rules look at the tokens after the
# forest; they are the node's own `after`, since the rival reads the same tokens at the
# same place.
def DerivesOnce(+grammar: +List<Production>, +guards: +List<GuardMark>, +items: +List<Item>, +own: +List<Guard>, +index: Nat, +prefix: +List<Nat>, +tokens: +List<Nat>, +after: +List<Nat>, +xs: +List<Nat>) -> Type:
  &forest: +List<Tree> -> {fits(forest, grammar, items) == True{} : Bool} & {leaves(forest) == tokens : +List<Nat>} & {revisits(grammar, forest, xs, tokens) == False{} : Bool} & AllHold(grammar, own, items, forest, List.append(&2, Nat, tokens, after)) & Admissible(grammar, guards, forest, items, index, prefix, 0n, after)

# A rival of a node that used production q of nonterminal x: another production of x, of
# higher rank, whose right side derives the same tokens without going round a cycle. The
# nonterminals `xs` are the ones a cycle would come back to: x itself, and the nodes above
# this one that read the same tokens. A node with a rival is outranked: swapping in the
# rival's subtree gives a parse tree that made the preferred choice. A rival that can
# only derive the tokens by going round a cycle does not count: in A ::= @prefer A | a,
# the tree A -> a would otherwise lose to A -> A, which can only end in A -> a again,
# and no tree would be left.
def ProdRival(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +x: Nat, +q: Nat, +tokens: +List<Nat>, +after: +List<Nat>, +xs: +List<Nat>) -> Type:
  &q2: Nat -> {Bool.and(lhsIs(grammar, q2, x), outranks(prodRank(marks, q2), prodRank(marks, q))) == True{} : Bool} & DerivesOnce(grammar, guards, rhsOf(grammar, q2), prodGuards(guards, q2), q2, [], tokens, after, xs)

# A rival of a pick or a round that used alternative a of the bracket at (index, path):
# another alternative of that bracket, of higher rank, that derives the same tokens
# without going round a cycle back to one of the nonterminals `xs`. Those include the
# nonterminal of production `index`: a cycle back to this bracket passes through it.
def AltRival(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +a: Nat, +tokens: +List<Nat>, +after: +List<Nat>, +xs: +List<Nat>) -> Type:
  &a2: Nat -> {Bool.and(isAlt(alts, a2), outranks(altRank(marks, index, path, a2), altRank(marks, index, path, a))) == True{} : Bool} & DerivesOnce(grammar, guards, altOf(alts, a2), altGuards(guards, index, path, a2), index, List.append(&2, Nat, path, [a2]), tokens, after, xs)

# The nonterminals above a tree that read the same tokens as the tree: `above` are the
# ones above its parent, which read `span`; they still count when the tree reads `span`
# too, and not otherwise.
def keepAbove(same: Bool, +above: +List<Nat>) -> +List<Nat>:
  match same:
    case True{}:
      above
    case False{}:
      []

def sameAbove(+above: +List<Nat>, +span: +List<Nat>, +tokens: +List<Nat>) -> +List<Nat>:
  keepAbove(pathEq(tokens, span), above)

# No node of the forest is outranked. The forest fits the items from the dot on in the
# sequence at (index, prefix); walking both side by side tells which choice point every
# node, pick and loop belongs to. `above` are the nonterminals of the nodes above that
# read the tokens `span`, the tokens of the enclosing node or pick. A node is checked
# against the other productions of its nonterminal, a pick against the other
# alternatives of its bracket, and a loop round by round. Leaves and skips make no
# choice. `after` are the tokens after the forest, as in Admissible: a rival's rules
# look at them.
def Unbeaten(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, forest: +List<Tree>, items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match forest items:
    case Con{Node{+q, +children}, +ts} Con{Sym{Nonterminal{+x}}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(ts), after)
      +xs = {x <> sameAbove(above, span, w) : +List<Nat>}
      (ProdRival(grammar, guards, marks, x, q, w, next, xs) -> Empty) & Unbeaten(grammar, guards, marks, children, rhsOf(grammar, q), q, [], 0n, xs, w, next) & Unbeaten(grammar, guards, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{Pick{+a, +children}, +ts} Con{Brack{kind, +alts}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(ts), after)
      +same = sameAbove(above, span, w)
      +path = List.append(&2, Nat, prefix, [dot])
      (AltRival(grammar, guards, marks, alts, index, path, a, w, next, {lhsOf(grammar, index) <> same : +List<Nat>}) -> Empty) & Unbeaten(grammar, guards, marks, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, same, w, next) & Unbeaten(grammar, guards, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{Loop{+rounds}, +ts} Con{Brack{kind, +alts}, +rest}:
      RoundsUnbeaten(grammar, guards, marks, rounds, alts, index, List.append(&2, Nat, prefix, [dot]), above, span, List.append(&2, Nat, leaves(ts), after)) & Unbeaten(grammar, guards, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{t, +ts} Con{it, +rest}:
      Unbeaten(grammar, guards, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case _ _:
      Unit

# The rounds of a loop. Each round is a pick of an alternative of the bracket at
# (index, path), and is checked on its own against the other alternatives.
def RoundsUnbeaten(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, rounds: +List<Tree>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match rounds:
    case Nil{}:
      Unit
    case Con{Pick{+a, +children}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(rest), after)
      +same = sameAbove(above, span, w)
      (AltRival(grammar, guards, marks, alts, index, path, a, w, next, {lhsOf(grammar, index) <> same : +List<Nat>}) -> Empty) & Unbeaten(grammar, guards, marks, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, same, w, next) & RoundsUnbeaten(grammar, guards, marks, rest, alts, index, path, above, span, after)
    case Con{other, +rest}:
      RoundsUnbeaten(grammar, guards, marks, rest, alts, index, path, above, span, after)

# An unbeaten tree: an admissible tree with no outranked node. These are the trees that
# @prefer and @avoid keep, among the admissible ones. Without marks, every admissible tree
# is unbeaten; without rules, every parse tree is admissible.
def UnbeatenTree(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +start: Nat, +inputTokens: +List<Nat>, +tree: Tree) -> Type:
  AdmissibleTree(grammar, guards, start, inputTokens, tree) & Unbeaten(grammar, guards, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], [])

# Some parse tree of the input is unbeaten: the preferences leave a reading.
def SomeUnbeaten(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +start: Nat, +inputTokens: +List<Nat>) -> Type:
  &tree: Tree -> UnbeatenTree(grammar, guards, marks, start, inputTokens, tree)

# A set that embeds exactly the unbeaten trees: a parse tree of the input uses only steps
# of the set when, and only when, it is admissible and no node of it is outranked. The
# set may also hold steps that are in no unbeaten tree; they make no tree of their own,
# so an oracle that keeps them still chooses among the unbeaten trees, and only those.
def EmbedsUnbeaten(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} ->
    ({allIn(steps(tree, 0n), set) == True{} : Bool} -> Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, []) & Unbeaten(grammar, guards, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], [])) &
    (Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, []) & Unbeaten(grammar, guards, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {allIn(steps(tree, 0n), set) == True{} : Bool})

# PHASE 3, SELECTED TREES: @longest AND @shortest.
#
# An extent mark asks for the longest or shortest reading of an item: of every node of a
# nonterminal (`@longest X = ...`), or of one bracket (`@longest { word }`). It is local,
# like @prefer: it compares the readings of one sequence over the same tokens, the
# children of one node, pick or round. A sequence's forest is out when another forest
# fits the same items, spells the same tokens, and reads its marked items better: longer
# for @longest, shorter for @shortest. With several marked items in one sequence, the
# first one decides, then the next, and so on (left to right, as Swift Apus's bracket
# extent does). Some forest always reads them best, so @longest and @shortest never remove
# every reading of a sequence. A forest can only be swapped for another over the same
# tokens, so a node's marked items are compared within the node, never across trees.
#
# Joined to phases 1 and 2: only a better forest that could take the sequence's place
# counts. It must keep the hard rules (the sequence's own, over its tokens and the tokens
# after them, and those of every node, pick and round inside it) and have no outranked
# node itself, in the same context as the forest it would replace (the tokens after it,
# and the nodes above it over the same tokens). A better reading that breaks a rule, or
# makes a choice @prefer or @avoid rules out, beats nothing.

type Extent is Data:
  Longest{}
  Shortest{}

# Where an extent mark sits. NtExtent: on every node of nonterminal x. BrackExtent: on the
# bracket item at (index, path), with path as in Mark: [m] for item m of the right side of
# production `index`, [m, a, d] for item d of alternative a of the bracket at m, and so on.
type ExtentMark is Data:
  NtExtent{x: Nat, ext: Extent}
  BrackExtent{index: Nat, path: +List<Nat>, ext: Extent}

def extentIf(hit: Bool, +e: Extent) -> Maybe<&2, Extent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      None{}

def orExtent(found: Maybe<&2, Extent>, +otherwise: Maybe<&2, Extent>) -> Maybe<&2, Extent>:
  match found:
    case Some{e}:
      Some{e}
    case None{}:
      otherwise

# The extent asked of nonterminal x, from the first mark for it.
def ntExtent(marks: +List<ExtentMark>, +x: Nat) -> Maybe<&2, Extent>:
  match marks:
    case Nil{}:
      None{}
    case Con{NtExtent{y, +e}, rest}:
      orExtent(extentIf(Nat.is_eq(y, x), e), ntExtent(rest, x))
    case Con{BrackExtent{p, bp, e}, rest}:
      ntExtent(rest, x)

# The extent asked of the bracket item at (index, path), from the first mark for it.
def brackExtent(marks: +List<ExtentMark>, +index: Nat, +path: +List<Nat>) -> Maybe<&2, Extent>:
  match marks:
    case Nil{}:
      None{}
    case Con{NtExtent{y, e}, rest}:
      brackExtent(rest, index, path)
    case Con{BrackExtent{p, bp, +e}, rest}:
      orExtent(extentIf(Bool.and(Nat.is_eq(p, index), pathEq(bp, path)), e), brackExtent(rest, index, path))

# The extent asked of an item at (index, path); terminals and ε have none.
def itemExtent(+marks: +List<ExtentMark>, item: Item, +index: Nat, +path: +List<Nat>) -> Maybe<&2, Extent>:
  match item:
    case Sym{Nonterminal{+x}}:
      ntExtent(marks, x)
    case Sym{Terminal{k}}:
      None{}
    case Brack{kind, alts}:
      brackExtent(marks, index, path)
    case Eps{}:
      None{}

# A marked item's reading: what is asked of it, and how many tokens it reads.
type Measure is Data:
  Measure{ext: Extent, len: Nat}

def measureIf(found: Maybe<&2, Extent>, +len: Nat, +rest: +List<Measure>) -> +List<Measure>:
  match found:
    case Some{+e}:
      Measure{e, len} <> rest
    case None{}:
      rest

# The readings of the marked items of the sequence at (index, prefix), from the dot on.
def measures(+marks: +List<ExtentMark>, forest: +List<Tree>, items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat) -> +List<Measure>:
  match forest items:
    case Con{+t, ts} Con{+it, rest}:
      measureIf(itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), List.length(&2, Nat, leaves([t])), measures(marks, ts, rest, index, prefix, 1n+dot))
    case _ _:
      []

# Does a reading of length a beat one of length b?
def better(e: Extent, +a: Nat, +b: Nat) -> Bool:
  match e:
    case Longest{}:
      Nat.is_lt(b, a)
    case Shortest{}:
      Nat.is_lt(a, b)

# Do the readings xs beat ys? The first marked item where they differ decides.
def beats(xs: +List<Measure>, ys: +List<Measure>) -> Bool:
  match xs ys:
    case Con{Measure{+e, +a}, xr} Con{Measure{e2, +b}, yr}:
      Bool.or(better(e, a, b), Bool.and(Nat.is_eq(a, b), beats(xr, yr)))
    case _ _:
      False{}

# A better reading of a sequence: another forest for the same items over the same tokens
# w, whose marked items beat those of f, and that phases 1 and 2 keep where f stands: the
# sequence's rules `own` hold for it, it is admissible, and no node of it is outranked,
# with `after` the tokens after it and `above`, `span` as in Unbeaten for f.
def ExtentRival(+grammar: +List<Production>, +guards: +List<GuardMark>, +pmarks: +List<Mark>, +marks: +List<ExtentMark>, +items: +List<Item>, +own: +List<Guard>, +index: Nat, +prefix: +List<Nat>, +w: +List<Nat>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +f: +List<Tree>) -> Type:
  &f2: +List<Tree> -> {fits(f2, grammar, items) == True{} : Bool} & {leaves(f2) == w : +List<Nat>} & {beats(measures(marks, f2, items, index, prefix, 0n), measures(marks, f, items, index, prefix, 0n)) == True{} : Bool} &
    AllHold(grammar, own, items, f2, List.append(&2, Nat, w, after)) & Admissible(grammar, guards, f2, items, index, prefix, 0n, after) & Unbeaten(grammar, guards, pmarks, f2, items, index, prefix, 0n, above, span, after)

# No sequence of the forest has a better reading. The walk is the one of Unbeaten: the
# children of every node, pick and round are checked against the other forests for their
# alternative over the same tokens, with the same `above`, `span` and `after`.
def ExtentBest(+grammar: +List<Production>, +guards: +List<GuardMark>, +pmarks: +List<Mark>, +marks: +List<ExtentMark>, forest: +List<Tree>, items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match forest items:
    case Con{Node{+q, +children}, +ts} Con{Sym{Nonterminal{+x}}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(ts), after)
      +xs = {x <> sameAbove(above, span, w) : +List<Nat>}
      (ExtentRival(grammar, guards, pmarks, marks, rhsOf(grammar, q), prodGuards(guards, q), q, [], w, next, xs, w, children) -> Empty) & ExtentBest(grammar, guards, pmarks, marks, children, rhsOf(grammar, q), q, [], 0n, xs, w, next) & ExtentBest(grammar, guards, pmarks, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{Pick{+a, +children}, +ts} Con{Brack{kind, +alts}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(ts), after)
      +same = sameAbove(above, span, w)
      +path = List.append(&2, Nat, prefix, [dot])
      +pre = List.append(&2, Nat, path, [a])
      (ExtentRival(grammar, guards, pmarks, marks, altOf(alts, a), altGuards(guards, index, path, a), index, pre, w, next, same, w, children) -> Empty) & ExtentBest(grammar, guards, pmarks, marks, children, altOf(alts, a), index, pre, 0n, same, w, next) & ExtentBest(grammar, guards, pmarks, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{Loop{+rounds}, +ts} Con{Brack{kind, +alts}, +rest}:
      RoundsBest(grammar, guards, pmarks, marks, rounds, alts, index, List.append(&2, Nat, prefix, [dot]), above, span, List.append(&2, Nat, leaves(ts), after)) & ExtentBest(grammar, guards, pmarks, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case Con{t, +ts} Con{it, +rest}:
      ExtentBest(grammar, guards, pmarks, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
    case _ _:
      Unit

# The rounds of a loop, each a pick of an alternative of the bracket at (index, path).
def RoundsBest(+grammar: +List<Production>, +guards: +List<GuardMark>, +pmarks: +List<Mark>, +marks: +List<ExtentMark>, rounds: +List<Tree>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match rounds:
    case Nil{}:
      Unit
    case Con{Pick{+a, +children}, +rest}:
      +w = leaves(children)
      +next = List.append(&2, Nat, leaves(rest), after)
      +same = sameAbove(above, span, w)
      +pre = List.append(&2, Nat, path, [a])
      (ExtentRival(grammar, guards, pmarks, marks, altOf(alts, a), altGuards(guards, index, path, a), index, pre, w, next, same, w, children) -> Empty) & ExtentBest(grammar, guards, pmarks, marks, children, altOf(alts, a), index, pre, 0n, same, w, next) & RoundsBest(grammar, guards, pmarks, marks, rest, alts, index, path, above, span, after)
    case Con{other, +rest}:
      RoundsBest(grammar, guards, pmarks, marks, rest, alts, index, path, above, span, after)

# An admissible, unbeaten tree with no sequence that has a better reading.
def ExtentBestTree(+grammar: +List<Production>, +guards: +List<GuardMark>, +pmarks: +List<Mark>, +marks: +List<ExtentMark>, +start: Nat, +inputTokens: +List<Nat>, +tree: Tree) -> Type:
  UnbeatenTree(grammar, guards, pmarks, start, inputTokens, tree) & ExtentBest(grammar, guards, pmarks, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], [])

# A set that embeds exactly the trees of phase 3, as in phases 1 and 2.
def EmbedsExtentBest(+grammar: +List<Production>, +guards: +List<GuardMark>, +pmarks: +List<Mark>, +marks: +List<ExtentMark>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} ->
    ({allIn(steps(tree, 0n), set) == True{} : Bool} -> Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, []) & Unbeaten(grammar, guards, pmarks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], []) & ExtentBest(grammar, guards, pmarks, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], [])) &
    (Admissible(grammar, guards, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, []) & Unbeaten(grammar, guards, pmarks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], []) & ExtentBest(grammar, guards, pmarks, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {allIn(steps(tree, 0n), set) == True{} : Bool})

# THE SELECTED TREES: the answer of all three phases. A selected tree is a parse tree of the
# input that is admissible, unbeaten and extent-best.
def Selected(+grammar: +List<Production>, +guards: +List<GuardMark>, +marks: +List<Mark>, +extents: +List<ExtentMark>, +start: Nat, +inputTokens: +List<Nat>, +tree: Tree) -> Type:
  ExtentBestTree(grammar, guards, marks, extents, start, inputTokens, tree)

# ======== DERIVED NOTIONS: NULLABLE, FIRST, FOLLOW, PREDICT AND LL(1) ========
#
# Defined from `Derives` and the steps of parse trees, and used only by the LL(1) laws in
# LAWS.bend. Nothing above depends on them. The engine's own tables (FIRST.bend) are an
# untrusted computation of over-approximations of these sets.

# The items can derive nothing.
def Nullable(+grammar: +List<Production>, +items: +List<Item>) -> Type:
  Derives(grammar, items, [])

# The items can derive something that begins with the token.
def First(+grammar: +List<Production>, +items: +List<Item>, +token: Nat) -> Type:
  &rest: +List<Nat> -> Derives(grammar, items, token <> rest)

# The item number m of a sequence, and alternative a of a bracket item.
def itemAt(items: +List<Item>, m: Nat) -> Maybe<&2, Item>:
  match items m:
    case Nil{} _:
      None{}
    case Con{x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+n:
      itemAt(rest, n)

def bracketAlternative(item: Maybe<&2, Item>, a: Nat) -> +List<Item>:
  match item:
    case Some{Brack{kind, alts}}:
      altOf(alts, a)
    case _:
      []

# The sequence named by a prefix, inside the items: [] is the items themselves, [m, a] the
# alternative a of the bracket at item m, [m, a, m2, a2] one level deeper, as in a slot's
# path without its final dot. A prefix of odd length names no sequence.
#
# WHY ODD PREFIXES ARE HERE AT ALL (a deliberate shortcut). Nothing builds an odd prefix:
# the walk, the engine and LL1.bend always add a whole (item, alternative) pair. They only
# show up because `LL1` says "for every ChoicePoint", and a ChoicePoint's prefix is a plain
# list of numbers, so the law also ranges over junk such as BracketAt{index, [2], dot}.
# Mapping an odd prefix to [] makes such a point have no choices, so LL(1) holds there
# trivially. (Before, the leftover number was ignored, which made [2] a copy of [] and cost
# the proof a detour.) The clean fix is a path type of whole pairs for ChoicePoint and
# Choice, with FollowAt flattening it for the steps' slot paths: about 50 lines of SPEC and
# a third of PROOF_LL1.bend. Doing it for slot paths and the engine too would reopen most
# proofs. Not worth it while no real path is ever odd.
def sequenceIn(prefix: +List<Nat>, items: +List<Item>) -> +List<Item>:
  match prefix:
    case Nil{}:
      items
    case Con{m, Nil{}}:
      []
    case Con{m, Con{a, rest}}:
      sequenceIn(rest, bracketAlternative(itemAt(items, m), a))

def sequenceAt(+grammar: +List<Production>, +index: Nat, prefix: +List<Nat>) -> +List<Item>:
  sequenceIn(prefix, rhsOf(grammar, index))

# The items of a sequence from the dot on.
def itemsFrom(n: Nat, items: +List<Item>) -> +List<Item>:
  match n items:
    case 0n _:
      items
    case 1n+m Nil{}:
      []
    case 1n+m Con{x, rest}:
      itemsFrom(m, rest)

# FOLLOW of a sequence: in a parse tree of some input, the step of the sequence's last slot
# records that it ended at j, and `next` is the token at j (None: the end of the input).
# FIRST looks only at the items; FOLLOW is about where the sequence stands: every place it
# occurs, and what follows those places, up to the start symbol. Read from parse trees,
# FOLLOW holds exactly what really comes next in some sentence. The textbook equations (FIRST
# of what follows each occurrence, FOLLOW of the owner when that can be empty) give a set
# that can be larger: they also count occurrences no sentence uses. FIRST.bend computes those
# equations; its tables contain this FOLLOW, so they predict safely.
def FollowAt(+grammar: +List<Production>, +start: Nat, +index: Nat, +prefix: +List<Nat>, +next: Maybe<&2, Nat>) -> Type:
  &input: +List<Nat> -> &tree: Tree -> &i: Nat -> &k: Nat -> &j: Nat ->
    {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} & {leaves([tree]) == input : +List<Nat>} &
    {bsrMember(at(index, prefix, List.length(&2, Item, sequenceAt(grammar, index, prefix)), i, k, j), steps(tree, 0n)) == True{} : Bool} &
    {List.get(&2, Nat, input, j) == next : Maybe<&2, Nat>}

def FirstOf(+grammar: +List<Production>, +items: +List<Item>, next: Maybe<&2, Nat>) -> Type:
  match next:
    case None{}:
      Empty
    case Some{+token}:
      First(grammar, items, token)

def PredictsBy(viaFirst: Bool, +grammar: +List<Production>, +start: Nat, +items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +next: Maybe<&2, Nat>) -> Type:
  match viaFirst:
    case True{}:
      FirstOf(grammar, items, next)
    case False{}:
      Nullable(grammar, items) & FollowAt(grammar, start, index, prefix, next)

# PREDICT: the items, followed by what can come after the sequence at (index, prefix), can
# begin with `next`: through FIRST, or the items derive nothing and FOLLOW has it.
def Predicts(+grammar: +List<Production>, +start: Nat, +items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +next: Maybe<&2, Nat>) -> Type:
  &viaFirst: Bool -> PredictsBy(viaFirst, grammar, start, items, index, prefix, next)

# A CHOICE POINT: a place where a parse tree makes a choice. A nonterminal, expanded by one
# of its alternates; the bracket item at the dot of the sequence at (index, prefix), entered
# by one of its alternates or, for [ ] and { }, left for the rest of its sequence (skipped,
# or its rounds stopped); and, for a < > only, the moment after one of its rounds, when it
# goes on with another round or is left.
#
# A choice may read nothing only where the bracket rule (`roundsOk`) allows an empty round:
# an alternate of a nonterminal, the one round of ( ), the first round of < > (which is then
# its only round), and leaving. The rounds of [ ] and { }, and the later rounds of < >,
# always read something, so those alternates are told apart by FIRST alone. (Scott and
# Johnstone's EBNF parsers keep every empty round, so there a nullable body of [ ] or { } is
# a real ambiguity; here such readings are no trees.) For { }, entering and going on are the
# same choice, so one choice point serves all its rounds; for < > they differ, since leaving
# is not allowed before the first round. A prefix of odd length names no place (see
# `sequenceIn`), so a choice point with one has no choices.
type ChoicePoint is Data:
  NonterminalAt{nonterminal: Nat}
  BracketAt{index: Nat, prefix: +List<Nat>, dot: Nat}
  AfterRoundAt{index: Nat, prefix: +List<Nat>, dot: Nat}

# One choice at a choice point: items, followed by the end of the sequence at (index,
# prefix), and whether it may read nothing.
type Choice is Data:
  Choice{items: +List<Item>, index: Nat, prefix: +List<Nat>, mayBeEmpty: Bool}

def leaveChoice(leave: Bool, +rest: +List<Item>, +index: Nat, +prefix: +List<Nat>) -> Maybe<&2, Choice>:
  match leave:
    case True{}:
      Some{Choice{rest, index, prefix, True{}}}
    case False{}:
      None{}

# The choices at a bracket: its alternates, numbered from 0 (as a tree's Pick numbers
# them), each possibly empty or not; then, if it can be left here, leaving it.
def bracketAlternate(isAlternate: Bool, +alts: +List<+List<Item>>, +choice: Nat, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +mayBeEmpty: Bool, +leave: Bool, +rest: +List<Item>) -> Maybe<&2, Choice>:
  match isAlternate:
    case True{}:
      Some{Choice{altOf(alts, choice), index, List.append(&2, Nat, prefix, [dot, choice]), mayBeEmpty}}
    case False{}:
      leaveChoice(Bool.and(Nat.is_eq(choice, List.length(&2, +List<Item>, alts)), leave), rest, index, prefix)

# Entering a bracket: ( ) and < > must take a round, which may be empty; [ ] and { } may be
# left, and their rounds read something.
def enterChoice(kind: Bracket, +alts: +List<+List<Item>>, +choice: Nat, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +rest: +List<Item>) -> Maybe<&2, Choice>:
  match kind:
    case Group{}:
      bracketAlternate(isAlt(alts, choice), alts, choice, index, prefix, dot, True{}, False{}, rest)
    case Optional{}:
      bracketAlternate(isAlt(alts, choice), alts, choice, index, prefix, dot, False{}, True{}, rest)
    case Closure{}:
      bracketAlternate(isAlt(alts, choice), alts, choice, index, prefix, dot, False{}, True{}, rest)
    case Positive{}:
      bracketAlternate(isAlt(alts, choice), alts, choice, index, prefix, dot, True{}, False{}, rest)

# After a round of < >: another round, which reads something, or leaving.
def afterRoundChoice(kind: Bracket, +alts: +List<+List<Item>>, +choice: Nat, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +rest: +List<Item>) -> Maybe<&2, Choice>:
  match kind:
    case Positive{}:
      bracketAlternate(isAlt(alts, choice), alts, choice, index, prefix, dot, False{}, True{}, rest)
    case _:
      None{}

def bracketChoice(item: Maybe<&2, Item>, +afterRound: Bool, +choice: Nat, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +rest: +List<Item>) -> Maybe<&2, Choice>:
  match item afterRound:
    case Some{Brack{+kind, +alts}} False{}:
      enterChoice(kind, alts, choice, index, prefix, dot, rest)
    case Some{Brack{+kind, +alts}} True{}:
      afterRoundChoice(kind, alts, choice, index, prefix, dot, rest)
    case _ _:
      None{}

def nonterminalAlternate(isOwn: Bool, +grammar: +List<Production>, +choice: Nat) -> Maybe<&2, Choice>:
  match isOwn:
    case True{}:
      Some{Choice{rhsOf(grammar, choice), choice, [], True{}}}
    case False{}:
      None{}

# Choice number `choice` at a choice point. A nonterminal's alternates are numbered by their
# production, since the grammar keeps each alternate of a nonterminal as a production of its
# own (and a tree's Node names it by that number); a bracket keeps its alternates inside the
# item, numbered from 0 (as a tree's Pick does), and the choice after them is leaving the
# bracket, where it can be left. None when there is no such choice.
def choiceOf(+grammar: +List<Production>, point: ChoicePoint, +choice: Nat) -> Maybe<&2, Choice>:
  match point:
    case NonterminalAt{+x}:
      nonterminalAlternate(lhsIs(grammar, choice, x), grammar, choice)
    case BracketAt{+index, +prefix, +dot}:
      +seq = sequenceAt(grammar, index, prefix)
      bracketChoice(itemAt(seq, dot), False{}, choice, index, prefix, dot, itemsFrom(1n+dot, seq))
    case AfterRoundAt{+index, +prefix, +dot}:
      +seq = sequenceAt(grammar, index, prefix)
      bracketChoice(itemAt(seq, dot), True{}, choice, index, prefix, dot, itemsFrom(1n+dot, seq))

# Can the choice begin with `next`? Through FIRST; or, when it may read nothing, its items
# derive nothing and FOLLOW of its sequence has `next`.
def predictsWhen(mayBeEmpty: Bool, +grammar: +List<Production>, +start: Nat, +items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +next: Maybe<&2, Nat>) -> Type:
  match mayBeEmpty:
    case True{}:
      Predicts(grammar, start, items, index, prefix, next)
    case False{}:
      FirstOf(grammar, items, next)

def ChoicePredicts(+grammar: +List<Production>, +start: Nat, choice: Maybe<&2, Choice>, +next: Maybe<&2, Nat>) -> Type:
  match choice:
    case None{}:
      Empty
    case Some{Choice{+items, +index, +prefix, +mayBeEmpty}}:
      predictsWhen(mayBeEmpty, grammar, start, items, index, prefix, next)

# LL(1) AT A CHOICE POINT: no two different choices can both begin with the same next token.
# This is strong LL(1): each choice's predict set uses FOLLOW of its own sequence, whatever
# the tree around it.
def LL1At(+grammar: +List<Production>, +start: Nat, +point: ChoicePoint) -> Type:
  @first: Nat -> @second: Nat -> @next: Maybe<&2, Nat> -> {Nat.is_eq(first, second) == False{} : Bool} ->
    ChoicePredicts(grammar, start, choiceOf(grammar, point, first), next) -> ChoicePredicts(grammar, start, choiceOf(grammar, point, second), next) -> Empty

# An LL(1) grammar: LL(1) at every choice point.
def LL1(+grammar: +List<Production>, +start: Nat) -> Type:
  @point: ChoicePoint -> LL1At(grammar, start, point)

# THE CHOICES A TREE MAKES: at which choice point, at which position, which choice. A node
# is its nonterminal's choice where it starts; a Pick of ( ) or [ ] is the bracket's choice
# where it starts, and a Skip of [ ] is leaving it there; each round of { } chooses at the
# bracket where the round starts, and stopping is leaving it where the loop ends; for < >,
# the first round chooses at the bracket, and every later round, and stopping, choose after
# the round before (AfterRoundAt). Used only by the law ll1_at.
type Made is Data:
  Made{point: ChoicePoint, pos: Nat, choice: Nat}

def nonterminalOf(item: Maybe<&2, Item>) -> Nat:
  match item:
    case Some{Sym{Nonterminal{x}}}:
      x
    case _:
      0n

def alternateCount(item: Maybe<&2, Item>) -> Nat:
  match item:
    case Some{Brack{kind, alts}}:
      List.length(&2, +List<Item>, alts)
    case _:
      0n

# A Skip leaves a [ ]; a Skip of an ε item makes no choice.
def skipMade(item: Maybe<&2, Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +k: Nat) -> +List<Made>:
  match item:
    case Some{Brack{kind, alts}}:
      [Made{BracketAt{index, prefix, dot}, k, List.length(&2, +List<Item>, alts)}]
    case _:
      []

# Where a round of a loop chooses: after the round before, for a later round of < >.
def roundPoint(later: Bool, item: Maybe<&2, Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat) -> ChoicePoint:
  match later item:
    case True{} Some{Brack{Positive{}, alts}}:
      AfterRoundAt{index, prefix, dot}
    case _ _:
      BracketAt{index, prefix, dot}

# The choices of a forest for the sequence at (index, prefix) from item dot, starting at k;
# with rounds = True, the rounds of the loop at item dot (later: a round came before).
def madeIn(+grammar: +List<Production>, forest: +List<Tree>, rounds: Bool, later: Bool, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +k: Nat) -> +List<Made>:
  match forest rounds:
    case Nil{} False{}:
      []
    case Con{Leaf{kind}, +ts} False{}:
      madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, 1n+k)
    case Con{Node{+q, +children}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      Made{NonterminalAt{nonterminalOf(itemAt(sequenceAt(grammar, index, prefix), dot))}, k, q} <>
        List.append(&2, Made, madeIn(grammar, children, False{}, False{}, q, [], 0n, k), madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, end))
    case Con{Pick{+a, +children}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      Made{BracketAt{index, prefix, dot}, k, a} <>
        List.append(&2, Made, madeIn(grammar, children, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, end))
    case Con{Skip{}, +ts} False{}:
      List.append(&2, Made, skipMade(itemAt(sequenceAt(grammar, index, prefix), dot), index, prefix, dot, k), madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, k))
    case Con{Loop{+rs}, +ts} False{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(rs)))
      List.append(&2, Made, madeIn(grammar, rs, True{}, False{}, index, prefix, dot, k), madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, end))
    case Nil{} True{}:
      +item = itemAt(sequenceAt(grammar, index, prefix), dot)
      [Made{roundPoint(later, item, index, prefix, dot), k, alternateCount(item)}]
    case Con{Pick{+a, +children}, +ts} True{}:
      +end = Nat.add(k, List.length(&2, Nat, leaves(children)))
      Made{roundPoint(later, itemAt(sequenceAt(grammar, index, prefix), dot), index, prefix, dot), k, a} <>
        List.append(&2, Made, madeIn(grammar, children, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), madeIn(grammar, ts, True{}, True{}, index, prefix, dot, end))
    case Con{other, ts} True{}:
      []

# The choices of a parse tree of the start symbol: its root node, and everything below.
def choicesMade(+grammar: +List<Production>, +start: Nat, tree: Tree) -> +List<Made>:
  match tree:
    case Node{+q, +children}:
      Made{NonterminalAt{start}, 0n, q} <> madeIn(grammar, children, False{}, False{}, q, [], 0n, 0n)
    case _:
      []

# x is one of xs.
def Among(+x: Made, xs: +List<Made>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{+y, rest}:
      Either<{x == y : Made}, Among(x, rest)>
