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

# PREFERENCES: @prefer AND @avoid. A grammar's annotations choose among its parse trees;
# they never add one. This is a disambiguation filter in the sense of Klint and Visser
# (1994): it maps the parse trees of an input to a subset of them.
#
# A choice point is a nonterminal (its productions) or a bracket (its alternatives).
# Every alternative has a rank: @prefer is high, @avoid is low, unmarked is in between.
# A node that chose alternative x for the tokens it reads is outranked when a sibling of
# higher rank also derives exactly those tokens. A selected tree is a parse tree with no
# outranked node. The rival's own tree need not be selected: grammars are context-free,
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

# The items derive these tokens without a node of one of the nonterminals xs over the
# same tokens.
def DerivesOnce(+grammar: +List<Production>, +items: +List<Item>, +tokens: +List<Nat>, +xs: +List<Nat>) -> Type:
  &forest: +List<Tree> -> {fits(forest, grammar, items) == True{} : Bool} & {leaves(forest) == tokens : +List<Nat>} & {revisits(grammar, forest, xs, tokens) == False{} : Bool}

# A rival of a node that used production q of nonterminal x: another production of x, of
# higher rank, whose right side derives the same tokens without going round a cycle. The
# nonterminals `xs` are the ones a cycle would come back to: x itself, and the nodes above
# this one that read the same tokens. A node with a rival is outranked: swapping in the
# rival's subtree gives a parse tree that made the preferred choice. A rival that can
# only derive the tokens by going round a cycle does not count: in A ::= @prefer A | a,
# the tree A -> a would otherwise lose to A -> A, which can only end in A -> a again,
# and no tree would be left.
def ProdRival(+grammar: +List<Production>, +marks: +List<Mark>, +x: Nat, +q: Nat, +tokens: +List<Nat>, +xs: +List<Nat>) -> Type:
  &q2: Nat -> {Bool.and(lhsIs(grammar, q2, x), outranks(prodRank(marks, q2), prodRank(marks, q))) == True{} : Bool} & DerivesOnce(grammar, rhsOf(grammar, q2), tokens, xs)

# A rival of a pick or a round that used alternative a of the bracket at (index, path):
# another alternative of that bracket, of higher rank, that derives the same tokens
# without going round a cycle back to one of the nonterminals `xs`. Those include the
# nonterminal of production `index`: a cycle back to this bracket passes through it.
def AltRival(+grammar: +List<Production>, +marks: +List<Mark>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +a: Nat, +tokens: +List<Nat>, +xs: +List<Nat>) -> Type:
  &a2: Nat -> {Bool.and(isAlt(alts, a2), outranks(altRank(marks, index, path, a2), altRank(marks, index, path, a))) == True{} : Bool} & DerivesOnce(grammar, altOf(alts, a2), tokens, xs)

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
# choice.
def Unbeaten(+grammar: +List<Production>, +marks: +List<Mark>, forest: +List<Tree>, items: +List<Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +above: +List<Nat>, +span: +List<Nat>) -> Type:
  match forest items:
    case Con{Node{+q, +children}, +ts} Con{Sym{Nonterminal{+x}}, +rest}:
      +w = leaves(children)
      +xs = {x <> sameAbove(above, span, w) : +List<Nat>}
      (ProdRival(grammar, marks, x, q, w, xs) -> Empty) & Unbeaten(grammar, marks, children, rhsOf(grammar, q), q, [], 0n, xs, w) & Unbeaten(grammar, marks, ts, rest, index, prefix, 1n+dot, above, span)
    case Con{Pick{+a, +children}, +ts} Con{Brack{kind, +alts}, +rest}:
      +w = leaves(children)
      +same = sameAbove(above, span, w)
      +path = List.append(&2, Nat, prefix, [dot])
      (AltRival(grammar, marks, alts, index, path, a, w, {lhsOf(grammar, index) <> same : +List<Nat>}) -> Empty) & Unbeaten(grammar, marks, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, same, w) & Unbeaten(grammar, marks, ts, rest, index, prefix, 1n+dot, above, span)
    case Con{Loop{+rounds}, +ts} Con{Brack{kind, +alts}, +rest}:
      RoundsUnbeaten(grammar, marks, rounds, alts, index, List.append(&2, Nat, prefix, [dot]), above, span) & Unbeaten(grammar, marks, ts, rest, index, prefix, 1n+dot, above, span)
    case Con{t, +ts} Con{it, +rest}:
      Unbeaten(grammar, marks, ts, rest, index, prefix, 1n+dot, above, span)
    case _ _:
      Unit

# The rounds of a loop. Each round is a pick of an alternative of the bracket at
# (index, path), and is checked on its own against the other alternatives.
def RoundsUnbeaten(+grammar: +List<Production>, +marks: +List<Mark>, rounds: +List<Tree>, +alts: +List<+List<Item>>, +index: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>) -> Type:
  match rounds:
    case Nil{}:
      Unit
    case Con{Pick{+a, +children}, +rest}:
      +w = leaves(children)
      +same = sameAbove(above, span, w)
      (AltRival(grammar, marks, alts, index, path, a, w, {lhsOf(grammar, index) <> same : +List<Nat>}) -> Empty) & Unbeaten(grammar, marks, children, altOf(alts, a), index, List.append(&2, Nat, path, [a]), 0n, same, w) & RoundsUnbeaten(grammar, marks, rest, alts, index, path, above, span)
    case Con{other, +rest}:
      RoundsUnbeaten(grammar, marks, rest, alts, index, path, above, span)

# A selected tree: a parse tree of the input with no outranked node. This is the filter:
# the trees that the annotations keep. Without marks, every parse tree is selected.
def Selected(+grammar: +List<Production>, +marks: +List<Mark>, +start: Nat, +inputTokens: +List<Nat>, +tree: Tree) -> Type:
  {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} & {leaves([tree]) == inputTokens : +List<Nat>} & Unbeaten(grammar, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [])

# A set that embeds exactly the selected trees: a parse tree of the input uses only steps
# of the set when, and only when, no node of it is outranked. The set may also hold steps
# that are in no selected tree; they make no tree of their own, so an oracle that keeps
# them still chooses among the selected trees, and only those.
def EmbedsSelected(+grammar: +List<Production>, +marks: +List<Mark>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} ->
    ({allIn(steps(tree, 0n), set) == True{} : Bool} -> Unbeaten(grammar, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], [])) &
    (Unbeaten(grammar, marks, [tree], [Sym{Nonterminal{start}}], 0n, [], 0n, [], []) -> {allIn(steps(tree, 0n), set) == True{} : Bool})
