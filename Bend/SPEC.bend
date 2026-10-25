import Base

# THE SPECIFICATION: what parsing an EBNF grammar means, independent of any parser.
#
# Right-hand sides are regular expressions over symbols, after Scott and Johnstone,
# "GLL Syntax Analysers For EBNF Grammars", Definition 1: a sequence of items, where
# an item is a symbol or a bracket ( ) [ ] { } < > around alternatives. An empty
# sequence is ε. Terminals are token kinds, nonterminals are ids, as before.

type Symbol is Data:
  Terminal{kind: Nat}
  Nonterminal{id: Nat}

# ( τ ) group, [ τ ] optional, { τ } closure (zero or more), < τ > positive closure.
type Bracket is Data:
  Group{}
  Optional{}
  Closure{}
  Positive{}

# One item of a sequence: a symbol, or a bracket around one or more alternatives.
type Item is Data:
  Sym{symbol: Symbol}
  Brack{kind: Bracket, alts: +List<+List<Item>>}

# One production `lhs = rhs`. Alternatives at the top are separate productions, so a
# nonterminal's rule A ::= τ1 | ... | τt is t productions.
type Production is Data:
  Production{lhs: Nat, rhs: +List<Item>}

# PARSE TREES. A bracket gets a node of its own, as in Scott's "root-node based
# choice" (section 3.1): it groups what the bracket matched, which is what makes
# closures with nullable bodies come out right.
#   Leaf{kind}           a token
#   Node{index, ...}     a nonterminal, expanded by production `index`
#   Pick{alt, ...}       a bracket matched once, by its alternative number `alt`
#   Skip{}               an optional [ τ ] that matched nothing (Scott's ε node)
#   Loop{rounds}         a closure { τ } or < τ >; each round is a Pick
type Tree is Data:
  Leaf{kind: Nat}
  Node{index: Nat, children: +List<Tree>}
  Pick{alt: Nat, children: +List<Tree>}
  Skip{}
  Loop{rounds: +List<Tree>}

def lhsIs(+grammar: +List<Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Production{lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+i:
      lhsIs(rest, i, id)

def rhsOf(+grammar: +List<Production>, index: Nat) -> +List<Item>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Production{lhs, rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+i:
      rhsOf(rest, i)

# Alternative number `a` of a bracket (empty when there is no such alternative).
def altOf(alts: +List<+List<Item>>, a: Nat) -> +List<Item>:
  match alts a:
    case Nil{} _:
      []
    case Con{alt, rest} 0n:
      alt
    case Con{alt, rest} 1n+b:
      altOf(rest, b)

def isAlt(alts: +List<+List<Item>>, +a: Nat) -> Bool:
  Nat.is_lt(a, List.length(&2, +List<Item>, alts))

# n copies of the same item: the rounds of a closure each match the bracket once.
def times(n: Nat, +item: Item) -> +List<Item>:
  match n:
    case 0n:
      []
    case 1n+m:
      item <> times(m, item)

# Does the forest fit the items, one tree per item?
#   a leaf fits a terminal of its kind;
#   a node fits a nonterminal through one of its productions;
#   a pick fits ( τ ) or [ τ ] when its children fit the chosen alternative;
#   a skip fits [ τ ];
#   a loop fits { τ } when each round fits ( τ ), and < τ > when there is a round.
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
    case Con{Pick{+a, children}, ts} Con{Brack{Optional{}, +alts}, rest}:
      Bool.and(Bool.and(isAlt(alts, a), fits(children, grammar, altOf(alts, a))), fits(ts, grammar, rest))
    case Con{Skip{}, ts} Con{Brack{Optional{}, alts}, rest}:
      fits(ts, grammar, rest)
    case Con{Loop{+rounds}, ts} Con{Brack{Closure{}, +alts}, rest}:
      Bool.and(fits(rounds, grammar, times(List.length(&2, Tree, rounds), Brack{Group{}, alts})), fits(ts, grammar, rest))
    case Con{Loop{+rounds}, ts} Con{Brack{Positive{}, +alts}, rest}:
      Bool.and(Bool.and(Bool.not(List.is_empty(&2, Tree, rounds)), fits(rounds, grammar, times(List.length(&2, Tree, rounds), Brack{Group{}, alts}))), fits(ts, grammar, rest))
    case _ _:
      False{}

# The tokens at the leaves of the forest, left to right.
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

# The items derive the input when some forest fits them and spells the input.
def Derives(+grammar: +List<Production>, +items: +List<Item>, +inputTokens: +List<Nat>) -> Type:
  &forest: +List<Tree> -> {fits(forest, grammar, items) == True{} : Bool} & {leaves(forest) == inputTokens : +List<Nat>}

# BINARY SUBTREE SETS.
#
# A slot is a position in a production's right side: `path` leads through nested
# brackets to a dot. [d] is the dot after d items of the right side; [m, a, d] is the
# dot after d items of alternative a of the bracket at item m; and so on, deeper.
type Slot is Data:
  Slot{index: Nat, path: +List<Nat>}

type Bsr is Data:
  Bsr{slot: Slot, i: Nat, k: Nat, j: Nat}

def pathEq(xs: +List<Nat>, ys: +List<Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Nat.is_eq(x, y), pathEq(xr, yr))
    case _ _:
      False{}

def bsrMember(+element: Bsr, set: +List<Bsr>) -> Bool:
  match element set:
    case _ Nil{}:
      False{}
    case Bsr{Slot{+p, +path}, +i, +k, +j} Con{Bsr{Slot{p2, path2}, i2, k2, j2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(p, p2), Bool.and(pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), bsrMember(Bsr{Slot{p, path}, i, k, j}, rest))

def at(+index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bsr:
  Bsr{Slot{index, List.append(&2, Nat, prefix, [dot])}, i, k, j}

# The ε step of an empty sequence, for the first position only.
def emptyStep(dot: Nat, +index: Nat, +prefix: +List<Nat>, +i: Nat, +k: Nat) -> +List<Bsr>:
  match dot:
    case 0n:
      [at(index, prefix, 0n, i, k, k)]
    case 1n+d:
      []

# The steps of a forest, with Swift Apus's conventions:
# - in a sequence (rounds = False), child number `dot` + 1 completes the slot after it,
#   from the sequence start i, with pivot at its own start; every child does, the
#   first one too; an empty sequence has one ε step;
# - a nonterminal, a ( ) or a [ ] starts a sequence of its own at its start, like an
#   anonymous nonterminal;
# - the rounds of a loop (rounds = True) each run the body from the loop's start, so
#   later rounds chain on to earlier ones, as in Scott and Johnstone's closures.
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

# All steps of a tree that starts at position i.
def steps(tree: Tree, +i: Nat) -> +List<Bsr>:
  match tree:
    case Node{+index, +children}:
      walk(children, False{}, index, [], 0n, i, i)
    case _:
      []

def allIn(xs: +List<Bsr>, +set: +List<Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(bsrMember(x, set), allIn(rest, set))

def sameSet(+xs: +List<Bsr>, +ys: +List<Bsr>) -> Bool:
  Bool.and(allIn(xs, ys), allIn(ys, xs))

# EXACT BSR SETS: what every parser must produce, for any EBNF grammar. As for BNF:
# a set is the exact BSR set of an input when it holds exactly the steps of the parse
# trees of the input. Every element is a step of some parse tree (no dead wood), and
# no step of a parse tree is missing. Order and duplicates do not matter.

# No dead wood: every element is a step of some parse tree of the input.
def OnlyParseSteps(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @element: Bsr -> {bsrMember(element, set) == True{} : Bool} ->
    &tree: Tree -> {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} & {leaves([tree]) == inputTokens : +List<Nat>} & {bsrMember(element, steps(tree, 0n)) == True{} : Bool}

# Nothing missing: every step of every parse tree of the input is in the set.
def EveryParseStep(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> @element: Bsr ->
    {fits([tree], grammar, [Sym{Nonterminal{start}}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} -> {bsrMember(element, steps(tree, 0n)) == True{} : Bool} ->
    {bsrMember(element, set) == True{} : Bool}

def IsExactBsr(+grammar: +List<Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Bsr>) -> Type:
  OnlyParseSteps(grammar, start, inputTokens, set) & EveryParseStep(grammar, start, inputTokens, set)
