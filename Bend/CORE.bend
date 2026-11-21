import Base
import ./LEMMAS.bend as Lemma

# THE BNF CORE: grammars of plain productions, their trees, and the steps of a tree.
#
# Every law is stated on this core. A grammar as written (with brackets) means the core
# grammar EBNF.bend translates it to, and its parse trees are the core trees of that
# grammar. So a tree has two shapes, a leaf and a node, and a position in a right side is a
# production and a dot (how many of its items lie before it).

# ======== GRAMMARS ========

# What an occurrence of a nonterminal must read: anything, at least one token, or no token.
# Nonterminals as written may read anything. The translation of brackets uses the other two
# (EBNF.bend): the pick of a [ ] and the rounds of a loop read something, and the one round of
# a < > over nothing reads nothing.
type Need is Data:
  Anything{}
  Something{}
  Nothing{}

# An item of a right side: a terminal (a token kind) or a nonterminal (a number) with its need.
type Sym is Data:
  Terminal{kind: Nat}
  Nonterminal{id: Nat, need: Need}

# One production `lhs = rhs`. A nonterminal's alternatives are separate productions; a
# tree names the production it uses by its place in the grammar.
type Production is Data:
  Production{lhs: Nat, rhs: +List<Sym>}

# The right side of production `index` (empty past the end of the grammar).
def rhsOf(+grammar: +List<Production>, index: Nat) -> +List<Sym>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Production{lhs, +rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+n:
      rhsOf(rest, n)

# Is production `index` a production of nonterminal `id`?
def lhsIs(+grammar: +List<Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Production{+lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+n:
      lhsIs(rest, n, id)

# ======== TREES ========

# A tree: a leaf is a token; a node is a use of production `index`, with one child per item
# of its right side. A list of trees is a forest.
type Tree is Data:
  Leaf{kind: Nat}
  Node{index: Nat, children: +List<Tree>}

# The tokens a forest spells, left to right.
def leaves(forest: +List<Tree>) -> +List<Nat>:
  match forest:
    case Nil{}:
      []
    case Con{Leaf{+k}, ts}:
      k <> leaves(ts)
    case Con{Node{q, +ch}, ts}:
      List.append(&2, Nat, leaves(ch), leaves(ts))

# How many tokens a tree spells.
def width(+t: Tree) -> Nat:
  List.length(&2, Nat, leaves([t]))

# Does an occurrence with this need allow a tree of this width?
def needOk(need: Need, +w: Nat) -> Bool:
  match need:
    case Anything{}:
      True{}
    case Something{}:
      Bool.not(Nat.is_eq(w, 0n))
    case Nothing{}:
      Nat.is_eq(w, 0n)

# The forest fits the items, one tree per item: a leaf a terminal of its kind, a node a
# nonterminal through one of its productions, within the occurrence's need.
def fits(forest: +List<Tree>, +grammar: +List<Production>, items: +List<Sym>) -> Bool:
  match forest items:
    case Nil{} Nil{}:
      True{}
    case Con{Leaf{kind}, ts} Con{Terminal{k}, rest}:
      Bool.and(Nat.is_eq(kind, k), fits(ts, grammar, rest))
    case Con{Node{+q, +ch}, ts} Con{Nonterminal{id, need}, rest}:
      Bool.and(Bool.and(Bool.and(lhsIs(grammar, q, id), needOk(need, width(Node{q, ch}))), fits(ch, grammar, rhsOf(grammar, q))), fits(ts, grammar, rest))
    case _ _:
      False{}

# The token at position n of the input; None past its end.
def tokAt(input: +List<Nat>, n: Nat) -> Maybe<&2, Nat>:
  match input n:
    case Nil{} _:
      None{}
    case Con{+x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+m:
      tokAt(rest, m)

# Is the token found the token t?
def tokIs(found: Maybe<&2, Nat>, +t: Nat) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, t)

# The forest fits the items and reads the input from position k on: every leaf is the token
# at its position.
def reads(forest: +List<Tree>, +grammar: +List<Production>, items: +List<Sym>, +input: +List<Nat>, +k: Nat) -> Bool:
  match forest items:
    case Nil{} Nil{}:
      True{}
    case Con{Leaf{+kind}, ts} Con{Terminal{t}, rest}:
      Bool.and(Nat.is_eq(kind, t), Bool.and(tokIs(tokAt(input, k), kind), reads(ts, grammar, rest, input, 1n+k)))
    case Con{Node{+q, +ch}, ts} Con{Nonterminal{id, need}, rest}:
      Bool.and(Bool.and(Bool.and(lhsIs(grammar, q, id), needOk(need, width(Node{q, ch}))), reads(ch, grammar, rhsOf(grammar, q), input, k)), reads(ts, grammar, rest, input, Nat.add(k, width(Node{q, ch}))))
    case _ _:
      False{}

# A parse tree of the input: a tree of the start symbol that reads the input from position 0,
# and has as many leaves as the input has tokens.
def ParseTree(+grammar: +List<Production>, +start: Nat, +input: +List<Nat>, +tree: Tree) -> Type:
  {reads([tree], grammar, [Nonterminal{start, Anything{}}], input, 0n) == True{} : Bool} & {List.length(&2, Nat, leaves([tree])) == List.length(&2, Nat, input) : Nat}

# The items derive w: there is a forest that fits them and spells w.
def Derives(+grammar: +List<Production>, +items: +List<Sym>, +w: +List<Nat>) -> Type:
  &f: +List<Tree> -> {fits(f, grammar, items) == True{} : Bool} & {leaves(f) == w : +List<Nat>}

# ======== STEPS ========

# One step of a parse tree (a binary subtree set element, BSR): production `index` after its
# first `dot` items. Its node starts at position i, and the item just before the dot reads
# the input from k to j. An empty right side has one step, at dot 0, with i = k = j.
type Bsr is Data:
  Bsr{index: Nat, dot: Nat, i: Nat, k: Nat, j: Nat}

# The step of an empty right side: only when no child came before (dot 0).
def emptyAt(dot: Nat, +q: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match dot:
    case 0n:
      [Bsr{q, 0n, i, k, k}]
    case 1n+d:
      []

# A node's own steps: one per child (the slot after it), or the one step of an empty
# right side.
def own(+q: Nat, ch: +List<Tree>, +dot: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match ch:
    case Nil{}:
      emptyAt(dot, q, i, k)
    case Con{+t, rest}:
      Bsr{q, 1n+dot, i, k, Nat.add(k, width(t))} <> own(q, rest, 1n+dot, i, Nat.add(k, width(t)))

# All steps of a forest that starts at k: each node's own steps, then its children's.
def steps(forest: +List<Tree>, +k: Nat) -> +List<Bsr>:
  match forest:
    case Nil{}:
      []
    case Con{Leaf{kind}, ts}:
      steps(ts, 1n+k)
    case Con{Node{+q, +ch}, ts}:
      List.append(&2, Bsr, own(q, ch, 0n, k, k), List.append(&2, Bsr, steps(ch, k), steps(ts, Nat.add(k, width(Node{q, ch})))))

# Are the two steps the same?
def bsrEq(a: Bsr, b: Bsr) -> Bool:
  match a b:
    case Bsr{q1, d1, i1, k1, j1} Bsr{q2, d2, i2, k2, j2}:
      Bool.and(Nat.is_eq(q1, q2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(i1, i2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2)))))

# A set of steps is a list read only by membership.
def member(+x: Bsr, set: +List<Bsr>) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(bsrEq(x, y), member(x, rest))

# Is every step of xs in the set?
def allIn(xs: +List<Bsr>, +set: +List<Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(member(x, set), allIn(rest, set))

# THE EXACT SET. EveryParseStep: for every parse tree and every step x of it, x is in the
# set. OnlyParseSteps: for every x in the set, there is a parse tree that has x. IsExact:
# both, so the set holds the steps of the parse trees and nothing else.
def EveryParseStep(+grammar: +List<Production>, +start: Nat, +input: +List<Nat>, +set: +List<Bsr>) -> Type:
  @tree: Tree -> @x: Bsr -> ParseTree(grammar, start, input, tree) -> {member(x, steps([tree], 0n)) == True{} : Bool} -> {member(x, set) == True{} : Bool}

def OnlyParseSteps(+grammar: +List<Production>, +start: Nat, +input: +List<Nat>, +set: +List<Bsr>) -> Type:
  @x: Bsr -> {member(x, set) == True{} : Bool} -> &tree: Tree -> ParseTree(grammar, start, input, tree) & {member(x, steps([tree], 0n)) == True{} : Bool}

def IsExact(+grammar: +List<Production>, +start: Nat, +input: +List<Nat>, +set: +List<Bsr>) -> Type:
  EveryParseStep(grammar, start, input, set) & OnlyParseSteps(grammar, start, input, set)
