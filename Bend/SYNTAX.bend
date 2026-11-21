import Base

# THE GRAMMAR AS WRITTEN. The syntax the core reads (EBNF.bend translates it): productions
# whose right sides are items, an item a symbol, a bracket ( ) [ ] { } < > around
# alternatives, or ε; the marks as written; and Swift Apus's steps, named by slots in the
# grammar as written, which the core's steps map to (EBNF.bend, `stepsToSwift`). Only syntax
# lives here: what a grammar means is its translation to the core (CORE.bend).

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

# One rule on an alternative, as written. N... is a list of nonterminals. Ahead{N...} is
# >?>( N ) (several are written as several >?>), NotAhead{N...} is >!>( N, ... ),
# LeftAssoc{[]} a bare @left and LeftAssoc{N...} @left(N...), RightAssoc the same for
# @right. What each rule means is in GUARD.bend.
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

# The rank of an alternative: Avoided for @avoid, Plain without a mark, Preferred for
# @prefer. Alternatives of equal rank are not ranked against each other, so two
# Preferred siblings both stay.
type Rank is Data:
  Avoided{}
  Plain{}
  Preferred{}

# The marks of a grammar, kept next to it. ProdMark: production `index` is marked.
# AltMark: alternative `alt` of the bracket at (index, path) is marked, where path is the
# path of the bracket's own item, as in a Slot ([m] for item m of the right side, [m, a, d]
# for item d of alternative a of the bracket at m, and so on). An alternative without a
# mark is Plain; with more than one, the first counts.
type Mark is Data:
  ProdMark{index: Nat, rank: Rank}
  AltMark{index: Nat, path: +List<Nat>, alt: Nat, rank: Rank}

# @longest and @shortest; what they mean is in EXTENT.bend.
type Extent is Data:
  Longest{}
  Shortest{}

# Where an extent mark sits. NtExtent: on every node of nonterminal x. BrackExtent: on the
# bracket item at (index, path), with path as in Mark: [m] for item m of the right side of
# production `index`, [m, a, d] for item d of alternative a of the bracket at m, and so on.
type ExtentMark is Data:
  NtExtent{x: Nat, ext: Extent}
  BrackExtent{index: Nat, path: +List<Nat>, ext: Extent}
