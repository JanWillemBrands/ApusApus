import Base
import ./CORE.bend as Core
import ./SETS.bend as Sets
import ./GLL.bend as Gll

# THE LL(1) TABLES ON THE CORE (not trusted, then checked). Nullable, FIRST and FOLLOW are
# grown as sets of facts and handed to the check only as they are: the check makes sure
# each is closed under its rules, so it holds what the meaning (LL1.bend) asks of it, and
# then that no two productions of one nonterminal predict the same next token. The tables
# may be larger than the exact sets, so the check may report a conflict the grammar does
# not have; never the other way round (`tables_ll1_sound`).

type FirstFact is Data:
  FirstFact{x: Nat, t: Nat}

type FollowFact is Data:
  FollowFact{x: Nat, next: Maybe<&2, Nat>}

def maybeEq(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{+x} Some{+y}:
      Nat.is_eq(x, y)
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}

def maybeIn(+n: Maybe<&2, Nat>, xs: +List<Maybe<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(maybeEq(n, y), maybeIn(n, rest))

def allMaybeIn(xs: +List<Maybe<&2, Nat>>, +ys: +List<Maybe<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(maybeIn(x, ys), allMaybeIn(rest, ys))

def joinMaybes(a: +List<Maybe<&2, Nat>>, +b: +List<Maybe<&2, Nat>>) -> +List<Maybe<&2, Nat>>:
  match a:
    case Nil{}:
      b
    case Con{+x, rest}:
      x <> joinMaybes(rest, b)

def someAll(ts: +List<Nat>) -> +List<Maybe<&2, Nat>>:
  match ts:
    case Nil{}:
      []
    case Con{+t, rest}:
      Some{t} <> someAll(rest)

# ======== THE SETS ========

def maybeIf(b: Bool, +n: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>) -> +List<Maybe<&2, Nat>>:
  match b:
    case True{}:
      n <> rest
    case False{}:
      rest

def natsIf(b: Bool, +xs: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      xs
    case False{}:
      []

def maybesIf(b: Bool, +xs: +List<Maybe<&2, Nat>>) -> +List<Maybe<&2, Nat>>:
  match b:
    case True{}:
      xs
    case False{}:
      []


def firstsOf(+x: Nat, facts: +List<FirstFact>) -> +List<Nat>:
  match facts:
    case Nil{}:
      []
    case Con{FirstFact{+y, +t}, rest}:
      Sets.addIf(Nat.is_eq(y, x), t, firstsOf(x, rest))

def followsOf(+x: Nat, facts: +List<FollowFact>) -> +List<Maybe<&2, Nat>>:
  match facts:
    case Nil{}:
      []
    case Con{FollowFact{+y, +n}, rest}:
      maybeIf(Nat.is_eq(y, x), n, followsOf(x, rest))

# The tokens the items can begin with, by the tables.
def firstOfItems(items: +List<Core.Sym>, +firsts: +List<FirstFact>, +nulls: +List<Nat>) -> +List<Nat>:
  match items:
    case Nil{}:
      []
    case Con{Core.Terminal{+k}, rest}:
      [k]
    case Con{Core.Nonterminal{+y, +need}, +rest}:
      Sets.joinNats(firstsOf(y, firsts), natsIf(Sets.itemNull(Core.Nonterminal{y, need}, nulls), firstOfItems(rest, firsts, nulls)))

def followHas(+x: Nat, +n: Maybe<&2, Nat>, +follows: +List<FollowFact>) -> Bool:
  maybeIn(n, followsOf(x, follows))

def allFollow(ts: +List<Nat>, +y: Nat, +follows: +List<FollowFact>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{+t, rest}:
      Bool.and(followHas(y, Some{t}, follows), allFollow(rest, y, follows))

# FOLLOW's rule at one item of a production of x: what can begin the items after it, and,
# when they can read nothing, what follows x.
def itemOk(s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> Bool:
  match s:
    case Core.Terminal{k}:
      True{}
    case Core.Nonterminal{+y, need}:
      Bool.and(allFollow(firstOfItems(rest, firsts, nulls), y, follows), Bool.or(Bool.not(Sets.allNull(rest, nulls)), allMaybeIn(followsOf(x, follows), followsOf(y, follows))))

def suffixOk(items: +List<Core.Sym>, +x: Nat, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{+s, +rest}:
      Bool.and(itemOk(s, rest, x, firsts, follows, nulls), suffixOk(rest, x, firsts, follows, nulls))

def firstsClosed(prods: +List<Core.Production>, +firsts: +List<FirstFact>, +nulls: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(Sets.allNatIn(firstOfItems(rhs, firsts, nulls), firstsOf(lhs, firsts)), firstsClosed(rest, firsts, nulls))

def followsClosed(prods: +List<Core.Production>, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(suffixOk(rhs, lhs, firsts, follows, nulls), followsClosed(rest, firsts, follows, nulls))

# ======== PREDICTION AND THE CHECK ========

# What production (x, rhs) can begin with: its FIRST, and FOLLOW of x when it can read nothing.
def predictOf(+x: Nat, +rhs: +List<Core.Sym>, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> +List<Maybe<&2, Nat>>:
  joinMaybes(someAll(firstOfItems(rhs, firsts, nulls)), maybesIf(Sets.allNull(rhs, nulls), followsOf(x, follows)))

def disjoint(xs: +List<Maybe<&2, Nat>>, +ys: +List<Maybe<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.not(maybeIn(x, ys)), disjoint(rest, ys))

# Production (x, rhs) against every later production of the same nonterminal.
def againstLater(prods: +List<Core.Production>, +x: Nat, +rhs: +List<Core.Sym>, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs2, +rhs2}, rest}:
      Bool.and(Bool.or(Bool.not(Nat.is_eq(lhs2, x)), disjoint(predictOf(x, rhs, firsts, follows, nulls), predictOf(lhs2, rhs2, firsts, follows, nulls))),
        againstLater(rest, x, rhs, firsts, follows, nulls))

def pairsOk(prods: +List<Core.Production>, +firsts: +List<FirstFact>, +follows: +List<FollowFact>, +nulls: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      Bool.and(againstLater(rest, lhs, rhs, firsts, follows, nulls), pairsOk(rest, firsts, follows, nulls))

# The tables are closed, the start symbol is followed by the end, and no two productions of
# one nonterminal predict the same token.
def checkWith(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<FirstFact>, +follows: +List<FollowFact>) -> Bool:
  Bool.and(Sets.nullsClosed(grammar, nulls),
    Bool.and(firstsClosed(grammar, firsts, nulls),
      Bool.and(followsClosed(grammar, firsts, follows, nulls),
        Bool.and(followHas(start, None{}, follows),
          Bool.and(suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls),
            pairsOk(grammar, firsts, follows, nulls))))))

# ======== GROWING THE TABLES (not trusted) ========

def firstIn(+x: Nat, +t: Nat, facts: +List<FirstFact>) -> Bool:
  Sets.natIn(t, firstsOf(x, facts))

def firstPick(have: Bool, +x: Nat, +t: Nat, +acc: +List<FirstFact>) -> +List<FirstFact>:
  match have:
    case True{}:
      acc
    case False{}:
      FirstFact{x, t} <> acc

def addFirsts(ts: +List<Nat>, +x: Nat, +acc: +List<FirstFact>) -> +List<FirstFact>:
  match ts:
    case Nil{}:
      acc
    case Con{+t, rest}:
      addFirsts(rest, x, firstPick(firstIn(x, t, acc), x, t, acc))

def firstsOnce(prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<FirstFact>) -> +List<FirstFact>:
  match prods:
    case Nil{}:
      acc
    case Con{Core.Production{+lhs, +rhs}, rest}:
      firstsOnce(rest, nulls, addFirsts(firstOfItems(rhs, acc, nulls), lhs, acc))

def growFirsts(n: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<FirstFact>) -> +List<FirstFact>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      growFirsts(p, grammar, nulls, firstsOnce(grammar, nulls, acc))

def followPick(have: Bool, +x: Nat, +n: Maybe<&2, Nat>, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match have:
    case True{}:
      acc
    case False{}:
      FollowFact{x, n} <> acc

def addFollows(ns: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match ns:
    case Nil{}:
      acc
    case Con{+n, rest}:
      addFollows(rest, y, followPick(followHas(y, n, acc), y, n, acc))

def itemFollows(s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +firsts: +List<FirstFact>, +nulls: +List<Nat>, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match s:
    case Core.Terminal{k}:
      acc
    case Core.Nonterminal{+y, need}:
      addFollows(joinMaybes(someAll(firstOfItems(rest, firsts, nulls)), maybesIf(Sets.allNull(rest, nulls), followsOf(x, acc))), y, acc)

def suffixFollows(items: +List<Core.Sym>, +x: Nat, +firsts: +List<FirstFact>, +nulls: +List<Nat>, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match items:
    case Nil{}:
      acc
    case Con{+s, +rest}:
      suffixFollows(rest, x, firsts, nulls, itemFollows(s, rest, x, firsts, nulls, acc))

def followsOnce(prods: +List<Core.Production>, +firsts: +List<FirstFact>, +nulls: +List<Nat>, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match prods:
    case Nil{}:
      acc
    case Con{Core.Production{+lhs, +rhs}, rest}:
      followsOnce(rest, firsts, nulls, suffixFollows(rhs, lhs, firsts, nulls, acc))

def growFollows(n: Nat, +grammar: +List<Core.Production>, +firsts: +List<FirstFact>, +nulls: +List<Nat>, +acc: +List<FollowFact>) -> +List<FollowFact>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      growFollows(p, grammar, firsts, nulls, followsOnce(grammar, firsts, nulls, acc))

def checkFirsts(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<FirstFact>) -> Bool:
  checkWith(grammar, start, nulls, firsts, growFollows(fuel, grammar, firsts, nulls, [FollowFact{start, None{}}]))

def checkNulls(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>) -> Bool:
  checkFirsts(fuel, grammar, start, nulls, growFirsts(fuel, grammar, nulls, []))

# LL(1) BY THE TABLES: grow the tables with `fuel` rounds each, then check them.
def ll1ByTables(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat) -> Bool:
  checkNulls(fuel, grammar, start, Sets.growNulls(fuel, grammar, []))
