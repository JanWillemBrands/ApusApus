import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll

# NULLABLE, FIRST AND FOLLOW TABLES (not trusted: computed here, checked to be closed).
#
# Per nonterminal x: can x derive nothing, which tokens can start it, and which tokens
# (or the end of the input) can follow it. The engine's prediction (`Gll.predictAt`)
# reads them. They are found by iterating from empty tables until one more round adds
# nothing; the closedness check is that last round. Closed tables contain the true
# sets, which is all prediction needs: a larger set only predicts more.

# The number of nonterminals: one more than the largest left side.
def ntCount(grammar: +List<Spec.Production>) -> Nat:
  match grammar:
    case Nil{}:
      0n
    case Con{Spec.Production{lhs, rhs}, rest}:
      Nat.max(1n+lhs, ntCount(rest))

def natsSub(xs: +List<Nat>, +ys: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Gll.natIn(x, ys), natsSub(rest, ys))

# Is every token of a in b?
def lsSub(a: Gll.LSet, b: Gll.LSet) -> Bool:
  match a b:
    case Gll.LSet{a1, t1, e1} Gll.LSet{+a2, +t2, e2}:
      Bool.or(a2, Bool.and(Bool.not(a1), Bool.and(natsSub(t1, t2), Bool.or(Bool.not(e1), e2))))

# What the productions of x give, with the tables t.
def nulFor(grammar: +List<Spec.Production>, +x: Nat, +t: Gll.Tables) -> Bool:
  match grammar:
    case Nil{}:
      False{}
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      Bool.or(Bool.and(Nat.is_eq(lhs, x), Gll.nulOf(Gll.infoItems(rhs, t))), nulFor(rest, x, t))

def fstFor(grammar: +List<Spec.Production>, +x: Nat, +t: Gll.Tables) -> Gll.LSet:
  match grammar:
    case Nil{}:
      Gll.emptyLS()
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      Gll.lsUnion(Gll.lsIf(Nat.is_eq(lhs, x), Gll.firstOf(Gll.infoItems(rhs, t))), fstFor(rest, x, t))

# What may follow x where it stands in the items: the predict set of the slot after it.
# The same two modes as `Gll.infoOf`; in MAlts, `dot` counts the alternatives.
def follows(fuel: Nat, mode: Gll.Mode, items: +List<Spec.Item>, alts: +List<+List<Spec.Item>>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat, +index: Nat, +rpath: +List<Nat>, +dot: Nat) -> Gll.LSet:
  match fuel mode items alts:
    case 0n _ _ _:
      Gll.LSet{True{}, [], True{}}
    case 1n+(+f) Gll.MItems{} Nil{} _:
      Gll.emptyLS()
    case 1n+(+f) Gll.MItems{} Con{Spec.Sym{Spec.Nonterminal{+y}}, rest} _:
      Gll.lsUnion(Gll.lsIf(Nat.is_eq(y, x), Gll.predictAt(grammar, t, index, rpath, 1n+dot)), follows(1n+f, Gll.MItems{}, rest, alts, grammar, t, x, index, rpath, 1n+dot))
    case 1n+(+f) Gll.MItems{} Con{Spec.Brack{kind, inner}, rest} _:
      Gll.lsUnion(follows(f, Gll.MAlts{}, [], inner, grammar, t, x, index, dot <> rpath, 0n), follows(1n+f, Gll.MItems{}, rest, alts, grammar, t, x, index, rpath, 1n+dot))
    case 1n+(+f) Gll.MItems{} Con{it, rest} _:
      follows(1n+f, Gll.MItems{}, rest, alts, grammar, t, x, index, rpath, 1n+dot)
    case 1n+(+f) Gll.MAlts{} _ Nil{}:
      Gll.emptyLS()
    case 1n+(+f) Gll.MAlts{} _ Con{alt, rest}:
      Gll.lsUnion(follows(f, Gll.MItems{}, alt, [], grammar, t, x, index, dot <> rpath, 0n), follows(1n+f, Gll.MAlts{}, items, rest, grammar, t, x, index, rpath, 1n+dot))

def folFrom(prods: +List<Spec.Production>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat, +index: Nat) -> Gll.LSet:
  match prods:
    case Nil{}:
      Gll.emptyLS()
    case Con{Spec.Production{lhs, +rhs}, rest}:
      Gll.lsUnion(follows(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, x, index, [], 0n), folFrom(rest, grammar, t, x, 1n+index))

def folFor(+grammar: +List<Spec.Production>, +start: Nat, +x: Nat, +t: Gll.Tables) -> Gll.LSet:
  Gll.lsUnion(Gll.LSet{False{}, [], Nat.is_eq(x, start)}, folFrom(grammar, grammar, t, x, 0n))

# One round, for the nonterminals from x on (n of them): the old entry joined with what
# the productions give.
def nulRound(n: Nat, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat) -> +List<Bool>:
  match n:
    case 0n:
      []
    case 1n+m:
      Bool.or(Gll.boolAt(Gll.nulTab(t), x), nulFor(grammar, x, t)) <> nulRound(m, grammar, t, 1n+x)

def fstRound(n: Nat, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat) -> +List<Gll.LSet>:
  match n:
    case 0n:
      []
    case 1n+m:
      Gll.lsUnion(Gll.lsAt(Gll.fstTab(t), x), fstFor(grammar, x, t)) <> fstRound(m, grammar, t, 1n+x)

def folRound(n: Nat, +grammar: +List<Spec.Production>, +start: Nat, +t: Gll.Tables, +x: Nat) -> +List<Gll.LSet>:
  match n:
    case 0n:
      []
    case 1n+m:
      Gll.lsUnion(Gll.lsAt(Gll.folTab(t), x), folFor(grammar, start, x, t)) <> folRound(m, grammar, start, t, 1n+x)

def round(+grammar: +List<Spec.Production>, +start: Nat, +t: Gll.Tables) -> Gll.Tables:
  +n = ntCount(grammar)
  Gll.Tables{nulRound(n, grammar, t, 0n), fstRound(n, grammar, t, 0n), folRound(n, grammar, start, t, 0n)}

# CLOSED TABLES, stated where they are used: for every production, its right side's
# nullable and FIRST are in its nonterminal's entries; for every nonterminal y in every
# right side, the predict set of the slot after it is in FOLLOW(y); and the end of the
# input may follow the start symbol. (One more round adds nothing.) Running out of
# nesting fuel fails the check.
def followsOk(fuel: Nat, mode: Gll.Mode, items: +List<Spec.Item>, alts: +List<+List<Spec.Item>>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat) -> Bool:
  match fuel mode items alts:
    case 0n _ _ _:
      False{}
    case 1n+(+f) Gll.MItems{} Nil{} _:
      True{}
    case 1n+(+f) Gll.MItems{} Con{Spec.Sym{Spec.Nonterminal{+y}}, rest} _:
      Bool.and(lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+dot), Gll.lsAt(Gll.folTab(t), y)), followsOk(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, rpath, 1n+dot))
    case 1n+(+f) Gll.MItems{} Con{Spec.Brack{kind, inner}, rest} _:
      Bool.and(followsOk(f, Gll.MAlts{}, [], inner, grammar, t, index, dot <> rpath, 0n), followsOk(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, rpath, 1n+dot))
    case 1n+(+f) Gll.MItems{} Con{it, rest} _:
      followsOk(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, rpath, 1n+dot)
    case 1n+(+f) Gll.MAlts{} _ Nil{}:
      True{}
    case 1n+(+f) Gll.MAlts{} _ Con{alt, rest}:
      Bool.and(followsOk(f, Gll.MItems{}, alt, [], grammar, t, index, dot <> rpath, 0n), followsOk(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, rpath, 1n+dot))

def prodOk(+lhs: Nat, +rhs: +List<Spec.Item>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat) -> Bool:
  +info = Gll.infoItems(rhs, t)
  +nulOk = Bool.or(Bool.not(Gll.nulOf(info)), Gll.boolAt(Gll.nulTab(t), lhs))
  +fstOk = lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), lhs))
  Bool.and(nulOk, Bool.and(fstOk, followsOk(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, index, [], 0n)))

def prodsOk(prods: +List<Spec.Production>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      Bool.and(prodOk(lhs, rhs, grammar, t, index), prodsOk(rest, grammar, t, 1n+index))

def tablesClosed(+grammar: +List<Spec.Production>, +start: Nat, +t: Gll.Tables) -> Bool:
  Bool.and(prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)))

# Iterate a number of rounds; the check decides whether that was enough.
def iterate(n: Nat, +grammar: +List<Spec.Production>, +start: Nat, t: Gll.Tables) -> Gll.Tables:
  match n:
    case 0n:
      t
    case 1n+m:
      iterate(m, grammar, start, round(grammar, start, t))

def closedPick(ok: Bool, +t: Gll.Tables) -> Maybe<&2, Gll.Tables>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      None{}

def emptyTables() -> Gll.Tables:
  Gll.Tables{[], [], []}

# The tables after `rounds` rounds, handed out only when they are closed.
def tablesOf(rounds: Nat, +grammar: +List<Spec.Production>, +start: Nat) -> Maybe<&2, Gll.Tables>:
  +t = iterate(rounds, grammar, start, emptyTables())
  closedPick(tablesClosed(grammar, start, t), t)
