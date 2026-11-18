import Base
import ../LEMMAS.bend as Lemma
import ../SPEC.bend as Spec
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./EBNF.bend as E
import ./GUARD.bend as Guard
import ./RIVAL.bend as R
import ./SETS.bend as Sets

# PHASE 2 ON THE CORE: @prefer AND @avoid.
#
# Every production has a rank: @prefer high, @avoid low, unmarked in between (a mark on a
# bracket alternative sits on that alternative's group production). A completed step of
# production q over i .. j is beaten when a production of the same nonterminal with a higher
# rank has a rival there: a forest over the same tokens whose steps, placed at i, keep their
# rules (phase 1). A tree is unbeaten when none of its completed steps is beaten.
#
# A rival that goes round a cycle back to where it competes, over the same tokens, would
# only say "the same again", and could beat every reading. A well-formed grammar has no
# such rival: an outranking production lies on no cycle that reads no input (the rule at
# the end of this file, and `no_self_rival` in PROOF_PREFER.bend).

# ======== THE MEANING ========

type Rank is Data:
  Avoided{}
  Plain{}
  Preferred{}

def rankNat(r: Rank) -> Nat:
  match r:
    case Avoided{}:
      0n
    case Plain{}:
      1n
    case Preferred{}:
      2n

def outranks(a: Rank, b: Rank) -> Bool:
  Nat.is_lt(rankNat(b), rankNat(a))

type RankMark is Data:
  RankMark{index: Nat, rank: Rank}

def rankPick(hit: Bool, +r: Rank, +later: Rank) -> Rank:
  match hit:
    case True{}:
      r
    case False{}:
      later

# The rank of production q: from the first mark for it, and Plain without one.
def rankOf(marks: +List<RankMark>, +q: Nat) -> Rank:
  match marks:
    case Nil{}:
      Plain{}
    case Con{RankMark{+p, +r}, rest}:
      rankPick(Nat.is_eq(p, q), r, rankOf(rest, q))

# Production m is another production of q's nonterminal, of higher rank.
def outranking(+grammar: +List<Core.Production>, +marks: +List<RankMark>, +q: Nat, +m: Nat) -> Bool:
  Bool.and(Core.lhsIs(grammar, m, Gll.lhsOf(grammar, q)), outranks(rankOf(marks, m), rankOf(marks, q)))

def ntOf(s: Core.Sym) -> Maybe<&2, Nat>:
  match s:
    case Core.Terminal{k}:
      None{}
    case Core.Nonterminal{+id, need}:
      Some{id}

def ntAt(items: +List<Core.Sym>, e: Nat) -> Maybe<&2, Nat>:
  match items e:
    case Nil{} _:
      None{}
    case Con{+s, rest} 0n:
      ntOf(s)
    case Con{s, +rest} 1n+(+m):
      ntAt(rest, m)

# The nonterminal of the item before dot d, if that item is a nonterminal.
def before(+items: +List<Core.Sym>, d: Nat) -> Maybe<&2, Nat>:
  match d:
    case 0n:
      None{}
    case 1n+(+e):
      ntAt(items, e)

def isNt(m: Maybe<&2, Nat>, +y: Nat) -> Bool:
  match m:
    case Some{+v}:
      Nat.is_eq(v, y)
    case None{}:
      False{}

# A rival of production m over i .. j: children for m that spell the same tokens, and whose
# steps, placed at i, keep their rules.
def Rival(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat) -> Type:
  &ch: +List<Core.Tree> -> {Core.fits(ch, grammar, Core.rhsOf(grammar, m)) == True{} : Bool} & {Core.leaves(ch) == Lemma.slice(input, i, Nat.sub(j, i)) : +List<Nat>} & Guard.AllStepsOk(grammar, gmarks, input, Core.steps([Core.Node{m, ch}], i))

def Beaten(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<RankMark>, +input: +List<Nat>, +q: Nat, +i: Nat, +j: Nat) -> Type:
  &m: Nat -> {outranking(grammar, rmarks, q, m) == True{} : Bool} & Rival(grammar, gmarks, input, m, i, j)

# A step is free when it completes no beaten node.
def Free(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<RankMark>, +input: +List<Nat>, x: Core.Bsr) -> Type:
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      Guard.When(Nat.is_eq(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Beaten(grammar, gmarks, rmarks, input, q, i, j) -> Empty)

# ======== THE MARKS AS WRITTEN, ON THE CORE ========

def rankFrom(r: Spec.Rank) -> Rank:
  match r:
    case Spec.Avoided{}:
      Avoided{}
    case Spec.Plain{}:
      Plain{}
    case Spec.Preferred{}:
      Preferred{}

def rankAt(m: Maybe<&2, Nat>, +r: Spec.Rank, +rest: +List<RankMark>) -> +List<RankMark>:
  match m:
    case Some{+q}:
      RankMark{q, rankFrom(r)} <> rest
    case None{}:
      rest

# A mark on production `index` stays there; a mark on alternative a of the bracket at
# (index, path) moves to the production whose origin is that alternative's sequence.
def rankMarksOf(ms: +List<Spec.Mark>, +origins: +List<E.Origin>) -> +List<RankMark>:
  match ms:
    case Nil{}:
      []
    case Con{Spec.ProdMark{+index, +r}, rest}:
      RankMark{index, rankFrom(r)} <> rankMarksOf(rest, origins)
    case Con{Spec.AltMark{+index, +path, +a, +r}, rest}:
      rankAt(Guard.productionAt(origins, index, List.append(&2, Nat, path, [a]), 0n), r, rankMarksOf(rest, origins))

# ======== THE VERDICT ON A STEP ========
#
# A completed step of q over i .. j is asked about each production m that outranks q. Yes
# (not beaten by m) when no forest for m over the tokens has steps that keep their rules
# (RIVAL.bend, checked closed); No (beaten) with a certificate: children for m over the
# tokens, checked with `reads`, whose steps at i are each answered Yes by phase 1. Unknown
# otherwise.

def allYes(xs: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Guard.isYes(Guard.stepTri(fuel, grammar, gmarks, input, x)), allYes(rest, fuel, grammar, gmarks, input))

def certWith(+ch: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat) -> Bool:
  Bool.and(Guard.forestOk(grammar, m, Lemma.slice(input, i, Nat.sub(j, i)), ch), allYes(Core.steps([Core.Node{m, ch}], i), fuel, grammar, gmarks, input))

def certTri(b: Bool) -> Guard.Tri:
  match b:
    case True{}:
      Guard.No{}
    case False{}:
      Guard.Unknown{}

def closedTri(b: Bool) -> Guard.Tri:
  match b:
    case True{}:
      Guard.Yes{}
    case False{}:
      Guard.Unknown{}

def foundTri(found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>) -> Guard.Tri:
  match found:
    case True{}:
      certTri(certWith(R.forestAt(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), fuel, grammar, gmarks, input, m, i, j))
    case False{}:
      closedTri(Bool.and(R.closedAll(segs, fuel, grammar, gmarks, input, segs), R.hasSeg(m, i, 0n, i, segs)))

def rootTri(t: Guard.Tri, +found: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat, +e: Nat, +segs: +List<R.Seg>) -> Guard.Tri:
  match t:
    case Guard.Yes{}:
      foundTri(found, fuel, grammar, gmarks, input, m, i, j, e, segs)
    case Guard.No{}:
      Guard.Yes{}
    case Guard.Unknown{}:
      Guard.Unknown{}

# Is there a rival of m over i .. j? It ends at e, after the tokens there. Yes when m's one
# step of an empty right side is answered No, or the closed segments from m at i do not
# complete m; No with a certificate from the segments' forest.
def rivalTri(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat) -> Guard.Tri:
  +e = Nat.add(i, List.length(&2, Nat, Lemma.slice(input, i, Nat.sub(j, i))))
  +segs = R.segsFrom(fuel, grammar, gmarks, input, m, i)
  rootTri(R.endTri(Core.rhsOf(grammar, m), fuel, grammar, gmarks, input, m, i, e), R.hasSeg(m, i, List.length(&2, Core.Sym, Core.rhsOf(grammar, m)), e, segs), fuel, grammar, gmarks, input, m, i, j, e, segs)

def candTri(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat, +j: Nat) -> Guard.Tri:
  match b:
    case False{}:
      Guard.Yes{}
    case True{}:
      rivalTri(fuel, grammar, gmarks, input, m, i, j)

def candsFrom(prods: +List<Core.Production>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<RankMark>, +input: +List<Nat>, +q: Nat, +m: Nat, +i: Nat, +j: Nat) -> Guard.Tri:
  match prods:
    case Nil{}:
      Guard.Yes{}
    case Con{p, rest}:
      Guard.andTri(candTri(outranking(grammar, rmarks, q, m), fuel, grammar, gmarks, input, m, i, j), candsFrom(rest, fuel, grammar, gmarks, rmarks, input, q, 1n+m, i, j))

# Yes: the step is free; No: it completes a beaten node.
def rankTri(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<RankMark>, +input: +List<Nat>, x: Core.Bsr) -> Guard.Tri:
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      Guard.only(Nat.is_eq(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), candsFrom(grammar, fuel, grammar, gmarks, rmarks, input, q, 0n, i, j))

# ======== THE RULE: NO PREFERENCE CYCLE ========
#
# NO PREFERENCE CYCLE. A production of A reaches nonterminal B when one of its items is B
# and every other item can read nothing. A cycle that reads no input is a path of such
# steps from a nonterminal back to itself. A production that outranks a sibling (Preferred
# over Plain or Avoided, Plain over Avoided) lies on no such cycle: it would be a rival
# that only comes back to where it competes, over the same tokens.
#
# Decided with closed sets, each grown (not trusted) and then checked closed: the
# nonterminals that can read nothing, and, for each outranking production, the
# nonterminals it reaches.

def ntList(s: Core.Sym) -> +List<Nat>:
  match s:
    case Core.Terminal{k}:
      []
    case Core.Nonterminal{+x, need}:
      [x]

def edgeIf(b: Bool, s: Core.Sym) -> +List<Nat>:
  match b:
    case True{}:
      ntList(s)
    case False{}:
      []

# The nonterminals a right side reaches: its items whose other items can all read nothing.
# pre: every item before this one can read nothing.
def edgesFrom(items: +List<Core.Sym>, +pre: Bool, +nulls: +List<Nat>) -> +List<Nat>:
  match items:
    case Nil{}:
      []
    case Con{+s, +rest}:
      Sets.joinNats(edgeIf(Bool.and(pre, Sets.allNull(rest, nulls)), s), edgesFrom(rest, Bool.and(pre, Sets.itemNull(s, nulls)), nulls))

def addAll(xs: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      addAll(rest, Sets.addIf(Bool.not(Sets.natIn(x, acc)), x, acc))

def addAllIf(b: Bool, +xs: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      addAll(xs, acc)
    case False{}:
      acc

def reachOnce(prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match prods:
    case Nil{}:
      acc
    case Con{Core.Production{+lhs, +rhs}, rest}:
      reachOnce(rest, nulls, addAllIf(Sets.natIn(lhs, acc), edgesFrom(rhs, True{}, nulls), acc))

def growReach(n: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      growReach(p, grammar, nulls, reachOnce(grammar, nulls, acc))

def reachClosed(prods: +List<Core.Production>, +nulls: +List<Nat>, +r: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(Bool.or(Bool.not(Sets.natIn(lhs, r)), Sets.allNatIn(edgesFrom(rhs, True{}, nulls), r)), reachClosed(rest, nulls, r))

# Production m lies on no cycle that reads no input: r holds what m reaches, is closed, and
# does not hold m's own nonterminal.
def cycleFreeWith(+r: +List<Nat>, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +m: Nat) -> Bool:
  Bool.and(reachClosed(grammar, nulls, r), Bool.and(Sets.allNatIn(edgesFrom(Core.rhsOf(grammar, m), True{}, nulls), r), Bool.not(Sets.natIn(Gll.lhsOf(grammar, m), r))))

def cycleFree(+grammar: +List<Core.Production>, +nulls: +List<Nat>, +m: Nat) -> Bool:
  cycleFreeWith(growReach(1n+List.length(&2, Core.Production, grammar), grammar, nulls, edgesFrom(Core.rhsOf(grammar, m), True{}, nulls)), grammar, nulls, m)

# Does production m outrank a sibling?
def belowFrom(prods: +List<Core.Production>, +grammar: +List<Core.Production>, +marks: +List<RankMark>, +m: Nat, +q: Nat) -> Bool:
  match prods:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Bool.or(outranking(grammar, marks, q, m), belowFrom(rest, grammar, marks, m, 1n+q))

def prodsOk(prods: +List<Core.Production>, +grammar: +List<Core.Production>, +marks: +List<RankMark>, +nulls: +List<Nat>, +m: Nat) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(Bool.or(Bool.not(belowFrom(grammar, grammar, marks, m, 0n)), cycleFree(grammar, nulls, m)), prodsOk(rest, grammar, marks, nulls, 1n+m))

def noCycleWith(+nulls: +List<Nat>, +grammar: +List<Core.Production>, +marks: +List<RankMark>) -> Bool:
  Bool.and(Sets.nullsClosed(grammar, nulls), prodsOk(grammar, grammar, marks, nulls, 0n))

def noPreferenceCycle(+grammar: +List<Core.Production>, +marks: +List<RankMark>) -> Bool:
  noCycleWith(Sets.growNulls(1n+List.length(&2, Core.Production, grammar), grammar, []), grammar, marks)
