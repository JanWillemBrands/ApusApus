import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# PRUNING: keep the steps that a parse tree of the whole input needs.
#
# A segment Seg{q, ks, dot, end} says: in a node of production q started at ks, the items
# before `dot` end at `end`. A step completes the segment of its slot, so it is kept when
# that segment is needed. Needs flow down from the root: a kept step needs the segment
# before it, and, after a nonterminal, every production of it over what it spans.
#
# The needed segments are computed by a loop that is not trusted; `needsClosed` checks
# that every rule adds nothing new, and PROOF_PRUNE.bend shows that a closed set of needs
# keeps every step of every parse tree. (Empty rounds need no rule of their own: the needs of
# the translation's occurrences keep them out of the parser's steps.)

type Seg is Data:
  Seg{q: Nat, ks: Nat, dot: Nat, end: Nat}

def segEq(a: Seg, b: Seg) -> Bool:
  match a b:
    case Seg{q1, s1, d1, e1} Seg{q2, s2, d2, e2}:
      Bool.and(Nat.is_eq(q1, q2), Bool.and(Nat.is_eq(s1, s2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2))))

def segIn(+x: Seg, xs: +List<Seg>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(segEq(x, y), segIn(x, rest))

def allSegsIn(xs: +List<Seg>, +set: +List<Seg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(segIn(x, set), allSegsIn(rest, set))

# The segment a step completes.
def segOf(e: Core.Bsr) -> Seg:
  match e:
    case Core.Bsr{+q, +d, +i, k, +j}:
      Seg{q, i, d, j}

def isKept(+e: Core.Bsr, +needs: +List<Seg>) -> Bool:
  segIn(segOf(e), needs)

def keepPick(k: Bool, +e: Core.Bsr, es: +List<Core.Bsr>) -> +List<Core.Bsr>:
  match k:
    case True{}:
      e <> es
    case False{}:
      es

# The kept steps.
def keep(ys: +List<Core.Bsr>, +needs: +List<Seg>) -> +List<Core.Bsr>:
  match ys:
    case Nil{}:
      []
    case Con{+e, rest}:
      keepPick(isKept(e, needs), e, keep(rest, needs))

def keepSeg(keep: Bool, +s: Seg, ss: +List<Seg>) -> +List<Seg>:
  match keep:
    case True{}:
      s <> ss
    case False{}:
      ss

# ---- What a needed step needs ----

# The whole of every production of x over k .. j.
def prodSegs(grammar: +List<Core.Production>, +x: Nat, +index: Nat, +k: Nat, +j: Nat) -> +List<Seg>:
  match grammar:
    case Nil{}:
      []
    case Con{Core.Production{lhs, +rhs}, rest}:
      keepSeg(Nat.is_eq(lhs, x), Seg{index, k, List.length(&2, Core.Sym, rhs), j}, prodSegs(rest, x, 1n+index, k, j))

def itemNeeds(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +k: Nat, +j: Nat) -> +List<Seg>:
  match item:
    case Some{Core.Nonterminal{+x, need}}:
      prodSegs(grammar, x, 0n, k, j)
    case _:
      []

# A step after item d needs the segment before it and what the item spans.
def stepNeeds(+grammar: +List<Core.Production>, e: Core.Bsr) -> +List<Seg>:
  match e:
    case Core.Bsr{+q, 0n, i, k, j}:
      []
    case Core.Bsr{+q, 1n+(+d), +i, +k, +j}:
      Seg{q, i, d, k} <> itemNeeds(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, k, j)

def rootSegs(+grammar: +List<Core.Production>, +start: Nat, +n: Nat) -> +List<Seg>:
  prodSegs(grammar, start, 0n, 0n, n)

# ---- Closed needs ----

def stepOk(+grammar: +List<Core.Production>, +needs: +List<Seg>, +e: Core.Bsr) -> Bool:
  Bool.or(Bool.not(isKept(e, needs)), allSegsIn(stepNeeds(grammar, e), needs))

def allStepsOk(ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +needs: +List<Seg>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(stepOk(grammar, needs, e), allStepsOk(rest, grammar, needs))

def needsClosed(+grammar: +List<Core.Production>, +start: Nat, +n: Nat, +ys: +List<Core.Bsr>, +needs: +List<Seg>) -> Bool:
  Bool.and(allSegsIn(rootSegs(grammar, start, n), needs), allStepsOk(ys, grammar, needs))

# ---- Computing the needs (not trusted) ----

type NeedState is Data:
  NeedState{seen: +List<Seg>, todo: +List<Seg>}

def addIf(known: Bool, +x: Seg, +xs: +List<Seg>) -> +List<Seg>:
  match known:
    case True{}:
      xs
    case False{}:
      x <> xs

def addSegs(xs: +List<Seg>, +seen: +List<Seg>, +todo: +List<Seg>) -> NeedState:
  match xs:
    case Nil{}:
      NeedState{seen, todo}
    case Con{+x, rest}:
      addSegs(rest, addIf(segIn(x, seen), x, seen), addIf(segIn(x, seen), x, todo))

def stepPick(hit: Bool, +grammar: +List<Core.Production>, +e: Core.Bsr) -> +List<Seg>:
  match hit:
    case True{}:
      stepNeeds(grammar, e)
    case False{}:
      []

# What one needed segment needs: the needs of the steps that complete it.
def segNeeds(ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, +seg: Seg) -> +List<Seg>:
  match ys:
    case Nil{}:
      []
    case Con{+e, rest}:
      List.append(&2, Seg, stepPick(segEq(segOf(e), seg), grammar, e), segNeeds(rest, grammar, seg))

def needLoop(fuel: Nat, +ys: +List<Core.Bsr>, +grammar: +List<Core.Production>, s: NeedState) -> Maybe<&2, +List<Seg>>:
  match fuel s:
    case 0n _:
      None{}
    case 1n+f NeedState{seen, Nil{}}:
      Some{seen}
    case 1n+f NeedState{+seen, Con{+seg, rest}}:
      needLoop(f, ys, grammar, addSegs(segNeeds(ys, grammar, seg), seen, rest))

def needsOf(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +n: Nat, +ys: +List<Core.Bsr>) -> Maybe<&2, +List<Seg>>:
  needLoop(fuel, ys, grammar, addSegs(rootSegs(grammar, start, n), [], []))

# ---- The pruned steps of the checked parser ----

def prunePick(ok: Bool, +ys: +List<Core.Bsr>, +ns: +List<Seg>) -> Maybe<&2, +List<Core.Bsr>>:
  match ok:
    case True{}:
      Some{keep(ys, ns)}
    case False{}:
      None{}

def pruneChecked(needs: Maybe<&2, +List<Seg>>, +grammar: +List<Core.Production>, +start: Nat, +n: Nat, +ys: +List<Core.Bsr>) -> Maybe<&2, +List<Core.Bsr>>:
  match needs:
    case Some{+ns}:
      prunePick(needsClosed(grammar, start, n, ys, ns), ys, ns)
    case None{}:
      None{}

def pruneSteps(found: Maybe<&2, +List<Core.Bsr>>, fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+ys}:
      +n = List.length(&2, Nat, input)
      pruneChecked(needsOf(fuel, grammar, start, n, ys), grammar, start, n, ys)
    case None{}:
      None{}

def prunedSteps(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  +f = fuel
  pruneSteps(Check.checkedSteps(f, grammar, start, input), f, grammar, start, input)
