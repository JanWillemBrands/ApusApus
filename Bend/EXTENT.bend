import Base
import ./SYNTAX.bend as Spec
import ./CORE.bend as Core
import ./EBNF.bend as E
import ./EXACT.bend as Exact
import ./WITNESS.bend as Witness
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle

# PHASE 3 ON THE CORE: @longest AND @shortest.
#
# A mark asks for the longest or shortest reading of an item: of one item of a production
# (a bracket's mark sits on the item of its nonterminal), or of every item that is a given
# nonterminal. A reading of production q from i is where its items end, k_1 .. k_n; its
# steps are q's own steps along those ends, and each must lie on some tree that phases 1
# and 2 keep (the reading may be stitched from steps of different such trees). A step of q
# is out when it stands on a reading that ends at some e, and another reading that ends at
# e reads q's marked items better: the same on every marked item before the step's item,
# and better (longer, shorter) on the step's item. A tree is selected when phases 1 and 2
# keep it and none of its steps is out.

# ======== THE MEANING ========

# @longest or @shortest.
type Extent is Data:
  Longest{}
  Shortest{}

# ItemExtent: the item before dot `dot` of production `index`. NtExtent: every item that is
# nonterminal x.
type ExtentMark is Data:
  ItemExtent{index: Nat, dot: Nat, ext: Extent}
  NtExtent{x: Nat, ext: Extent}

def extentIf(hit: Bool, +e: Extent) -> Maybe<&2, Extent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      None{}

def orExtent(found: Maybe<&2, Extent>, +later: Maybe<&2, Extent>) -> Maybe<&2, Extent>:
  match found:
    case Some{+e}:
      Some{e}
    case None{}:
      later

# The mark's extent, if it marks the item before dot d of production q.
def extentHit(m: ExtentMark, +grammar: +List<Core.Production>, +q: Nat, +d: Nat) -> Maybe<&2, Extent>:
  match m:
    case ItemExtent{p, e, +ext}:
      extentIf(Bool.and(Nat.is_eq(p, q), Nat.is_eq(e, d)), ext)
    case NtExtent{x, +ext}:
      extentIf(Prefer.isNt(Prefer.before(Core.rhsOf(grammar, q), d), x), ext)

# What is asked of the item before dot d of production q: the first mark for it.
def extentOf(marks: +List<ExtentMark>, +grammar: +List<Core.Production>, +q: Nat, +d: Nat) -> Maybe<&2, Extent>:
  match marks:
    case Nil{}:
      None{}
    case Con{+m, rest}:
      orExtent(extentHit(m, grammar, q, d), extentOf(rest, grammar, q, d))

# Is length a better than length b: longer for @longest, shorter for @shortest?
def better(e: Extent, +a: Nat, +b: Nat) -> Bool:
  match e:
    case Longest{}:
      Nat.is_lt(b, a)
    case Shortest{}:
      Nat.is_lt(a, b)

# Better, if the item is marked; never better if it is not.
def betterOpt(m: Maybe<&2, Extent>, +a: Nat, +b: Nat) -> Bool:
  match m:
    case Some{+e}:
      better(e, a, b)
    case None{}:
      False{}

# The same length, if the item is marked; unmarked items need not agree.
def sameOpt(m: Maybe<&2, Extent>, +a: Nat, +b: Nat) -> Bool:
  match m:
    case Some{e}:
      Nat.is_eq(a, b)
    case None{}:
      True{}

# One item of the comparison in beatsAt: better here, or the same here and better later.
def compareAt(here: Bool, +m: Maybe<&2, Extent>, +w1: Nat, +w2: Nat, later: Bool) -> Bool:
  match here:
    case True{}:
      betterOpt(m, w2, w1)
    case False{}:
      Bool.and(sameOpt(m, w1, w2), later)

# The reading ks2 beats ks1 at the item before dot d: the same on each marked item before
# it, better on it. prev1, prev2: where the item after dot p starts. (The lists come first
# because Bend checks that a recursion shrinks its first argument.)
def beatsAt(ks1: +List<Nat>, ks2: +List<Nat>, +marks: +List<ExtentMark>, +grammar: +List<Core.Production>, +q: Nat, +d: Nat, +p: Nat, +prev1: Nat, +prev2: Nat) -> Bool:
  match ks1:
    case Nil{}:
      False{}
    case Con{+a, r1}:
      match ks2:
        case Nil{}:
          False{}
        case Con{+b, r2}:
          compareAt(Nat.is_eq(1n+p, d), extentOf(marks, grammar, q, 1n+p), Nat.sub(a, prev1), Nat.sub(b, prev2), beatsAt(r1, r2, marks, grammar, q, d, 1n+p, a, b))

# q's own steps along the ends ks, from dot p, the item after dot p starting at prev.
def ownOf(ks: +List<Nat>, +q: Nat, +i: Nat, +p: Nat, +prev: Nat) -> +List<Core.Bsr>:
  match ks:
    case Nil{}:
      []
    case Con{+k, rest}:
      Core.Bsr{q, 1n+p, i, prev, k} <> ownOf(rest, q, i, 1n+p, k)

# The steps of a reading of q from i; an empty right side has its one step.
def stepsOf(+q: Nat, +i: Nat, ks: +List<Nat>) -> +List<Core.Bsr>:
  match ks:
    case Nil{}:
      [Core.Bsr{q, 0n, i, i, i}]
    case Con{+k, +rest}:
      ownOf(k <> rest, q, i, 0n, i)

# Where a reading ends: its last item's end (prev for an empty right side).
def endOf(ks: +List<Nat>, +prev: Nat) -> Nat:
  match ks:
    case Nil{}:
      prev
    case Con{+k, rest}:
      endOf(rest, k)

# A step of some tree that phases 1 and 2 keep.
def ChosenStep(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr) -> Type:
  &tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) & Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) & {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}

# Every step in the list lies on some tree that phases 1 and 2 keep.
def AllChosen(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, xs: +List<Core.Bsr>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      ChosenStep(grammar, gmarks, rmarks, start, input, x) & AllChosen(grammar, gmarks, rmarks, start, input, rest)

# A reading of q from i: one end per item, and all its steps lie on trees phases 1 and 2 keep.
def Reading(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +q: Nat, +i: Nat, +ks: +List<Nat>) -> Type:
  {List.length(&2, Nat, ks) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat} & AllChosen(grammar, gmarks, rmarks, start, input, stepsOf(q, i, ks))

# A step is out: it stands on a reading ks1 of its production, and another reading ks2
# to the same end beats ks1 at the step's item.
def Out(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<ExtentMark>, +start: Nat, +input: +List<Nat>, x: Core.Bsr) -> Type:
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      &ks1: +List<Nat> -> &ks2: +List<Nat> -> Reading(grammar, gmarks, rmarks, start, input, q, i, ks1) & Reading(grammar, gmarks, rmarks, start, input, q, i, ks2) &
        {endOf(ks1, i) == endOf(ks2, i) : Nat} & {Core.member(Core.Bsr{q, d, i, k, j}, stepsOf(q, i, ks1)) == True{} : Bool} & {beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i) == True{} : Bool}

# No step in the list is out.
def AllBest(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<ExtentMark>, +start: Nat, +input: +List<Nat>, xs: +List<Core.Bsr>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      (Out(grammar, gmarks, rmarks, emarks, start, input, x) -> Empty) & AllBest(grammar, gmarks, rmarks, emarks, start, input, rest)

# A selected tree: phases 1 and 2 keep it, and none of its steps is out.
def Selected(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<ExtentMark>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree) -> Type:
  Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) & AllBest(grammar, gmarks, rmarks, emarks, start, input, Core.steps([tree], 0n))

# A set that embeds exactly the selected trees: a parse tree of the input uses only steps of
# the set when, and only when, it is selected. (The set may hold other steps too.)
def EmbedsSelected(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Type:
  @tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) ->
    ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Selected(grammar, gmarks, rmarks, emarks, start, input, tree)) &
    (Selected(grammar, gmarks, rmarks, emarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool})

# ======== THE MARKS AS WRITTEN, ON THE CORE ========

def extentFrom(e: Spec.Extent) -> Extent:
  match e:
    case Spec.Longest{}:
      Longest{}
    case Spec.Shortest{}:
      Shortest{}

# xs reversed, then acc.
def revOnto(xs: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      revOnto(rest, x <> acc)

def headOr(xs: +List<Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{+x, rest}:
      x

def tailOf(xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      []
    case Con{x, +rest}:
      rest

def itemAt(m: Maybe<&2, Nat>, +dot: Nat, +e: Spec.Extent, +rest: +List<ExtentMark>) -> +List<ExtentMark>:
  match m:
    case Some{+q}:
      ItemExtent{q, dot, extentFrom(e)} <> rest
    case None{}:
      rest

# A mark on nonterminal x stays on x; a mark on the bracket at (index, prefix ++ [m]) moves
# to item m of the production whose origin is the sequence at (index, prefix).
def extentMarksOf(ms: +List<Spec.ExtentMark>, +origins: +List<E.Origin>) -> +List<ExtentMark>:
  match ms:
    case Nil{}:
      []
    case Con{Spec.NtExtent{+x, +e}, rest}:
      NtExtent{x, extentFrom(e)} <> extentMarksOf(rest, origins)
    case Con{Spec.BrackExtent{+index, +path, +e}, rest}:
      +rev = revOnto(path, [])
      itemAt(Guard.productionAt(origins, index, revOnto(tailOf(rev), []), 0n), 1n+headOr(rev, 0n), e, extentMarksOf(rest, origins))

# ======== THE CHOSEN SET, EXACTLY ========
#
# The oracle's set without its dead wood, handed out only with checked witnesses: every step
# lies on a parse tree all of whose steps are in the set, so (by oracle_exact) on a chosen tree.

def treeIn(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +t: Core.Tree) -> Bool:
  Bool.and(Exact.treeOk(grammar, start, input, t), Core.allIn(Core.steps([t], 0n), set))

def allTreesIn(ws: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+t, rest}:
      Bool.and(treeIn(grammar, start, input, set, t), allTreesIn(rest, grammar, start, input, set))

def coverFrom(found: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+set}:
      +ws = Witness.witnesses(fuel, grammar, start, input, set)
      Exact.exactPick(Bool.and(allTreesIn(ws, grammar, start, input, set), Exact.allCovered(set, ws)), set)
    case None{}:
      None{}

# The oracle's set may hold dead wood: steps on no parse tree all of whose steps are in the
# set (a rule rejects a later step of the same node). One pass over the set keeps the trees
# found so far: a step on one of them is live without a search; for another step the
# witness search inside the set runs once, and the step stays when it finds a tree (which
# joins the others), is dropped when its facts are closed (so no such tree exists,
# `root_found`), and otherwise there is no answer (fuel).
def hasRoot(m: Maybe<&2, +List<Core.Tree>>) -> Bool:
  match m:
    case Some{ts}:
      True{}
    case None{}:
      False{}

# What the pass hands out: whether every dropped step had closed facts, the live steps, and
# the trees found.
type Live is Data:
  Live{ok: Bool, kept: +List<Core.Bsr>, trees: +List<Core.Tree>}

# The witness facts for x, unless x is covered already.
def searchIf(covered: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr) -> +List<Witness.Fact>:
  match covered:
    case True{}:
      []
    case False{}:
      Witness.fixpoint(fuel, set, grammar, input, x, [])

def rootIf(covered: Bool, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +facts: +List<Witness.Fact>) -> Maybe<&2, +List<Core.Tree>>:
  match covered:
    case True{}:
      None{}
    case False{}:
      Witness.rootFor(grammar, grammar, x, 0n, start, List.length(&2, Nat, input), facts)

def liveCons(keep: Bool, closed: Bool, +x: Core.Bsr, +out: Live) -> Live:
  match keep:
    case True{}:
      match out:
        case Live{+ok, +kept, +trees}:
          Live{ok, x <> kept, trees}
    case False{}:
      match out:
        case Live{+ok, +kept, +trees}:
          Live{Bool.and(closed, ok), kept, trees}

def liveRun(xs: +List<Core.Bsr>, +ws: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Live:
  match xs:
    case Nil{}:
      Live{True{}, [], ws}
    case Con{+x, +rest}:
      +cov = Witness.coveredBy(x, ws)
      +facts = searchIf(cov, fuel, grammar, input, set, x)
      +r = rootIf(cov, grammar, start, input, x, facts)
      liveCons(Bool.or(cov, hasRoot(r)), Witness.closedW(set, grammar, input, x, facts), x, liveRun(rest, Witness.addWitness(r, ws), fuel, grammar, start, input, set))

def okPick(ok: Bool, +kept: +List<Core.Bsr>) -> Maybe<&2, +List<Core.Bsr>>:
  match ok:
    case True{}:
      Some{kept}
    case False{}:
      None{}

def livePick(out: Live) -> Maybe<&2, +List<Core.Bsr>>:
  match out:
    case Live{+ok, +kept, trees}:
      okPick(ok, kept)

def liveFrom(found: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+set}:
      livePick(liveRun(set, [], fuel, grammar, start, input, set))
    case None{}:
      None{}

def chosenSteps(fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  +f = fuel
  coverFrom(liveFrom(Oracle.oracleSteps(f, grammar, gmarks, rmarks, start, input), f, grammar, start, input), f, grammar, start, input)

# ======== THE READINGS IN THE SET ========
#
# All readings of q from i whose steps are in the set, found item by item; each is kept
# with its ends reversed.

def prevOf(+i: Nat, rev: +List<Nat>) -> Nat:
  match rev:
    case Nil{}:
      i
    case Con{+k, rest}:
      k

def fitsStep(+q: Nat, +p: Nat, +i: Nat, +prev: Nat, x: Core.Bsr) -> Bool:
  match x:
    case Core.Bsr{q2, d2, i2, k2, j2}:
      Bool.and(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(d2, 1n+p), Bool.and(Nat.is_eq(i2, i), Nat.is_eq(k2, prev))))

def stepEnd(x: Core.Bsr) -> Nat:
  match x:
    case Core.Bsr{q, d, i, k, +j}:
      j

def addPath(b: Bool, +path: +List<Nat>, +rest: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match b:
    case True{}:
      path <> rest
    case False{}:
      rest

def joinPaths(a: +List<+List<Nat>>, +b: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match a:
    case Nil{}:
      b
    case Con{+x, rest}:
      x <> joinPaths(rest, b)

def growOne(xs: +List<Core.Bsr>, +q: Nat, +p: Nat, +i: Nat, +rev: +List<Nat>) -> +List<+List<Nat>>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      addPath(fitsStep(q, p, i, prevOf(i, rev), x), stepEnd(x) <> rev, growOne(rest, q, p, i, rev))

def expand(states: +List<+List<Nat>>, +set: +List<Core.Bsr>, +q: Nat, +p: Nat, +i: Nat) -> +List<+List<Nat>>:
  match states:
    case Nil{}:
      []
    case Con{+rev, rest}:
      joinPaths(growOne(set, q, p, i, rev), expand(rest, set, q, p, i))

def run(items: +List<Core.Sym>, +set: +List<Core.Bsr>, +q: Nat, +p: Nat, +i: Nat, +states: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match items:
    case Nil{}:
      states
    case Con{it, rest}:
      run(rest, set, q, 1n+p, i, expand(states, set, q, p, i))

def chains(+set: +List<Core.Bsr>, +grammar: +List<Core.Production>, +q: Nat, +i: Nat) -> +List<+List<Nat>>:
  run(Core.rhsOf(grammar, q), set, q, 0n, i, [[]])

# ======== THE VERDICT ON A STEP ========

def readingIn(+grammar: +List<Core.Production>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +ks: +List<Nat>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, Nat, ks), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Core.allIn(stepsOf(q, i, ks), set))

def pairOk(+grammar: +List<Core.Production>, +emarks: +List<ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>, +ks2: +List<Nat>) -> Bool:
  Bool.and(readingIn(grammar, set, q, i, ks1), Bool.and(readingIn(grammar, set, q, i, ks2),
    Bool.and(Nat.is_eq(endOf(ks1, i), endOf(ks2, i)), Bool.and(Core.member(Core.Bsr{q, d, i, k, j}, stepsOf(q, i, ks1)), beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i)))))

def anyWith(cs: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+r2, rest}:
      Bool.or(pairOk(grammar, emarks, set, q, d, i, k, j, ks1, revOnto(r2, [])), anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1))

def anyPair(cs: +List<+List<Nat>>, +all: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+r1, rest}:
      Bool.or(anyWith(all, grammar, emarks, set, q, d, i, k, j, revOnto(r1, [])), anyPair(rest, all, grammar, emarks, set, q, d, i, k, j))

# Is the step out? Decided exactly: the readings in the chosen set are the readings.
def beaten(+grammar: +List<Core.Production>, +emarks: +List<ExtentMark>, +set: +List<Core.Bsr>, x: Core.Bsr) -> Bool:
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      +cs = chains(set, grammar, q, i)
      anyPair(cs, cs, grammar, emarks, set, q, d, i, k, j)

def keepBest(xs: +List<Core.Bsr>, +grammar: +List<Core.Production>, +emarks: +List<ExtentMark>, +set: +List<Core.Bsr>) -> +List<Core.Bsr>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      Oracle.keepIf(Bool.not(beaten(grammar, emarks, set, x)), x, keepBest(rest, grammar, emarks, set))

def selectFrom(found: Maybe<&2, +List<Core.Bsr>>, +grammar: +List<Core.Production>, +emarks: +List<ExtentMark>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+set}:
      Some{keepBest(set, grammar, emarks, set)}
    case None{}:
      None{}

# THE SELECTING ORACLE: the chosen set without the steps that are out.
def selectedSteps(fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<ExtentMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  selectFrom(chosenSteps(fuel, grammar, gmarks, rmarks, start, input), grammar, emarks)
