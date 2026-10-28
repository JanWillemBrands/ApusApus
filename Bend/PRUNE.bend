import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# PRUNING: keep the steps that a parse tree of the whole input needs.
#
# It runs on the checked parser's steps after the round rule (below) has removed the
# rounds that read nothing.
# A segment Seg{index, rpath, ctx, dot, end} says: in the sequence at (index, rpath),
# started at ctx, everything before the dot ends at `end`. A step completes the
# segment of its slot, so it is kept when that segment is needed. Needs flow down
# from the root: a kept step needs the segment before it and what its item spans
# (a nonterminal's productions, a bracket's alternatives); a round of a loop that
# starts after the loop's start needs the round before it to have ended there.
#
# The needed segments are computed by a loop that is not trusted; `needsClosed`
# checks that every rule adds nothing new, and PROOF_PRUNE.bend shows that a closed
# set of needs keeps every step of every parse tree.

type Seg is Data:
  Seg{index: Nat, rpath: +List<Nat>, ctx: Nat, dot: Nat, end: Nat}

def segEq(a: Seg, b: Seg) -> Bool:
  match a b:
    case Seg{p1, r1, c1, d1, e1} Seg{p2, r2, c2, d2, e2}:
      Bool.and(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2)))))

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

# ---- The segment of a step ----

def segFrom(rev: +List<Nat>, +index: Nat, +i: Nat, +j: Nat) -> Maybe<&2, Seg>:
  match rev:
    case Con{d, rp}:
      Some{Seg{index, rp, i, d, j}}
    case Nil{}:
      None{}

def segOf(e: Spec.Bsr) -> Maybe<&2, Seg>:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, +i, k, +j}:
      segFrom(Gll.reverseOnto(path, []), index, i, j)

def keptBy(seg: Maybe<&2, Seg>, +needs: +List<Seg>) -> Bool:
  match seg:
    case Some{+x}:
      segIn(x, needs)
    case None{}:
      False{}

def isKept(+e: Spec.Bsr, +needs: +List<Seg>) -> Bool:
  keptBy(segOf(e), needs)

def keepPick(k: Bool, +e: Spec.Bsr, es: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match k:
    case True{}:
      e <> es
    case False{}:
      es


# The kept steps.
def keep(ys: +List<Spec.Bsr>, +needs: +List<Seg>) -> +List<Spec.Bsr>:
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

# The segments for every production of x over k .. j.
def prodSegs(grammar: +List<Spec.Production>, +x: Nat, +index: Nat, +k: Nat, +j: Nat) -> +List<Seg>:
  match grammar:
    case Nil{}:
      []
    case Con{Spec.Production{lhs, +rhs}, rest}:
      keepSeg(Nat.is_eq(lhs, x), Seg{index, [], k, List.length(&2, Spec.Item, rhs), j}, prodSegs(rest, x, 1n+index, k, j))

# The segments for every alternative of the bracket at (index, rpath), counting down from n.
def altSegs(n: Nat, +alts: +List<+List<Spec.Item>>, +index: Nat, +rpath: +List<Nat>, +k: Nat, +j: Nat) -> +List<Seg>:
  match n:
    case 0n:
      []
    case 1n+(+a):
      Seg{index, a <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j} <> altSegs(a, alts, index, rpath, k, j)

# A [ ] that reads nothing is the skip: a parse tree has no pick of it over nothing
# (SPEC.bend, roundsOk), so there its alternatives are not needed. Every other
# bracket needs its alternatives over what it spans.
def bracketNeeds(kind: Spec.Bracket, +k: Nat, +j: Nat) -> Bool:
  match kind:
    case Spec.Group{}:
      True{}
    case Spec.Optional{}:
      Nat.is_lt(k, j)
    case Spec.Closure{}:
      True{}
    case Spec.Positive{}:
      True{}

def segsIf(ok: Bool, +segs: +List<Seg>) -> +List<Seg>:
  match ok:
    case True{}:
      segs
    case False{}:
      []

def itemNeeds(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +index: Nat, +rpath: +List<Nat>, +d: Nat, +k: Nat, +j: Nat) -> +List<Seg>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{t}}}:
      []
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      prodSegs(grammar, x, 0n, k, j)
    case Some{Spec.Brack{kind, +alts}}:
      segsIf(bracketNeeds(kind, k, j), altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, d <> rpath, k, j))
    case Some{Spec.Eps{}}:
      []
    case None{}:
      []

def needsAt(rev: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat, +i: Nat, +k: Nat, +j: Nat) -> +List<Seg>:
  match rev:
    case Con{1n+(+d), +rp}:
      Seg{index, rp, i, d, k} <> itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rp), d), grammar, index, rp, d, k, j)
    case _:
      []

def stepNeeds(+grammar: +List<Spec.Production>, e: Spec.Bsr) -> +List<Seg>:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, +i, +k, +j}:
      needsAt(Gll.reverseOnto(path, []), grammar, index, i, k, j)

def loopEndsPick(loop: Bool, +alts: +List<+List<Spec.Item>>, +index: Nat, +rpath: +List<Nat>, +i: Nat, +s: Nat) -> +List<Seg>:
  match loop:
    case True{}:
      altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, rpath, i, s)
    case False{}:
      []

# A round of a loop that starts at s: the earlier rounds must end at s.
#
# ApusApus's Swift Oracle currently retains transitive closure-prefix yields because
# bracket extent ranking uses them as candidates. Before making this proof and Swift
# agree on their retention, give extent disambiguation an explicit carrier in both.
def loopEnds(item: Maybe<&2, Spec.Item>, +index: Nat, +rpath: +List<Nat>, +i: Nat, +s: Nat) -> +List<Seg>:
  match item:
    case Some{Spec.Brack{+kind, +alts}}:
      loopEndsPick(Gll.isLoop(kind), alts, index, rpath, i, s)
    case _:
      []

def laterRound(later: Bool, item: Maybe<&2, Spec.Item>, +index: Nat, +rpath: +List<Nat>, +i: Nat, +s: Nat) -> +List<Seg>:
  match later:
    case True{}:
      loopEnds(item, index, rpath, i, s)
    case False{}:
      []

# A round of a loop that starts after the loop's start s > i is not the first round,
# so the round before it ended at s. A round that starts at the loop's start is the
# first: a parse tree has no empty round before another round (SPEC.bend, roundsOk).
def roundNeeds(+grammar: +List<Spec.Production>, seg: Seg) -> +List<Seg>:
  match seg:
    case Seg{+index, Con{a, Con{+m, +outer}}, +i, 0n, +s}:
      laterRound(Nat.is_lt(i, s), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), index, m <> outer, i, s)
    case _:
      []

def rootSegs(+grammar: +List<Spec.Production>, +start: Nat, +n: Nat) -> +List<Seg>:
  prodSegs(grammar, start, 0n, 0n, n)

# ---- Closed needs ----

def stepOk(+grammar: +List<Spec.Production>, +needs: +List<Seg>, +e: Spec.Bsr) -> Bool:
  Bool.or(Bool.not(isKept(e, needs)), allSegsIn(stepNeeds(grammar, e), needs))

def allStepsOk(ys: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +needs: +List<Seg>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(stepOk(grammar, needs, e), allStepsOk(rest, grammar, needs))

def allRoundsOk(ss: +List<Seg>, +grammar: +List<Spec.Production>, +needs: +List<Seg>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+seg, rest}:
      Bool.and(allSegsIn(roundNeeds(grammar, seg), needs), allRoundsOk(rest, grammar, needs))

def needsClosed(+grammar: +List<Spec.Production>, +start: Nat, +n: Nat, +ys: +List<Spec.Bsr>, +needs: +List<Seg>) -> Bool:
  Bool.and(allSegsIn(rootSegs(grammar, start, n), needs), Bool.and(allStepsOk(ys, grammar, needs), allRoundsOk(needs, grammar, needs)))

type NeedState is Data:
  NeedState{seen: +List<Seg>, todo: +List<Seg>}

# ---- Computing the needs (not trusted) ----

def segMatch(m: Maybe<&2, Seg>, +seg: Seg) -> Bool:
  match m:
    case Some{x}:
      segEq(x, seg)
    case None{}:
      False{}

def stepPick(hit: Bool, +grammar: +List<Spec.Production>, +e: Spec.Bsr) -> +List<Seg>:
  match hit:
    case True{}:
      stepNeeds(grammar, e)
    case False{}:
      []

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

# What one needed segment needs: the needs of its kept steps, and its rounds' needs.
def segNeeds(ys: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +seg: Seg) -> +List<Seg>:
  match ys:
    case Nil{}:
      roundNeeds(grammar, seg)
    case Con{+e, rest}:
      List.append(&2, Seg, stepPick(segMatch(segOf(e), seg), grammar, e), segNeeds(rest, grammar, seg))

def needLoop(fuel: Nat, +ys: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, s: NeedState) -> Maybe<&2, +List<Seg>>:
  match fuel s:
    case 0n _:
      None{}
    case 1n+f NeedState{seen, Nil{}}:
      Some{seen}
    case 1n+f NeedState{+seen, Con{+seg, rest}}:
      needLoop(f, ys, grammar, addSegs(segNeeds(ys, grammar, seg), seen, rest))

def needsOf(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +n: Nat, +ys: +List<Spec.Bsr>) -> Maybe<&2, +List<Seg>>:
  needLoop(fuel, ys, grammar, addSegs(rootSegs(grammar, start, n), [], []))

def prunePick(ok: Bool, +ys: +List<Spec.Bsr>, +ns: +List<Seg>) -> Maybe<&2, +List<Spec.Bsr>>:
  match ok:
    case True{}:
      Some{keep(ys, ns)}
    case False{}:
      None{}
# ---- The round rule ----
#
# A loop is written { ( τ ) } (SPEC.bend, the step convention): its one alternative is a
# group, so each round is one item. The step after that item, the round's link step,
# records the loop's start c, the round's start s and the round's end e. A parse tree
# has no removable empty round (SPEC.bend, roundsOk): a round reads something (s < e),
# or it is the one round of a < > over nothing (s = e = c). The rule drops the link
# steps of other rounds; pruning then drops what only they needed. Other steps pass.

def isPositive(kind: Spec.Bracket) -> Bool:
  match kind:
    case Spec.Positive{}:
      True{}
    case _:
      False{}

def roundOk(kind: Spec.Bracket, +c: Nat, +s: Nat, +e: Nat) -> Bool:
  Bool.or(Nat.is_lt(s, e), Bool.and(isPositive(kind), Bool.and(Nat.is_eq(s, c), Nat.is_eq(e, c))))

# The step after the only item of alternative a of a loop is a link step.
def linkItem(item: Maybe<&2, Spec.Item>, +a: Nat, +c: Nat, +s: Nat, +e: Nat) -> Bool:
  match item:
    case Some{Spec.Brack{+kind, +alts}}:
      Bool.or(Bool.not(Bool.and(Gll.isLoop(kind), Nat.is_eq(List.length(&2, Spec.Item, Spec.altOf(alts, a)), 1n))), roundOk(kind, c, s, e))
    case Some{Spec.Sym{x}}:
      True{}
    case Some{Spec.Eps{}}:
      True{}
    case None{}:
      True{}

# The path of the step's sequence, innermost first: alternative a of the bracket at m.
def linkRest(rest: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat, +c: Nat, +s: Nat, +e: Nat) -> Bool:
  match rest:
    case Con{+a, Con{+m, +outer}}:
      linkItem(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a, c, s, e)
    case Con{a, Nil{}}:
      True{}
    case Nil{}:
      True{}

# A step at dot d: only a step at dot 1 can be a link step.
def linkAt(rev: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat, +c: Nat, +s: Nat, +e: Nat) -> Bool:
  match rev:
    case Con{d, +rest}:
      Bool.or(Bool.not(Nat.is_eq(d, 1n)), linkRest(rest, grammar, index, c, s, e))
    case Nil{}:
      True{}

def linkOk(+grammar: +List<Spec.Production>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, +i, +k, +j}:
      linkAt(Gll.reverseOnto(path, []), grammar, index, i, k, j)

def keepLinks(ys: +List<Spec.Bsr>, +grammar: +List<Spec.Production>) -> +List<Spec.Bsr>:
  match ys:
    case Nil{}:
      []
    case Con{+e, rest}:
      keepPick(linkOk(grammar, e), e, keepLinks(rest, grammar))

def roundRule(found: Maybe<&2, +List<Spec.Bsr>>, +grammar: +List<Spec.Production>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+ys}:
      Some{keepLinks(ys, grammar)}
    case None{}:
      None{}

# ---- The pruned steps of the checked parser ----

def pruneChecked(needs: Maybe<&2, +List<Seg>>, +grammar: +List<Spec.Production>, +start: Nat, +n: Nat, +ys: +List<Spec.Bsr>) -> Maybe<&2, +List<Spec.Bsr>>:
  match needs:
    case Some{+ns}:
      prunePick(needsClosed(grammar, start, n, ys, ns), ys, ns)
    case None{}:
      None{}

def pruneSteps(found: Maybe<&2, +List<Spec.Bsr>>, fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+ys}:
      +n = List.length(&2, Nat, input)
      pruneChecked(needsOf(fuel, grammar, start, n, ys), grammar, start, n, ys)
    case None{}:
      None{}

def prunedSteps(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  +g = grammar
  pruneSteps(roundRule(Check.checkedSteps(f, g, start, input), g), f, g, start, input)
