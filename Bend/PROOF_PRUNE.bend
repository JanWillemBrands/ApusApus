import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./PROOF_GLL.bend as G
import ./LEMMAS.bend as Lemma
import ./FITS.bend as Fits
import ./PROOF_ROUNDS.bend as R

# PRUNING KEEPS EVERY STEP OF EVERY PARSE TREE.
#
# The proof walks a parse tree like PROOF_GLL.bend does, but from the right: the need
# at the end of a sequence gives, through a kept step, the need before that step and
# the needs of what its item spans. A loop's rounds are walked from the last one back;
# each round's start needs the earlier rounds to have ended there.

# ---- Paths: a step's segment ----

law kept_at:
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +needs: +List<Prune.Seg>
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for inN: {Prune.segIn(Prune.Seg{index, rpath, i, d, j}, needs) == True{} : Bool}
  {Prune.isKept(Spec.at(index, prefix, d, i, k, j), needs) == True{} : Bool}

def kept_at(index, rpath, prefix, d, i, k, j, needs, pEq, inN):
  %Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), []), d <> rpath, R.step_rev(rpath, prefix, d, pEq)) : {Prune.keptBy(Prune.segFrom(_, index, i, j), needs) == True{} : Bool}
  inN

law needs_at:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  {Prune.stepNeeds(grammar, Spec.at(index, prefix, 1n+d, i, k, j)) == Prune.Seg{index, rpath, i, d, k} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), d), grammar, index, rpath, d, k, j) : +List<Prune.Seg>}

def needs_at(grammar, index, rpath, prefix, d, i, k, j, pEq):
  %Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+d]), []), (1n+d) <> rpath, R.step_rev(rpath, prefix, 1n+d, pEq)) : {Prune.needsAt(_, grammar, index, i, k, j) == Prune.Seg{index, rpath, i, d, k} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), d), grammar, index, rpath, d, k, j) : +List<Prune.Seg>}
  {==}

# ---- Equal by ==, so equal ----

law seg_eq_sound:
  for a: Prune.Seg
  for b: Prune.Seg
  for e: {Prune.segEq(a, b) == True{} : Bool}
  {a == b : Prune.Seg}

def seg_eq_sound(a, b, e):
  match a b:
    case Prune.Seg{+p1, +r1, +c1, +d1, +e1} Prune.Seg{+p2, +r2, +c2, +d2, +e2}:
      +s0 = e
      +s1 = Lemma.and_true_right_side(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2)))), s0)
      +s2 = Lemma.and_true_right_side(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2))), s1)
      +s3 = Lemma.and_true_right_side(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2)), s2)
      ep = Lemma.nat_eq_sound(p1, p2, Lemma.and_true_left(Nat.is_eq(p1, p2), Bool.and(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2)))), s0))
      er = G.nats_eq_sound(r1, r2, Lemma.and_true_left(Gll.natsEq(r1, r2), Bool.and(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2))), s1))
      ec = Lemma.nat_eq_sound(c1, c2, Lemma.and_true_left(Nat.is_eq(c1, c2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2)), s2))
      ed = Lemma.nat_eq_sound(d1, d2, Lemma.and_true_left(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2), s3))
      ee = Lemma.nat_eq_sound(e1, e2, Lemma.and_true_right_side(Nat.is_eq(d1, d2), Nat.is_eq(e1, e2), s3))
      %ep : {Prune.Seg{p1, r1, c1, d1, e1} == Prune.Seg{_, r2, c2, d2, e2} : Prune.Seg}
      %er : {Prune.Seg{p1, r1, c1, d1, e1} == Prune.Seg{p1, _, c2, d2, e2} : Prune.Seg}
      %ec : {Prune.Seg{p1, r1, c1, d1, e1} == Prune.Seg{p1, r1, _, d2, e2} : Prune.Seg}
      %ed : {Prune.Seg{p1, r1, c1, d1, e1} == Prune.Seg{p1, r1, c1, _, e2} : Prune.Seg}
      %ee : {Prune.Seg{p1, r1, c1, d1, e1} == Prune.Seg{p1, r1, c1, d1, _} : Prune.Seg}
      {==}

# ---- Lists of segments ----

law segs_head:
  for +x: Prune.Seg
  for +rest: +List<Prune.Seg>
  for +set: +List<Prune.Seg>
  for all: {Prune.allSegsIn(x <> rest, set) == True{} : Bool}
  {Prune.segIn(x, set) == True{} : Bool}

def segs_head(x, rest, set, all):
  Lemma.and_true_left(Prune.segIn(x, set), Prune.allSegsIn(rest, set), all)

law keep_seg_head:
  for keep: Bool
  for +isKept: {keep == True{} : Bool}
  for +x: Prune.Seg
  for +xs: +List<Prune.Seg>
  for +set: +List<Prune.Seg>
  for all: {Prune.allSegsIn(Prune.keepSeg(keep, x, xs), set) == True{} : Bool}
  {Prune.segIn(x, set) == True{} : Bool}

def keep_seg_head(keep, isKept, x, xs, set, all):
  match keep:
    case True{}:
      Lemma.and_true_left(Prune.segIn(x, set), Prune.allSegsIn(xs, set), all)
    case False{}:
      Empty.absurd({Prune.segIn(x, set) == True{} : Bool}, Lemma.false_is_not_true(isKept))

law keep_seg_tail:
  for keep: Bool
  for +x: Prune.Seg
  for +xs: +List<Prune.Seg>
  for +set: +List<Prune.Seg>
  for all: {Prune.allSegsIn(Prune.keepSeg(keep, x, xs), set) == True{} : Bool}
  {Prune.allSegsIn(xs, set) == True{} : Bool}

def keep_seg_tail(keep, x, xs, set, all):
  match keep:
    case True{}:
      Lemma.and_true_right_side(Prune.segIn(x, set), Prune.allSegsIn(xs, set), all)
    case False{}:
      all

# The segment of production q of x, when all of x's productions are needed.
law prod_seg_in:
  for grammar: +List<Spec.Production>
  for +x: Nat
  for +o: Nat
  for +k: Nat
  for +j: Nat
  for q: Nat
  for +set: +List<Prune.Seg>
  for lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for all: {Prune.allSegsIn(Prune.prodSegs(grammar, x, o, k, j), set) == True{} : Bool}
  {Prune.segIn(Prune.Seg{Nat.add(o, q), [], k, List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), j}, set) == True{} : Bool}

def prod_seg_in(grammar, x, o, k, j, q, set, lhsOk, all):
  match grammar q:
    case Nil{} 0n:
      Empty.absurd({Prune.segIn(Prune.Seg{Nat.add(o, 0n), [], k, 0n, j}, set) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Nil{} 1n+r:
      Empty.absurd({Prune.segIn(Prune.Seg{Nat.add(o, 1n+r), [], k, 0n, j}, set) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {Prune.segIn(Prune.Seg{_, [], k, List.length(&2, Spec.Item, rhs), j}, set) == True{} : Bool}
      keep_seg_head(Nat.is_eq(lhs, x), lhsOk, Prune.Seg{o, [], k, List.length(&2, Spec.Item, rhs), j}, Prune.prodSegs(rest, x, 1n+o, k, j), set, all)
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+r):
      %Equal.sym(Nat, Nat.add(o, 1n+r), 1n+Nat.add(o, r), Lemma.add_succ_right(o, r)) : {Prune.segIn(Prune.Seg{_, [], k, List.length(&2, Spec.Item, Spec.rhsOf(rest, r)), j}, set) == True{} : Bool}
      prod_seg_in(rest, x, 1n+o, k, j, r, set, lhsOk, keep_seg_tail(Nat.is_eq(lhs, x), Prune.Seg{o, [], k, List.length(&2, Spec.Item, rhs), j}, Prune.prodSegs(rest, x, 1n+o, k, j), set, all))

law alt_seg_pick:
  for same: Bool
  for +m: Nat
  for +a: Nat
  for +sameEq: {Nat.is_eq(m, a) == same : Bool}
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +j: Nat
  for +set: +List<Prune.Seg>
  for lt: {Nat.is_lt(a, 1n+m) == True{} : Bool}
  for all: {Prune.allSegsIn(Prune.altSegs(1n+m, alts, index, rpath, k, j), set) == True{} : Bool}
  for later: {Nat.is_lt(a, m) == True{} : Bool} -> {Prune.allSegsIn(Prune.altSegs(m, alts, index, rpath, k, j), set) == True{} : Bool} -> {Prune.segIn(Prune.Seg{index, a <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}, set) == True{} : Bool}
  {Prune.segIn(Prune.Seg{index, a <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}, set) == True{} : Bool}

def alt_seg_pick(same, m, a, sameEq, alts, index, rpath, k, j, set, lt, all, later):
  match same:
    case True{}:
      +head = {Prune.Seg{index, m <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, m)), j} : Prune.Seg}
      %Lemma.nat_eq_sound(m, a, sameEq) : {Prune.segIn(Prune.Seg{index, _ <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, _)), j}, set) == True{} : Bool}
      Lemma.and_true_left(Prune.segIn(head, set), Prune.allSegsIn(Prune.altSegs(m, alts, index, rpath, k, j), set), all)
    case False{}:
      +head = {Prune.Seg{index, m <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, m)), j} : Prune.Seg}
      later(Lemma.lt_succ_ne(a, m, lt, sameEq), Lemma.and_true_right_side(Prune.segIn(head, set), Prune.allSegsIn(Prune.altSegs(m, alts, index, rpath, k, j), set), all))

# The segment of alternative a, when all of a bracket's alternatives are needed.
law alt_seg_in:
  for n: Nat
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +j: Nat
  for +a: Nat
  for +set: +List<Prune.Seg>
  for lt: {Nat.is_lt(a, n) == True{} : Bool}
  for all: {Prune.allSegsIn(Prune.altSegs(n, alts, index, rpath, k, j), set) == True{} : Bool}
  {Prune.segIn(Prune.Seg{index, a <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}, set) == True{} : Bool}

def alt_seg_in(n, alts, index, rpath, k, j, a, set, lt, all):
  match n:
    case 0n:
      Empty.absurd({Prune.segIn(Prune.Seg{index, a <> rpath, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}, set) == True{} : Bool}, Lemma.lt_zero_false(a, lt))
    case 1n+(+m):
      alt_seg_pick(Nat.is_eq(m, a), m, a, {==}, alts, index, rpath, k, j, set, lt, all,
        ltM => allM => alt_seg_in(m, alts, index, rpath, k, j, a, set, ltM, allM))

# ---- The closedness of the needs, one condition at a time ----

def NeedsOk(+grammar: +List<Spec.Production>, +ys: +List<Spec.Bsr>, +needs: +List<Prune.Seg>) -> Data:
  Sigma<&2, &2, {Prune.allStepsOk(ys, grammar, needs) == True{} : Bool}, _ => {Prune.allRoundsOk(needs, grammar, needs) == True{} : Bool}>

law step_ok_pick:
  for +grammar: +List<Spec.Production>
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +xOk: {Prune.stepOk(grammar, needs, x) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Prune.stepOk(grammar, needs, e) == True{} : Bool}
  {Prune.stepOk(grammar, needs, e) == True{} : Bool}

def step_ok_pick(grammar, needs, e, x, rest, cases, xOk, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Prune.stepOk(grammar, needs, e), Prune.stepOk(grammar, needs, x), True{}, Equal.cong(Spec.Bsr, Bool, v => Prune.stepOk(grammar, needs, v), e, x, same), xOk)
    case Inr{later}:
      searchRest(later)

law step_ok_of:
  for ys: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for all: {Prune.allStepsOk(ys, grammar, needs) == True{} : Bool}
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  {Prune.stepOk(grammar, needs, e) == True{} : Bool}

def step_ok_of(ys, grammar, needs, e, all, m):
  match ys:
    case Nil{}:
      Empty.absurd({Prune.stepOk(grammar, needs, e) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      +both = all
      step_ok_pick(grammar, needs, e, x, rest, G.ebnf_member_cases(e, x, rest, m),
        Lemma.and_true_left(Prune.stepOk(grammar, needs, x), Prune.allStepsOk(rest, grammar, needs), both),
        later => step_ok_of(rest, grammar, needs, e, Lemma.and_true_right_side(Prune.stepOk(grammar, needs, x), Prune.allStepsOk(rest, grammar, needs), both), later))

law or_not_true:
  for b: Bool
  for +bEq: {b == True{} : Bool}
  for x: Bool
  for h: {Bool.or(Bool.not(b), x) == True{} : Bool}
  {x == True{} : Bool}

def or_not_true(b, bEq, x, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({x == True{} : Bool}, Lemma.false_is_not_true(bEq))

# A kept step of the set brings its needs along.
law kept_needs:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +e: Spec.Bsr
  for inY: {Spec.bsrMember(e, ys) == True{} : Bool}
  for kept: {Prune.isKept(e, needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.stepNeeds(grammar, e), needs) == True{} : Bool}

def kept_needs(grammar, ys, needs, ok, e, inY, kept):
  match ok:
    case (stepsOk, roundsOk):
      or_not_true(Prune.isKept(e, needs), kept, Prune.allSegsIn(Prune.stepNeeds(grammar, e), needs), step_ok_of(ys, grammar, needs, e, stepsOk, inY))

law round_pick:
  for +grammar: +List<Spec.Production>
  for +needs: +List<Prune.Seg>
  for +seg: Prune.Seg
  for +y: Prune.Seg
  for -rest: +List<Prune.Seg>
  for cases: Either<{Prune.segEq(seg, y) == True{} : Bool}, {Prune.segIn(seg, rest) == True{} : Bool}>
  for +yOk: {Prune.allSegsIn(Prune.roundNeeds(grammar, y), needs) == True{} : Bool}
  for searchRest: {Prune.segIn(seg, rest) == True{} : Bool} -> {Prune.allSegsIn(Prune.roundNeeds(grammar, seg), needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.roundNeeds(grammar, seg), needs) == True{} : Bool}

def round_pick(grammar, needs, seg, y, rest, cases, yOk, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Prune.allSegsIn(Prune.roundNeeds(grammar, seg), needs), Prune.allSegsIn(Prune.roundNeeds(grammar, y), needs), True{},
        Equal.cong(Prune.Seg, Bool, v => Prune.allSegsIn(Prune.roundNeeds(grammar, v), needs), seg, y, seg_eq_sound(seg, y, same)), yOk)
    case Inr{later}:
      searchRest(later)

law round_ok_of:
  for xs: +List<Prune.Seg>
  for +grammar: +List<Spec.Production>
  for +needs: +List<Prune.Seg>
  for +seg: Prune.Seg
  for all: {Prune.allRoundsOk(xs, grammar, needs) == True{} : Bool}
  for m: {Prune.segIn(seg, xs) == True{} : Bool}
  {Prune.allSegsIn(Prune.roundNeeds(grammar, seg), needs) == True{} : Bool}

def round_ok_of(xs, grammar, needs, seg, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Prune.allSegsIn(Prune.roundNeeds(grammar, seg), needs) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +both = all
      round_pick(grammar, needs, seg, y, rest, Lemma.or_true_cases(Prune.segEq(seg, y), Prune.segIn(seg, rest), m),
        Lemma.and_true_left(Prune.allSegsIn(Prune.roundNeeds(grammar, y), needs), Prune.allRoundsOk(rest, grammar, needs), both),
        later => round_ok_of(rest, grammar, needs, seg, Lemma.and_true_right_side(Prune.allSegsIn(Prune.roundNeeds(grammar, y), needs), Prune.allRoundsOk(rest, grammar, needs), both), later))

# ---- Lists of steps ----

def allKept(xs: +List<Spec.Bsr>, +needs: +List<Prune.Seg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Prune.isKept(x, needs), allKept(rest, needs))

law kept_app:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for hx: {allKept(xs, needs) == True{} : Bool}
  for +hy: {allKept(ys, needs) == True{} : Bool}
  {allKept(List.append(&2, Spec.Bsr, xs, ys), needs) == True{} : Bool}

def kept_app(xs, ys, needs, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      +both = hx
      Lemma.and_true_intro(Prune.isKept(x, needs), allKept(List.append(&2, Spec.Bsr, rest, ys), needs),
        Lemma.and_true_left(Prune.isKept(x, needs), allKept(rest, needs), both),
        kept_app(rest, ys, needs, Lemma.and_true_right_side(Prune.isKept(x, needs), allKept(rest, needs), both), hy))

# ======== THE WALK, FROM THE RIGHT ========

# At most one tree.
def fewRounds(rs: +List<Spec.Tree>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      List.is_empty(&2, Spec.Tree, rest)

# Where the rounds rs of a loop started at ctx begin: after ctx, or at ctx and then
# either one round or only rounds that read input (SPEC.bend, roundsOk). So a round
# after the first one starts after ctx.
def RoundsFrom(+ctx: Nat, +pos: Nat, +rs: +List<Spec.Tree>) -> Bool:
  Bool.or(Nat.is_lt(ctx, pos), Bool.and(Nat.is_eq(ctx, pos), Bool.or(fewRounds(rs), Spec.allConsume(rs))))

# What the walk needs: the forest's steps are among the parser's steps, it fits the
# items from the dot on, and the segment at its end is needed (in a loop: the loop's
# end, for every alternative).
def PReady(rounds: Bool, +grammar: +List<Spec.Production>, +needs: +List<Prune.Seg>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, forest)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest)))}, needs) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, rpath, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest)))), needs) == True{} : Bool} & {RoundsFrom(ctx, pos, forest) == True{} : Bool}

# What the walk shows: every step is kept, and the segment where the forest starts is
# needed (in a loop: the round before has ended where the first round starts, unless
# that is the loop's start).
def PWalked(rounds: Bool, +needs: +List<Prune.Seg>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {allKept(Spec.walk(forest, False{}, index, prefix, dot, ctx, pos), needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, dot, pos}, needs) == True{} : Bool}
    case True{}:
      {allKept(Spec.walk(forest, True{}, index, prefix, dot, ctx, pos), needs) == True{} : Bool} & {Bool.or(List.is_empty(&2, Spec.Tree, forest), Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, rpath, ctx, pos), needs))) == True{} : Bool}

def PruneIH(+grammar: +List<Spec.Production>, +ys: +List<Spec.Bsr>, +needs: +List<Prune.Seg>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @ctx: Nat -> @pos: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, ctx, pos), ys) == True{} : Bool} -> PReady(rounds, grammar, needs, forest, index, rpath, dot, ctx, pos, items, kind, alts) -> PWalked(rounds, needs, forest, index, rpath, prefix, dot, ctx, pos, alts)

law seg_move:
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ctx: Nat
  for -d1: Nat
  for -d2: Nat
  for -e1: Nat
  for -e2: Nat
  for ed: {d1 == d2 : Nat}
  for ee: {e1 == e2 : Nat}
  for h: {Prune.segIn(Prune.Seg{index, rpath, ctx, d1, e1}, needs) == True{} : Bool}
  {Prune.segIn(Prune.Seg{index, rpath, ctx, d2, e2}, needs) == True{} : Bool}

def seg_move(needs, index, rpath, ctx, d1, d2, e1, e2, ed, ee, h):
  %ed : {Prune.segIn(Prune.Seg{index, rpath, ctx, _, e2}, needs) == True{} : Bool}
  %ee : {Prune.segIn(Prune.Seg{index, rpath, ctx, d1, _}, needs) == True{} : Bool}
  h

# The needs of a kept step: the segment before it, and what its item spans.
law step_split:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for inY: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, end), ys) == True{} : Bool}
  for +inN: {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.Seg{index, rpath, ctx, dot, pos} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), needs) == True{} : Bool}

def step_split(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, end, pEq, inY, inN):
  +e = Spec.at(index, prefix, 1n+dot, ctx, pos, end)
  Equal.trans(Bool, Prune.allSegsIn(Prune.Seg{index, rpath, ctx, dot, pos} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), needs), Prune.allSegsIn(Prune.stepNeeds(grammar, e), needs), True{},
    Equal.cong(+List<Prune.Seg>, Bool, v => Prune.allSegsIn(v, needs), Prune.Seg{index, rpath, ctx, dot, pos} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), Prune.stepNeeds(grammar, e),
      Equal.sym(+List<Prune.Seg>, Prune.stepNeeds(grammar, e), Prune.Seg{index, rpath, ctx, dot, pos} <> Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), needs_at(grammar, index, rpath, prefix, dot, ctx, pos, end, pEq))),
    kept_needs(grammar, ys, needs, ok, e, inY, kept_at(index, rpath, prefix, 1n+dot, ctx, pos, end, needs, pEq, inN)))

# What the item at the dot spans, once the item is known.
law item_needs_at:
  for +grammar: +List<Spec.Production>
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +pos: Nat
  for +end: Nat
  for +it: Spec.Item
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{it} : Maybe<&2, Spec.Item>}
  for all: {Prune.allSegsIn(Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.itemNeeds(Some{it}, grammar, index, rpath, dot, pos, end), needs) == True{} : Bool}

def item_needs_at(grammar, needs, index, rpath, dot, pos, end, it, itemEq, all):
  +item = Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot)
  Equal.trans(Bool, Prune.allSegsIn(Prune.itemNeeds(Some{it}, grammar, index, rpath, dot, pos, end), needs), Prune.allSegsIn(Prune.itemNeeds(item, grammar, index, rpath, dot, pos, end), needs), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Prune.allSegsIn(Prune.itemNeeds(v, grammar, index, rpath, dot, pos, end), needs), Some{it}, item, Equal.sym(Maybe<&2, Spec.Item>, item, Some{it}, itemEq)), all)

# A kept step and the kept steps after it.
law kept_cons:
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +rest: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for inN: {Prune.segIn(Prune.Seg{index, rpath, i, d, j}, needs) == True{} : Bool}
  for later: {allKept(rest, needs) == True{} : Bool}
  {allKept(Spec.at(index, prefix, d, i, k, j) <> rest, needs) == True{} : Bool}

def kept_cons(index, rpath, prefix, d, i, k, j, rest, needs, pEq, inN, later):
  Lemma.and_true_intro(Prune.isKept(Spec.at(index, prefix, d, i, k, j), needs), allKept(rest, needs), kept_at(index, rpath, prefix, d, i, k, j, needs, pEq, inN), later)

# ---- The end of a sequence ----

law p_nil:
  for dot: Nat
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, 0n), Nat.add(pos, 0n)}, needs) == True{} : Bool}
  PWalked(False{}, needs, [], index, rpath, prefix, dot, ctx, pos, [])

def p_nil(dot, needs, index, rpath, prefix, ctx, pos, pEq, endN):
  match dot:
    case 0n:
      +seg = seg_move(needs, index, rpath, ctx, 0n, 0n, Nat.add(pos, 0n), pos, {==}, Lemma.add_zero_right(pos), endN)
      (kept_cons(index, rpath, prefix, 0n, ctx, pos, pos, [], needs, pEq, seg, {==}), seg)
    case 1n+(+d):
      ({==}, seg_move(needs, index, rpath, ctx, Nat.add(1n+d, 0n), 1n+d, Nat.add(pos, 0n), pos, Lemma.add_zero_right(1n+d), Lemma.add_zero_right(pos), endN))

# ---- A terminal, or a skipped [ ]: the step, then the rest ----

law p_leaf_after:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for +later: +List<Spec.Bsr>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inAt: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, end), ys) == True{} : Bool}
  for ih: {allKept(later, needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}
  {allKept(Spec.at(index, prefix, 1n+dot, ctx, pos, end) <> later, needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, dot, pos}, needs) == True{} : Bool}

def p_leaf_after(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, end, later, pEq, inAt, ih):
  match ih:
    case (keptLater, seg0):
      +seg = {seg0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}}
      +before = {Prune.Seg{index, rpath, ctx, dot, pos} : Prune.Seg}
      +split = step_split(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, end, pEq, inAt, seg)
      (kept_cons(index, rpath, prefix, 1n+dot, ctx, pos, end, later, needs, pEq, seg, keptLater),
        segs_head(before, Prune.itemNeeds(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, index, rpath, dot, pos, end), needs, split))

law p_leaf:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Nat
  for +ts: +List<Spec.Tree>
  for +t: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Leaf{kind} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Leaf{kind} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Leaf{kind} <> ts)))}, needs) == True{} : Bool}
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Leaf{kind} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_leaf(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, ts, t, rest, pEq, inY, restEq, fit, endN, ihTs):
  +nts = List.length(&2, Spec.Tree, ts)
  +nl = List.length(&2, Nat, Spec.leaves(ts))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, 1n+pos)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, 1n+nl), 1n+Nat.add(pos, nl), Lemma.add_succ_right(dot, nts), Lemma.add_succ_right(pos, nl), endN)
  p_leaf_after(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, 1n+pos, later, pEq, R.in_head(step, later, ys, inY),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, 1n+pos, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, ys, inY), (restEq, (Lemma.and_true_right_side(Nat.is_eq(kind, t), Spec.fits(ts, grammar, rest), fit), endTs))))

law p_skip:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Skip{} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts)))}, needs) == True{} : Bool}
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_skip(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fitTs, endN, ihTs):
  +nts = List.length(&2, Spec.Tree, ts)
  +nl = List.length(&2, Nat, Spec.leaves(ts))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, pos)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, nl), Nat.add(pos, nl), Lemma.add_succ_right(dot, nts), {==}, endN)
  p_leaf_after(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, pos, later, pEq, R.in_head(step, later, ys, inY),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, pos, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, ys, inY), (restEq, (fitTs, endTs))))

# A closure with no rounds: the skip, with its end written as pos + 0.
law p_loop0:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{[]} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Loop{[]} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Loop{[]} <> ts)))}, needs) == True{} : Bool}
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_loop0(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fitTs, endN, ihTs):
  +nts = List.length(&2, Spec.Tree, ts)
  +nl = List.length(&2, Nat, Spec.leaves(ts))
  +p0 = Nat.add(pos, 0n)
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, p0)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, p0)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, nl), Nat.add(p0, nl), Lemma.add_succ_right(dot, nts),
    Equal.cong(Nat, Nat, v => Nat.add(v, nl), pos, p0, Equal.sym(Nat, p0, pos, Lemma.add_zero_right(pos))), endN)
  p_leaf_after(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, p0, later, pEq, R.in_head(step, later, ys, inY),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, p0, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, ys, inY), (restEq, (fitTs, endTs))))

# ---- A call: the step, then the callee inside, then the rest ----

law p_call_end:
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for +inner: +List<Spec.Bsr>
  for +later: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +segTs: {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}
  for +keptTs: {allKept(later, needs) == True{} : Bool}
  for +before: {Prune.segIn(Prune.Seg{index, rpath, ctx, dot, pos}, needs) == True{} : Bool}
  for +keptInner: {allKept(inner, needs) == True{} : Bool}
  {allKept(Spec.at(index, prefix, 1n+dot, ctx, pos, end) <> List.append(&2, Spec.Bsr, inner, later), needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, dot, pos}, needs) == True{} : Bool}

def p_call_end(index, rpath, prefix, dot, ctx, pos, end, inner, later, needs, pEq, segTs, keptTs, before, keptInner):
  (kept_cons(index, rpath, prefix, 1n+dot, ctx, pos, end, List.append(&2, Spec.Bsr, inner, later), needs, pEq, segTs, kept_app(inner, later, needs, keptInner, keptTs)), before)

law seq_kept:
  for +needs: +List<Prune.Seg>
  for +inner: +List<Spec.Bsr>
  for +seg: Prune.Seg
  for r: {allKept(inner, needs) == True{} : Bool} & {Prune.segIn(seg, needs) == True{} : Bool}
  {allKept(inner, needs) == True{} : Bool}

def seq_kept(needs, inner, seg, r):
  match r:
    case (k, s):
      k

law rounds_kept:
  for +needs: +List<Prune.Seg>
  for +inner: +List<Spec.Bsr>
  for -b: Bool
  for r: {allKept(inner, needs) == True{} : Bool} & {b == True{} : Bool}
  {allKept(inner, needs) == True{} : Bool}

def rounds_kept(needs, inner, b, r):
  match r:
    case (k, s):
      k

# The step, its kept rest, and what it needs: the segment before, and its item's needs.
def After(+grammar: +List<Spec.Production>, +needs: +List<Prune.Seg>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat, +end: Nat, +later: +List<Spec.Bsr>, +it: Spec.Item) -> Type:
  {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool} & {allKept(later, needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, dot, pos}, needs) == True{} : Bool} & {Prune.allSegsIn(Prune.itemNeeds(Some{it}, grammar, index, rpath, dot, pos, end), needs) == True{} : Bool}

law after_call:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +end: Nat
  for +later: +List<Spec.Bsr>
  for +it: Spec.Item
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inAt: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, ctx, pos, end), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{it} : Maybe<&2, Spec.Item>}
  for ih: {allKept(later, needs) == True{} : Bool} & {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}
  After(grammar, needs, index, rpath, dot, ctx, pos, end, later, it)

def after_call(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, end, later, it, pEq, inAt, itemEq, ih):
  match ih:
    case (keptTs, seg0):
      +seg = {seg0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, 1n+dot, end}, needs) == True{} : Bool}}
      +before = {Prune.Seg{index, rpath, ctx, dot, pos} : Prune.Seg}
      +item = Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot)
      +split = step_split(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, end, pEq, inAt, seg)
      (seg, (keptTs, (segs_head(before, Prune.itemNeeds(item, grammar, index, rpath, dot, pos, end), needs, split),
        item_needs_at(grammar, needs, index, rpath, dot, pos, end, it, itemEq, Lemma.and_true_right_side(Prune.segIn(before, needs), Prune.allSegsIn(Prune.itemNeeds(item, grammar, index, rpath, dot, pos, end), needs), split)))))

# ---- A nonterminal ----

law p_node_mid:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inCh: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, pos, pos), ys) == True{} : Bool}
  for +lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for after: After(grammar, needs, index, rpath, dot, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))), Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))), Spec.Sym{Spec.Nonterminal{x}})
  for ihCh: PruneIH(grammar, ys, needs, ch)
  PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_node_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, pEq, inCh, lhsOk, fitCh, after, ihCh):
  match after:
    case (segTs, (keptTs, (before, inner))):
      +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
      prodSeg = prod_seg_in(grammar, x, 0n, pos, e1, q, needs, lhsOk, inner)
      endCh = seg_move(needs, q, [], pos, List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), List.length(&2, Spec.Tree, ch), e1, e1, Equal.sym(Nat, List.length(&2, Spec.Tree, ch), List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), Fits.fits_count(ch, grammar, Spec.rhsOf(grammar, q), fitCh)), {==}, prodSeg)
      +innerSteps = Spec.walk(ch, False{}, q, [], 0n, pos, pos)
      p_call_end(index, rpath, prefix, dot, ctx, pos, e1, innerSteps, Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1), needs, pEq, segTs, keptTs, before,
        seq_kept(needs, innerSteps, Prune.Seg{q, [], pos, 0n, pos}, ihCh(False{}, q, [], [], 0n, pos, pos, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, inCh, ({==}, (fitCh, endCh)))))

law p_node:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Node{q, ch} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts)))}, needs) == True{} : Bool}
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_node(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, inY, itemEq, restEq, fit, endN, ihCh, ihTs):
  +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
  +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
  +lch = Spec.leaves(ch)
  +lts = Spec.leaves(ts)
  +nts = List.length(&2, Spec.Tree, ts)
  +e1 = Nat.add(pos, List.length(&2, Nat, lch))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +innerSteps = Spec.walk(ch, False{}, q, [], 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(e1, List.length(&2, Nat, lts)),
    Lemma.add_succ_right(dot, nts), Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), G.end_split(pos, lch, lts)), endN)
  p_node_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, pEq, R.in_app_left(innerSteps, later, ys, inRest),
    Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk),
    Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk),
    after_call(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, e1, later, Spec.Sym{Spec.Nonterminal{x}}, pEq, R.in_head(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY), itemEq,
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(innerSteps, later, ys, inRest), (restEq, (Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit), endTs)))),
    ihCh)

# ---- A ( ) or [ ] that matched ----

# A bracket that needs its alternatives here.
law bracket_segs:
  for bkind: Spec.Bracket
  for +k: Nat
  for +j: Nat
  for +bn: {Prune.bracketNeeds(bkind, k, j) == True{} : Bool}
  for +segs: +List<Prune.Seg>
  for +needs: +List<Prune.Seg>
  for h: {Prune.allSegsIn(Prune.segsIf(Prune.bracketNeeds(bkind, k, j), segs), needs) == True{} : Bool}
  {Prune.allSegsIn(segs, needs) == True{} : Bool}

def bracket_segs(bkind, k, j, bn, segs, needs, h):
  %bn : {Prune.allSegsIn(Prune.segsIf(_, segs), needs) == True{} : Bool}
  h

# A pick of a [ ] reads something, so the [ ] needs its alternatives there.
law opt_needs:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +pos: Nat
  for okR: {Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]) == True{} : Bool}
  {Prune.bracketNeeds(Spec.Optional{}, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def opt_needs(a, ch, pos, okR):
  +c = Spec.consumes(Spec.Pick{a, ch})
  R.nonempty_lt(Spec.leaves(ch), pos, Lemma.and_true_left(c, True{}, Lemma.or_false_right(Bool.and(c, True{}), okR)))

law p_pick_mid:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +isA: {Spec.isAlt(balts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +bn: {Prune.bracketNeeds(bkind, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for after: After(grammar, needs, index, rpath, dot, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))), Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))), Spec.Brack{bkind, balts})
  for ihCh: PruneIH(grammar, ys, needs, ch)
  PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_pick_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, pEq, inCh, itemEq, isA, fitCh, bn, after, ihCh):
  match after:
    case (segTs, (keptTs, (before, inner))):
      +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
      altSeg = alt_seg_in(List.length(&2, +List<Spec.Item>, balts), balts, index, dot <> rpath, pos, e1, a, needs, isA, bracket_segs(bkind, pos, e1, bn, Prune.altSegs(List.length(&2, +List<Spec.Item>, balts), balts, index, dot <> rpath, pos, e1), needs, inner))
      endCh = seg_move(needs, index, a <> dot <> rpath, pos, List.length(&2, Spec.Item, Spec.altOf(balts, a)), List.length(&2, Spec.Tree, ch), e1, e1, Equal.sym(Nat, List.length(&2, Spec.Tree, ch), List.length(&2, Spec.Item, Spec.altOf(balts, a)), Fits.fits_count(ch, grammar, Spec.altOf(balts, a), fitCh)), {==}, altSeg)
      +innerSteps = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos)
      p_call_end(index, rpath, prefix, dot, ctx, pos, e1, innerSteps, Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1), needs, pEq, segTs, keptTs, before,
        seq_kept(needs, innerSteps, Prune.Seg{index, a <> dot <> rpath, pos, 0n, pos},
          ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos, Spec.altOf(balts, a), Spec.Group{}, [], G.prefix_ext(rpath, prefix, [dot, a], pEq), inCh, (G.alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq), (fitCh, endCh)))))

law p_pick:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +isA: {Spec.isAlt(balts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +bn: {Prune.bracketNeeds(bkind, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts)))}, needs) == True{} : Bool}
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_pick(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, rest, pEq, inY, itemEq, restEq, isA, fitCh, fitTs, bn, endN, ihCh, ihTs):
  +lch = Spec.leaves(ch)
  +lts = Spec.leaves(ts)
  +nts = List.length(&2, Spec.Tree, ts)
  +e1 = Nat.add(pos, List.length(&2, Nat, lch))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +innerSteps = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(e1, List.length(&2, Nat, lts)),
    Lemma.add_succ_right(dot, nts), Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), G.end_split(pos, lch, lts)), endN)
  p_pick_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, pEq, R.in_app_left(innerSteps, later, ys, inRest), itemEq, isA, fitCh, bn,
    after_call(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, e1, later, Spec.Brack{bkind, balts}, pEq, R.in_head(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY), itemEq,
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(innerSteps, later, ys, inRest), (restEq, (fitTs, endTs)))),
    ihCh)

# ---- A loop with rounds ----

law p_loop_mid:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inRs: {Spec.allIn(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fromRs: {RoundsFrom(pos, pos, rs) == True{} : Bool}
  for +bn: {Prune.bracketNeeds(bkind, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))) == True{} : Bool}
  for after: After(grammar, needs, index, rpath, dot, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs))), Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))), Spec.Brack{bkind, balts})
  for ihRs: PruneIH(grammar, ys, needs, rs)
  PWalked(False{}, needs, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_loop_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, rs, ts, bkind, balts, pEq, inRs, itemEq, loopOk, fitRs, fromRs, bn, after, ihRs):
  match after:
    case (segTs, (keptTs, (before, inner))):
      +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))
      +innerSteps = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos)
      p_call_end(index, rpath, prefix, dot, ctx, pos, e1, innerSteps, Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1), needs, pEq, segTs, keptTs, before,
        rounds_kept(needs, innerSteps, Bool.or(List.is_empty(&2, Spec.Tree, rs), Bool.or(Bool.not(Nat.is_lt(pos, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, balts), balts, index, dot <> rpath, pos, pos), needs))),
          ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos, [], bkind, balts, G.prefix_ext(rpath, prefix, [dot], pEq), inRs, (itemEq, (loopOk, (fitRs, (bracket_segs(bkind, pos, e1, bn, Prune.altSegs(List.length(&2, +List<Spec.Item>, balts), balts, index, dot <> rpath, pos, e1), needs, inner), fromRs)))))))

law p_loop:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +fromRs: {RoundsFrom(pos, pos, rs) == True{} : Bool}
  for +bn: {Prune.bracketNeeds(bkind, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))) == True{} : Bool}
  for +endN: {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Loop{rs} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts)))}, needs) == True{} : Bool}
  for ihRs: PruneIH(grammar, ys, needs, rs)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, ctx, pos, [])

def p_loop(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, rs, ts, bkind, balts, rest, pEq, inY, itemEq, restEq, loopOk, fitRs, fitTs, fromRs, bn, endN, ihRs, ihTs):
  +lrs = Spec.leaves(rs)
  +lts = Spec.leaves(ts)
  +nts = List.length(&2, Spec.Tree, ts)
  +e1 = Nat.add(pos, List.length(&2, Nat, lrs))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +innerSteps = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY)
  endTs = seg_move(needs, index, rpath, ctx, Nat.add(dot, 1n+nts), 1n+Nat.add(dot, nts), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), Nat.add(e1, List.length(&2, Nat, lts)),
    Lemma.add_succ_right(dot, nts), Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), G.end_split(pos, lrs, lts)), endN)
  p_loop_mid(grammar, ys, needs, index, rpath, prefix, dot, ctx, pos, rs, ts, bkind, balts, pEq, R.in_app_left(innerSteps, later, ys, inRest), itemEq, loopOk, fitRs, fromRs, bn,
    after_call(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, e1, later, Spec.Brack{bkind, balts}, pEq, R.in_head(step, List.append(&2, Spec.Bsr, innerSteps, later), ys, inY), itemEq,
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(innerSteps, later, ys, inRest), (restEq, (fitTs, endTs)))),
    ihRs)

# ---- The rounds of a loop, from the last one back ----

law ends_hit:
  for loop: Bool
  for +loopEq: {loop == True{} : Bool}
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +rpath: +List<Nat>
  for +i: Nat
  for +s: Nat
  for +needs: +List<Prune.Seg>
  for r: {Prune.allSegsIn(Prune.loopEndsPick(loop, alts, index, rpath, i, s), needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, rpath, i, s), needs) == True{} : Bool}

def ends_hit(loop, loopEq, alts, index, rpath, i, s, needs, r):
  match loop:
    case True{}:
      r
    case False{}:
      Empty.absurd({Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, rpath, i, s), needs) == True{} : Bool}, Lemma.false_is_not_true(loopEq))

law later_hit:
  for later: Bool
  for +laterEq: {later == True{} : Bool}
  for +item: Maybe<&2, Spec.Item>
  for +index: Nat
  for +rpath: +List<Nat>
  for +i: Nat
  for +s: Nat
  for +needs: +List<Prune.Seg>
  for r: {Prune.allSegsIn(Prune.laterRound(later, item, index, rpath, i, s), needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.loopEnds(item, index, rpath, i, s), needs) == True{} : Bool}

def later_hit(later, laterEq, item, index, rpath, i, s, needs, r):
  match later:
    case True{}:
      r
    case False{}:
      Empty.absurd({Prune.allSegsIn(Prune.loopEnds(item, index, rpath, i, s), needs) == True{} : Bool}, Lemma.false_is_not_true(laterEq))

law lt_le_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lt_le_lt(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, Lemma.lt_zero_false(0n, ab))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, Lemma.lt_zero_false(1n+p, ab))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Lemma.false_is_not_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, Lemma.false_is_not_true(bc))
    case 1n+p 1n+q 1n+r:
      lt_le_lt(p, q, r, ab, bc)

law next_cases:
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r2: Spec.Tree
  for +rest2: +List<Spec.Tree>
  for cases: Either<{Nat.is_lt(ctx, pos) == True{} : Bool}, {Bool.and(Nat.is_eq(ctx, pos), Bool.or(fewRounds(Spec.Pick{a, ch} <> r2 <> rest2), Spec.allConsume(Spec.Pick{a, ch} <> r2 <> rest2))) == True{} : Bool}>
  {Nat.is_lt(ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def next_cases(ctx, pos, a, ch, r2, rest2, cases):
  match cases:
    case Inl{lt}:
      lt_le_lt(ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))), lt, Lemma.le_add_right(pos, List.length(&2, Nat, Spec.leaves(ch))))
    case Inr{both0}:
      +both = both0
      +rs = {Spec.Pick{a, ch} <> r2 <> rest2 : +List<Spec.Tree>}
      +eqP = Lemma.and_true_left(Nat.is_eq(ctx, pos), Bool.or(fewRounds(rs), Spec.allConsume(rs)), both)
      +all = Lemma.and_true_right_side(Nat.is_eq(ctx, pos), Bool.or(fewRounds(rs), Spec.allConsume(rs)), both)
      +cons = Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r2 <> rest2), all)
      %Equal.sym(Nat, ctx, pos, Lemma.nat_eq_sound(ctx, pos, eqP)) : {Nat.is_lt(_, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
      R.nonempty_lt(Spec.leaves(ch), pos, cons)

# A round that is not the last one ends after the loop's start.
law next_from:
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r2: Spec.Tree
  for +rest2: +List<Spec.Tree>
  for from: {RoundsFrom(ctx, pos, Spec.Pick{a, ch} <> r2 <> rest2) == True{} : Bool}
  {Nat.is_lt(ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def next_from(ctx, pos, a, ch, r2, rest2, from):
  +rs = {Spec.Pick{a, ch} <> r2 <> rest2 : +List<Spec.Tree>}
  next_cases(ctx, pos, a, ch, r2, rest2, Lemma.or_true_cases(Nat.is_lt(ctx, pos), Bool.and(Nat.is_eq(ctx, pos), Bool.or(fewRounds(rs), Spec.allConsume(rs))), from))

# The rounds of a loop that fits start at the loop's start.
law closure_from:
  for +pos: Nat
  for rs: +List<Spec.Tree>
  for ok: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  {RoundsFrom(pos, pos, rs) == True{} : Bool}

def closure_from(pos, rs, ok):
  match rs:
    case Nil{}:
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), True{}), Lemma.and_true_intro(Nat.is_eq(pos, pos), True{}, Lemma.nat_eq_refl(pos), {==}))
    case Con{+r, Nil{}}:
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), True{}), Lemma.and_true_intro(Nat.is_eq(pos, pos), True{}, Lemma.nat_eq_refl(pos), {==}))
    case Con{+r, Con{+r2, +rr}}:
      +all = Spec.allConsume(r <> r2 <> rr)
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), all), Lemma.and_true_intro(Nat.is_eq(pos, pos), all, Lemma.nat_eq_refl(pos), Lemma.or_false_right(all, ok)))

law positive_from:
  for +pos: Nat
  for rs: +List<Spec.Tree>
  for ok: {Spec.roundsOk(Spec.Positive{}, rs) == True{} : Bool}
  {RoundsFrom(pos, pos, rs) == True{} : Bool}

def positive_from(pos, rs, ok):
  match rs:
    case Nil{}:
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), True{}), Lemma.and_true_intro(Nat.is_eq(pos, pos), True{}, Lemma.nat_eq_refl(pos), {==}))
    case Con{+r, Nil{}}:
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), True{}), Lemma.and_true_intro(Nat.is_eq(pos, pos), True{}, Lemma.nat_eq_refl(pos), {==}))
    case Con{+r, Con{+r2, +rr}}:
      +all = Spec.allConsume(r <> r2 <> rr)
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(Nat.is_eq(pos, pos), all), Lemma.and_true_intro(Nat.is_eq(pos, pos), all, Lemma.nat_eq_refl(pos), Lemma.or_false_right(all, ok)))

# A round that starts after the loop's start is needed: so the round before has ended
# at pos.
law round_start:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +lt: {Nat.is_lt(ctx, pos) == True{} : Bool}
  for seg: {Prune.segIn(Prune.Seg{index, a <> m <> outer, ctx, 0n, pos}, needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs) == True{} : Bool}

def round_start(grammar, ys, needs, ok, index, a, m, outer, ctx, pos, kind, alts, itemEq, loopOk, lt, seg):
  match ok:
    case (stepsOk, roundsOk):
      +item = Gll.nthItem(Gll.seqAt(grammar, index, outer), m)
      ends = later_hit(Nat.is_lt(ctx, pos), lt, item, index, m <> outer, ctx, pos, needs, round_ok_of(needs, grammar, needs, Prune.Seg{index, a <> m <> outer, ctx, 0n, pos}, roundsOk, seg))
      endsK = Equal.trans(Bool, Prune.allSegsIn(Prune.loopEnds(Some{Spec.Brack{kind, alts}}, index, m <> outer, ctx, pos), needs), Prune.allSegsIn(Prune.loopEnds(item, index, m <> outer, ctx, pos), needs), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Prune.allSegsIn(Prune.loopEnds(v, index, m <> outer, ctx, pos), needs), Some{Spec.Brack{kind, alts}}, item, Equal.sym(Maybe<&2, Spec.Item>, item, Some{Spec.Brack{kind, alts}}, itemEq)),
        ends)
      ends_hit(Gll.isLoop(kind), loopOk, alts, index, m <> outer, ctx, pos, needs, endsK)

# A needed round: the round before has ended where it starts, unless it starts where
# the loop starts.
law start_or:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for seg: {Prune.segIn(Prune.Seg{index, a <> m <> outer, ctx, 0n, pos}, needs) == True{} : Bool}
  for b: Bool
  for +bEq: {Nat.is_lt(ctx, pos) == b : Bool}
  {Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}

def start_or(grammar, ys, needs, ok, index, a, m, outer, ctx, pos, kind, alts, itemEq, loopOk, seg, b, bEq):
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(ctx, pos), True{}, bEq) : {Bool.or(Bool.not(_), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}
      round_start(grammar, ys, needs, ok, index, a, m, outer, ctx, pos, kind, alts, itemEq, loopOk, bEq, seg)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(ctx, pos), False{}, bEq) : {Bool.or(Bool.not(_), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}
      {==}

law segs_move:
  for +needs: +List<Prune.Seg>
  for +n: Nat
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ctx: Nat
  for -e1: Nat
  for -e2: Nat
  for ee: {e1 == e2 : Nat}
  for h: {Prune.allSegsIn(Prune.altSegs(n, alts, index, rpath, ctx, e1), needs) == True{} : Bool}
  {Prune.allSegsIn(Prune.altSegs(n, alts, index, rpath, ctx, e2), needs) == True{} : Bool}

def segs_move(needs, n, alts, index, rpath, ctx, e1, e2, ee, h):
  %ee : {Prune.allSegsIn(Prune.altSegs(n, alts, index, rpath, ctx, _), needs) == True{} : Bool}
  h

law round_inner_end:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +ch: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for r: PWalked(False{}, needs, ch, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos, [])
  {allKept(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), needs) == True{} : Bool} & {Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}

def round_inner_end(grammar, ys, needs, ok, index, a, m, outer, prefix, ctx, pos, ch, kind, alts, itemEq, loopOk, r):
  match r:
    case (keptCh, seg0):
      (keptCh, start_or(grammar, ys, needs, ok, index, a, m, outer, ctx, pos, kind, alts, itemEq, loopOk, seg0, Nat.is_lt(ctx, pos), {==}))

# One round, given that the loop ends where the round ends.
law round_inner:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +inCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for ends: {Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))), needs) == True{} : Bool}
  for ihCh: PruneIH(grammar, ys, needs, ch)
  {allKept(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), needs) == True{} : Bool} & {Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}

def round_inner(grammar, ys, needs, ok, index, m, outer, prefix, ctx, pos, a, ch, kind, alts, pEq, inCh, itemEq, loopOk, isA, fitCh, ends, ihCh):
  +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
  altSeg = alt_seg_in(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, e1, a, needs, isA, ends)
  endCh = seg_move(needs, index, a <> m <> outer, ctx, List.length(&2, Spec.Item, Spec.altOf(alts, a)), List.length(&2, Spec.Tree, ch), e1, e1, Equal.sym(Nat, List.length(&2, Spec.Tree, ch), List.length(&2, Spec.Item, Spec.altOf(alts, a)), Fits.fits_count(ch, grammar, Spec.altOf(alts, a), fitCh)), {==}, altSeg)
  remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
  round_inner_end(grammar, ys, needs, ok, index, a, m, outer, prefix, ctx, pos, ch, kind, alts, itemEq, loopOk,
    ihCh(False{}, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos, Spec.altOf(alts, a), Spec.Group{}, [], G.prefix_ext(m <> outer, prefix, [a], pEq), inCh, (remCh, (fitCh, endCh))))

law round_wrap_nil:
  for +needs: +List<Prune.Seg>
  for +inner: +List<Spec.Bsr>
  for -b: Bool
  for r: {allKept(inner, needs) == True{} : Bool} & {b == True{} : Bool}
  {allKept(List.append(&2, Spec.Bsr, inner, []), needs) == True{} : Bool} & {b == True{} : Bool}

def round_wrap_nil(needs, inner, b, r):
  match r:
    case (k, s):
      (kept_app(inner, [], needs, k, {==}), s)

law round_more_end:
  for +needs: +List<Prune.Seg>
  for +inner: +List<Spec.Bsr>
  for +later: +List<Spec.Bsr>
  for -b: Bool
  for +keptLater: {allKept(later, needs) == True{} : Bool}
  for r: {allKept(inner, needs) == True{} : Bool} & {b == True{} : Bool}
  {allKept(List.append(&2, Spec.Bsr, inner, later), needs) == True{} : Bool} & {b == True{} : Bool}

def round_more_end(needs, inner, later, b, keptLater, r):
  match r:
    case (k, s):
      (kept_app(inner, later, needs, k, keptLater), s)

law round_more:
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r2: Spec.Tree
  for +rest2: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +inCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +ltE: {Nat.is_lt(ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for later: PWalked(True{}, needs, r2 <> rest2, index, m <> outer, prefix, 0n, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))), alts)
  for ihCh: PruneIH(grammar, ys, needs, ch)
  {allKept(List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), Spec.walk(r2 <> rest2, True{}, index, prefix, 0n, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch))))), needs) == True{} : Bool} & {Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)) == True{} : Bool}

def round_more(grammar, ys, needs, ok, index, m, outer, prefix, ctx, pos, a, ch, r2, rest2, kind, alts, pEq, inCh, itemEq, loopOk, isA, fitCh, ltE, later, ihCh):
  match later:
    case (keptRest, ends0):
      +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
      ends = or_not_true(Nat.is_lt(ctx, e1), ltE, Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, e1), needs), ends0)
      round_more_end(needs, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos), Spec.walk(r2 <> rest2, True{}, index, prefix, 0n, ctx, e1), Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, pos), needs)), keptRest,
        round_inner(grammar, ys, needs, ok, index, m, outer, prefix, ctx, pos, a, ch, kind, alts, pEq, inCh, itemEq, loopOk, isA, fitCh, ends, ihCh))

law round_last:
  for rest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +endN: {Prune.allSegsIn(Prune.altSegs(List.length(&2, +List<Spec.Item>, alts), alts, index, m <> outer, ctx, Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest)))), needs) == True{} : Bool}
  for +from: {RoundsFrom(ctx, pos, Spec.Pick{a, ch} <> rest) == True{} : Bool}
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihRest: PruneIH(grammar, ys, needs, rest)
  PWalked(True{}, needs, Spec.Pick{a, ch} <> rest, index, m <> outer, prefix, dot, ctx, pos, alts)

def round_last(rest, grammar, ys, needs, ok, index, m, outer, prefix, dot, ctx, pos, a, ch, kind, alts, pEq, inY, itemEq, loopOk, isA, fitCh, fitRest, endN, from, ihCh, ihRest):
  match rest:
    case Nil{}:
      +lch = Spec.leaves(ch)
      +e1 = Nat.add(pos, List.length(&2, Nat, lch))
      +n = List.length(&2, +List<Spec.Item>, alts)
      +innerSteps = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos)
      ends = segs_move(needs, n, alts, index, m <> outer, ctx, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, []))), e1, Equal.sym(Nat, e1, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, []))), G.end_alone(pos, lch)), endN)
      round_wrap_nil(needs, innerSteps, Bool.or(Bool.not(Nat.is_lt(ctx, pos)), Prune.allSegsIn(Prune.altSegs(n, alts, index, m <> outer, ctx, pos), needs)),
        round_inner(grammar, ys, needs, ok, index, m, outer, prefix, ctx, pos, a, ch, kind, alts, pEq, R.in_app_left(innerSteps, [], ys, inY), itemEq, loopOk, isA, fitCh, ends, ihCh))
    case Con{+r2, +rest2}:
      +lch = Spec.leaves(ch)
      +lrest = Spec.leaves(r2 <> rest2)
      +e1 = Nat.add(pos, List.length(&2, Nat, lch))
      +n = List.length(&2, +List<Spec.Item>, alts)
      +innerSteps = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos)
      +laterSteps = Spec.walk(r2 <> rest2, True{}, index, prefix, 0n, ctx, e1)
      endRest = segs_move(needs, n, alts, index, m <> outer, ctx, Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), Nat.add(e1, List.length(&2, Nat, lrest)), Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lrest)), Nat.add(pos, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), G.end_split(pos, lch, lrest)), endN)
      +ltE = next_from(ctx, pos, a, ch, r2, rest2, from)
      +fromNext = Lemma.or_true_left_intro(Nat.is_lt(ctx, e1), Bool.and(Nat.is_eq(ctx, e1), Bool.or(fewRounds(r2 <> rest2), Spec.allConsume(r2 <> rest2))), ltE)
      round_more(grammar, ys, needs, ok, index, m, outer, prefix, ctx, pos, a, ch, r2, rest2, kind, alts, pEq, R.in_app_left(innerSteps, laterSteps, ys, inY), itemEq, loopOk, isA, fitCh, ltE,
        ihRest(True{}, index, m <> outer, prefix, 0n, ctx, e1, [], kind, alts, pEq, R.in_app_right(innerSteps, laterSteps, ys, inY), (itemEq, (loopOk, (fitRest, (endRest, fromNext))))),
        ihCh)
law qleaf_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Leaf{k0} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qleaf_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Leaf{k0} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          p_leaf(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, k0, ts, t, rest, pEq, inY, restEq, fit, endN, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))

law qnode_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Node{q, ch} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qnode_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, inY, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Node{q, ch} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          p_node(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, inY, itemEq, restEq, fit, endN, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))

law qpick_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Pick{a, ch} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qpick_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, inY, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +hOk = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          p_pick(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Group{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit), {==}, endN, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +hOk = Lemma.and_true_left(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          +altOk = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          p_pick(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Optional{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), altOk),
            Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit),
            opt_needs(a, ch, pos, Lemma.and_true_left(okR, Spec.isAlt(balts, a), altOk)), endN, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))

law qskip_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Skip{} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qskip_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Skip{} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          p_skip(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, endN, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Skip{} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Skip{} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts)))}, needs) == True{} : Bool}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          p_skip(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, endN, ihTs)

law qloop0_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{[]} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Loop{[]} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qloop0_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Loop{[]} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Loop{[]} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          p_loop0(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, endN, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{[]} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))

law qloop_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +r: Spec.Tree
  for +rr: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{r <> rr} <> ts, False{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(False{}, grammar, needs, Spec.Loop{r <> rr} <> ts, index, rpath, dot, ctx, pos, items, kind, alts)
  for ihRs: PruneIH(grammar, ys, needs, r <> rr)
  for ihTs: PruneIH(grammar, ys, needs, ts)
  PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts)

def qloop_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, inY, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Loop{r <> rr} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Loop{r <> rr} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Closure{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          p_loop(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, r <> rr, ts, Spec.Closure{}, balts, rest, pEq, inY, itemEq, restEq, {==},
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit),
            closure_from(pos, r <> rr, Lemma.and_true_left(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both)), {==}, endN, ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +endN = {endN0 : {Prune.segIn(Prune.Seg{index, rpath, ctx, Nat.add(dot, List.length(&2, Spec.Tree, Spec.Loop{r <> rr} <> ts)), Nat.add(pos, List.length(&2, Nat, Spec.leaves(Spec.Loop{r <> rr} <> ts)))}, needs) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Positive{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          p_loop(grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, r <> rr, ts, Spec.Positive{}, balts, rest, pEq, inY, itemEq, restEq, {==},
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit),
            positive_from(pos, r <> rr, Lemma.and_true_left(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both)), {==}, endN, ihRs, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, endN0)):
          Empty.absurd(PWalked(False{}, needs, Spec.Loop{r <> rr} <> ts, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit0))

law qround_disp:
  for rpath: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(True{}, grammar, needs, Spec.Pick{a, ch} <> rest, index, rpath, dot, ctx, pos, [], kind, alts)
  for ihCh: PruneIH(grammar, ys, needs, ch)
  for ihRest: PruneIH(grammar, ys, needs, rest)
  PWalked(True{}, needs, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, ctx, pos, alts)

def qround_disp(rpath, a, ch, grammar, ys, needs, ok, index, prefix, dot, ctx, pos, kind, alts, rest, pEq, inY, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (itemEq, more):
          Empty.absurd(PWalked(True{}, needs, Spec.Pick{a, ch} <> rest, index, [], prefix, dot, ctx, pos, alts), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      match ready:
        case (itemEq0, (loopOk0, (fit0, (endN0, from0)))):
          +itemEq = {itemEq0 : {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +loopOk = {loopOk0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +R = Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}))
          +hOk = Lemma.and_true_left(h, R, fit)
          round_last(rest, grammar, ys, needs, ok, index, m, outer, prefix, dot, ctx, pos, a, ch, kind, alts, pEq, inY, itemEq, loopOk,
            Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
            Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
            Lemma.and_true_right_side(h, R, fit), endN0, from0, ihCh, ihRest)

law qseq_nil:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: PReady(False{}, grammar, needs, [], index, rpath, dot, ctx, pos, items, kind, alts)
  PWalked(False{}, needs, [], index, rpath, prefix, dot, ctx, pos, alts)

def qseq_nil(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, pEq, ready):
  match items:
    case Nil{}:
      match ready:
        case (rem, (fit, endN)):
          p_nil(dot, needs, index, rpath, prefix, ctx, pos, pEq, endN)
    case Con{it, rest}:
      match ready:
        case (rem, (fit, endN)):
          Empty.absurd(PWalked(False{}, needs, [], index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))

# Every step of a forest whose end is needed is kept, and its start is needed.
law prune_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +ok: NeedsOk(grammar, ys, needs)
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, ctx, pos), ys) == True{} : Bool}
  for ready: PReady(rounds, grammar, needs, forest, index, rpath, dot, ctx, pos, items, kind, alts)
  PWalked(rounds, needs, forest, index, rpath, prefix, dot, ctx, pos, alts)

def prune_walk(forest, rounds, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, items, kind, alts, pEq, inY, ready):
  match forest rounds:
    case Nil{} False{}:
      qseq_nil(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, pEq, ready)
    case Nil{} True{}:
      ({==}, {==})
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      qleaf_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      qnode_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ch, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      qpick_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ch, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      qskip_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      qloop0_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Loop{Con{+r, +rr}}, +ts} False{}:
      qloop_disp(items, grammar, ys, needs, ok, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(r <> rr, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ts, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      qround_disp(rpath, a, ch, grammar, ys, needs, ok, index, prefix, dot, ctx, pos, kind, alts, rest, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(ch, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => prune_walk(rest, ri, grammar, ys, needs, ok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, en))):
          Empty.absurd(PWalked(True{}, needs, Spec.Leaf{k0} <> rest, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, en))):
          Empty.absurd(PWalked(True{}, needs, Spec.Node{q, ch} <> rest, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, en))):
          Empty.absurd(PWalked(True{}, needs, Spec.Skip{} <> rest, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, en))):
          Empty.absurd(PWalked(True{}, needs, Spec.Loop{rs} <> rest, index, rpath, prefix, dot, ctx, pos, alts), Lemma.false_is_not_true(fit))

# ---- Membership in the kept set ----

law kept_pick:
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +xKept: {Prune.isKept(x, needs) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Prune.isKept(e, needs) == True{} : Bool}
  {Prune.isKept(e, needs) == True{} : Bool}

def kept_pick(needs, e, x, rest, cases, xKept, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Prune.isKept(e, needs), Prune.isKept(x, needs), True{}, Equal.cong(Spec.Bsr, Bool, v => Prune.isKept(v, needs), e, x, same), xKept)
    case Inr{later}:
      searchRest(later)

# An element of a list whose steps are all kept is kept.
law kept_member:
  for xs: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for all: {allKept(xs, needs) == True{} : Bool}
  for m: {Spec.bsrMember(e, xs) == True{} : Bool}
  {Prune.isKept(e, needs) == True{} : Bool}

def kept_member(xs, needs, e, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({Prune.isKept(e, needs) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      +both = all
      kept_pick(needs, e, x, rest, G.ebnf_member_cases(e, x, rest, m),
        Lemma.and_true_left(Prune.isKept(x, needs), allKept(rest, needs), both),
        later => kept_member(rest, needs, e, Lemma.and_true_right_side(Prune.isKept(x, needs), allKept(rest, needs), both), later))

law keep_head:
  for k: Bool
  for +isK: {k == True{} : Bool}
  for +x: Spec.Bsr
  for +others: +List<Spec.Bsr>
  {Spec.bsrMember(x, Prune.keepPick(k, x, others)) == True{} : Bool}

def keep_head(k, isK, x, others):
  match k:
    case True{}:
      R.bsr_member_head(x, others)
    case False{}:
      Empty.absurd({Spec.bsrMember(x, others) == True{} : Bool}, Lemma.false_is_not_true(isK))

law keep_later:
  for k: Bool
  for +x: Spec.Bsr
  for +others: +List<Spec.Bsr>
  for e: Spec.Bsr
  for m: {Spec.bsrMember(e, others) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keepPick(k, x, others)) == True{} : Bool}

def keep_later(k, x, others, e, m):
  match k:
    case True{}:
      R.bsr_member_cons(e, x, others, m)
    case False{}:
      m

law keep_pick2:
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +kept: {Prune.isKept(e, needs) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Spec.bsrMember(e, Prune.keep(rest, needs)) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keepPick(Prune.isKept(x, needs), x, Prune.keep(rest, needs))) == True{} : Bool}

def keep_pick2(needs, e, x, rest, cases, kept, searchRest):
  match cases:
    case Inl{same}:
      +eq = same
      +others = Prune.keep(rest, needs)
      keptX = Equal.trans(Bool, Prune.isKept(x, needs), Prune.isKept(e, needs), True{}, Equal.sym(Bool, Prune.isKept(e, needs), Prune.isKept(x, needs), Equal.cong(Spec.Bsr, Bool, v => Prune.isKept(v, needs), e, x, eq)), kept)
      %Equal.sym(Spec.Bsr, e, x, eq) : {Spec.bsrMember(_, Prune.keepPick(Prune.isKept(x, needs), x, others)) == True{} : Bool}
      keep_head(Prune.isKept(x, needs), keptX, x, others)
    case Inr{later}:
      keep_later(Prune.isKept(x, needs), x, Prune.keep(rest, needs), e, searchRest(later))

# A kept element of the parser's set is in the pruned set.
law keep_member:
  for ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  for +kept: {Prune.isKept(e, needs) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keep(ys, needs)) == True{} : Bool}

def keep_member(ys, needs, e, m, kept):
  match ys:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(e, []) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      keep_pick2(needs, e, x, rest, G.ebnf_member_cases(e, x, rest, m), kept,
        later => keep_member(rest, needs, e, later, kept))

# ---- The root ----

law root_kept:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for closedN: {Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, needs) == True{} : Bool}
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for inY: {Spec.allIn(Spec.steps(tree, 0n), ys) == True{} : Bool}
  {allKept(Spec.steps(tree, 0n), needs) == True{} : Bool}

def root_kept(grammar, start, input, ys, needs, closedN, tree, fitting, spelled, inY):
  match tree:
    case Spec.Node{+q, +ch}:
      +n = List.length(&2, Nat, input)
      +both = closedN
      +rootAll = Prune.allSegsIn(Prune.rootSegs(grammar, start, n), needs)
      +stepsAll = Prune.allStepsOk(ys, grammar, needs)
      +roundsAll = Prune.allRoundsOk(needs, grammar, needs)
      +rest = Lemma.and_true_right_side(rootAll, Bool.and(stepsAll, roundsAll), both)
      +ok = {(Lemma.and_true_left(stepsAll, roundsAll, rest), Lemma.and_true_right_side(stepsAll, roundsAll, rest)) : NeedsOk(grammar, ys, needs)}
      +fit = fitting
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, fit)
      +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +lch = Spec.leaves(ch)
      rootSeg = prod_seg_in(grammar, start, 0n, 0n, n, q, needs, lhsOk, Lemma.and_true_left(rootAll, Bool.and(stepsAll, roundsAll), both))
      lenEq = Equal.trans(Nat, List.length(&2, Nat, lch), List.length(&2, Nat, List.append(&2, Nat, lch, [])), n,
        Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), lch, List.append(&2, Nat, lch, []), Equal.sym(+List<Nat>, List.append(&2, Nat, lch, []), lch, Lemma.append_nil_right(lch))),
        Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, lch, []), input, spelled))
      endN = seg_move(needs, q, [], 0n, List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), List.length(&2, Spec.Tree, ch), n, List.length(&2, Nat, lch),
        Equal.sym(Nat, List.length(&2, Spec.Tree, ch), List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), Fits.fits_count(ch, grammar, Spec.rhsOf(grammar, q), fitCh)),
        Equal.sym(Nat, List.length(&2, Nat, lch), n, lenEq), rootSeg)
      seq_kept(needs, Spec.steps(Spec.Node{q, ch}, 0n), Prune.Seg{q, [], 0n, 0n, 0n},
        prune_walk(ch, False{}, grammar, ys, needs, ok, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, inY, ({==}, (fitCh, endN))))
    case Spec.Leaf{k}:
      Empty.absurd({allKept(Spec.steps(Spec.Leaf{k}, 0n), needs) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Pick{a, ch}:
      Empty.absurd({allKept(Spec.steps(Spec.Pick{a, ch}, 0n), needs) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({allKept(Spec.steps(Spec.Skip{}, 0n), needs) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({allKept(Spec.steps(Spec.Loop{rs}, 0n), needs) == True{} : Bool}, Lemma.false_is_not_true(fitting))

# ---- From the pruned parser's answer ----

# Every step of the list is kept, so the list is in the kept steps.
law all_in_pkeep:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for inY: {Spec.allIn(xs, ys) == True{} : Bool}
  for kept: {allKept(xs, needs) == True{} : Bool}
  {Spec.allIn(xs, Prune.keep(ys, needs)) == True{} : Bool}

def all_in_pkeep(xs, ys, needs, inY, kept):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +bothY = inY
      +bothK = kept
      Lemma.and_true_intro(Spec.bsrMember(x, Prune.keep(ys, needs)), Spec.allIn(rest, Prune.keep(ys, needs)),
        keep_member(ys, needs, x, Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), bothY), Lemma.and_true_left(Prune.isKept(x, needs), allKept(rest, needs), bothK)),
        all_in_pkeep(rest, ys, needs, Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), bothY), Lemma.and_true_right_side(Prune.isKept(x, needs), allKept(rest, needs), bothK)))

law pruned_final:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Spec.Bsr>
  for every: R.StepsIn(grammar, start, input, ys)
  for +needs: +List<Prune.Seg>
  for +set: +List<Spec.Bsr>
  for +closedN: {Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, needs) == True{} : Bool}
  for +same: {Prune.keep(ys, needs) == set : +List<Spec.Bsr>}
  R.StepsIn(grammar, start, input, set)

def pruned_final(grammar, start, input, ys, every, needs, set, closedN, same):
  +tree => +fitting => +spelled =>
    +inY = every(tree, fitting, spelled)
    kept = root_kept(grammar, start, input, ys, needs, closedN, tree, fitting, spelled, inY)
    %same : {Spec.allIn(Spec.steps(tree, 0n), _) == True{} : Bool}
    all_in_pkeep(Spec.steps(tree, 0n), ys, needs, inY, kept)

law prune_pick_facts:
  for ok: Bool
  for +ys: +List<Spec.Bsr>
  for +needs: +List<Prune.Seg>
  for +set: +List<Spec.Bsr>
  for got: {Prune.prunePick(ok, ys, needs) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {ok == True{} : Bool} & {Prune.keep(ys, needs) == set : +List<Spec.Bsr>}

def prune_pick_facts(ok, ys, needs, set, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{Prune.keep(ys, needs)}, Some{set}, got))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {Prune.keep(ys, needs) == set : +List<Spec.Bsr>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law pruned_facts:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Spec.Bsr>
  for every: R.StepsIn(grammar, start, input, ys)
  for +needs: +List<Prune.Seg>
  for +set: +List<Spec.Bsr>
  for facts: {Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, needs) == True{} : Bool} & {Prune.keep(ys, needs) == set : +List<Spec.Bsr>}
  R.StepsIn(grammar, start, input, set)

def pruned_facts(grammar, start, input, ys, every, needs, set, facts):
  match facts:
    case (closedN, same):
      pruned_final(grammar, start, input, ys, every, needs, set, closedN, same)

law pruned_needs:
  for nm: Maybe<&2, +List<Prune.Seg>>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Spec.Bsr>
  for every: R.StepsIn(grammar, start, input, ys)
  for +set: +List<Spec.Bsr>
  for got: {Prune.pruneChecked(nm, grammar, start, List.length(&2, Nat, input), ys) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def pruned_needs(nm, grammar, start, input, ys, every, set, got):
  match nm:
    case Some{+needs}:
      pruned_facts(grammar, start, input, ys, every, needs, set, prune_pick_facts(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, needs), ys, needs, set, got))
    case None{}:
      Empty.absurd(R.StepsIn(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law pruned_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for every: R.FoundSteps(found, grammar, start, input)
  for got: {Prune.pruneSteps(found, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def pruned_found(found, fuel, grammar, start, input, set, every, got):
  match found:
    case Some{+ys}:
      pruned_needs(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), grammar, start, input, ys, every, set, got)
    case None{}:
      Empty.absurd(R.StepsIn(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law prune_found_eq:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for every: R.FoundSteps(found, grammar, start, input)
  for out: Maybe<&2, +List<Spec.Bsr>>
  for eq: {Prune.pruneSteps(found, fuel, grammar, start, input) == out : Maybe<&2, +List<Spec.Bsr>>}
  R.FoundSteps(out, grammar, start, input)

def prune_found_eq(found, fuel, grammar, start, input, every, out, eq):
  match out:
    case Some{+set}:
      pruned_found(found, fuel, grammar, start, input, set, every, eq)
    case None{}:
      Unit{}

def unwrapOr(m: Maybe<&2, +List<Spec.Bsr>>, +d: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match m:
    case Some{xs}:
      xs
    case None{}:
      d

law found_every:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for every: R.FoundSteps(found, grammar, start, input)
  for got: {found == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

def found_every(found, grammar, start, input, set, every, got):
  match found:
    case Some{+ys}:
      +tree => +element => +fitting => +spelled => +inTree =>
        eqYS = Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => unwrapOr(v, ys), Some{ys}, Some{set}, got)
        %eqYS : {Spec.bsrMember(element, _) == True{} : Bool}
        G.ebnf_all_in_member(Spec.steps(tree, 0n), ys, element, every(tree, fitting, spelled), inTree)
    case None{}:
      Empty.absurd(Spec.EveryParseStep(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# THE RESULT OF STEP 4: the pruned set has every step of every parse tree.
law pruned_every:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Prune.prunedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)

def pruned_every(fuel, grammar, start, input, set, got):
  +filtered = Prune.roundRule(Check.checkedSteps(fuel, grammar, start, input), grammar)
  found_every(Prune.prunedSteps(fuel, grammar, start, input), grammar, start, input, set,
    prune_found_eq(filtered, fuel, grammar, start, input, R.rounds_found(fuel, grammar, start, input), Prune.prunedSteps(fuel, grammar, start, input), {==}), got)
