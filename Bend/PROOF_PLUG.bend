import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_SUBPARSE.bend as Sub
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# PLUGGING: the place of a forest in a tree, and the tree with another forest in that
# place. A frame says how a forest sits inside the forest one level up: as the children
# of a node or a pick, or as the rounds of a loop, with the trees to its left and right.
# A list of frames, innermost first, leads from the forest to the root.

type Frame is Data:
  NodeKid{left: +List<Spec.Tree>, q: Nat, right: +List<Spec.Tree>}
  PickKid{left: +List<Spec.Tree>, a: Nat, right: +List<Spec.Tree>}
  LoopKid{left: +List<Spec.Tree>, right: +List<Spec.Tree>}

def wrap(fr: Frame, +x: +List<Spec.Tree>) -> Spec.Tree:
  match fr:
    case NodeKid{l, +q, r}:
      Spec.Node{q, x}
    case PickKid{l, +a, r}:
      Spec.Pick{a, x}
    case LoopKid{l, r}:
      Spec.Loop{x}

def fill(fr: Frame, +x: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match fr:
    case NodeKid{+l, +q, +r}:
      List.append(&2, Spec.Tree, l, Spec.Node{q, x} <> r)
    case PickKid{+l, +a, +r}:
      List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r)
    case LoopKid{+l, +r}:
      List.append(&2, Spec.Tree, l, Spec.Loop{x} <> r)

def zip(z: +List<Frame>, +x: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match z:
    case Nil{}:
      x
    case Con{fr, +rest}:
      zip(rest, fill(fr, x))

# What each tree of a forest spells.
def spellEach(forest: +List<Spec.Tree>) -> +List<+List<Nat>>:
  match forest:
    case Nil{}:
      []
    case Con{+t, ts}:
      Spec.leaves([t]) <> spellEach(ts)

# ======== SPELLING ========

law leaves_one:
  for t: Spec.Tree
  {Spec.leaves([t]) == Spec.leaves([t]) : +List<Nat>}

def leaves_one(t):
  {==}

# A node, pick or loop over x spells what x spells.
law wrap_leaves:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  {Spec.leaves([wrap(fr, x)]) == Spec.leaves(x) : +List<Nat>}

def wrap_leaves(fr, x):
  match fr:
    case NodeKid{l, +q, r}:
      Lemma.append_nil_right(Spec.leaves(x))
    case PickKid{l, +a, r}:
      Lemma.append_nil_right(Spec.leaves(x))
    case LoopKid{l, r}:
      Lemma.append_nil_right(Spec.leaves(x))

law leaves_app:
  for l: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  {Spec.leaves(List.append(&2, Spec.Tree, l, r)) == List.append(&2, Nat, Spec.leaves(l), Spec.leaves(r)) : +List<Nat>}

def leaves_app(l, r):
  match l:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +a1 = Sub.leaves_cons(t, List.append(&2, Spec.Tree, ts, r))
      +ih = leaves_app(ts, r)
      +a2 = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, Spec.leaves([t]), v), Spec.leaves(List.append(&2, Spec.Tree, ts, r)), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(r)), ih)
      +a3 = Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Spec.leaves(r)), List.append(&2, Nat, Spec.leaves([t]), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(r))), G.nat_append_assoc(Spec.leaves([t]), Spec.leaves(ts), Spec.leaves(r)))
      +a4 = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(r)), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Spec.leaves(t <> ts), Equal.sym(+List<Nat>, Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Sub.leaves_cons(t, ts)))
      Equal.trans(+List<Nat>, Spec.leaves(t <> List.append(&2, Spec.Tree, ts, r)), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(List.append(&2, Spec.Tree, ts, r))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(r)), a1,
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(List.append(&2, Spec.Tree, ts, r))), List.append(&2, Nat, Spec.leaves([t]), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(r))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(r)), a2,
          Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves([t]), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(r))), List.append(&2, Nat, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Spec.leaves(r)), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(r)), a3, a4)))

law leaves_swap:
  for +l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.leaves(List.append(&2, Spec.Tree, l, t2 <> r)) == Spec.leaves(List.append(&2, Spec.Tree, l, t <> r)) : +List<Nat>}

def leaves_swap(l, t, t2, r, lv):
  +e1 = leaves_app(l, t2 <> r)
  +e2 = leaves_app(l, t <> r)
  +m2 = Equal.trans(+List<Nat>, Spec.leaves(t2 <> r), List.append(&2, Nat, Spec.leaves([t2]), Spec.leaves(r)), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(r)), Sub.leaves_cons(t2, r), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(r)), Spec.leaves([t2]), Spec.leaves([t]), lv))
  +m = Equal.trans(+List<Nat>, Spec.leaves(t2 <> r), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(r)), Spec.leaves(t <> r), m2, Equal.sym(+List<Nat>, Spec.leaves(t <> r), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(r)), Sub.leaves_cons(t, r)))
  Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, l, t2 <> r)), List.append(&2, Nat, Spec.leaves(l), Spec.leaves(t2 <> r)), Spec.leaves(List.append(&2, Spec.Tree, l, t <> r)), e1,
    Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(l), Spec.leaves(t2 <> r)), List.append(&2, Nat, Spec.leaves(l), Spec.leaves(t <> r)), Spec.leaves(List.append(&2, Spec.Tree, l, t <> r)), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, Spec.leaves(l), v), Spec.leaves(t2 <> r), Spec.leaves(t <> r), m), Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, l, t <> r)), List.append(&2, Nat, Spec.leaves(l), Spec.leaves(t <> r)), e2)))

# A tree swapped for one that spells the same: the forest spells the same.
law leaves_fill:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.leaves(fill(fr, x2)) == Spec.leaves(fill(fr, x)) : +List<Nat>}

def leaves_fill(fr, x, x2, lv):
  match fr:
    case NodeKid{+l, +q, +r}:
      leaves_swap(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q, x2}]), Spec.leaves(x2), Spec.leaves([Spec.Node{q, x}]), Lemma.append_nil_right(Spec.leaves(x2)), Equal.trans(+List<Nat>, Spec.leaves(x2), Spec.leaves(x), Spec.leaves([Spec.Node{q, x}]), lv, Equal.sym(+List<Nat>, Spec.leaves([Spec.Node{q, x}]), Spec.leaves(x), Lemma.append_nil_right(Spec.leaves(x))))))
    case PickKid{+l, +a, +r}:
      leaves_swap(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, Equal.trans(+List<Nat>, Spec.leaves([Spec.Pick{a, x2}]), Spec.leaves(x2), Spec.leaves([Spec.Pick{a, x}]), Lemma.append_nil_right(Spec.leaves(x2)), Equal.trans(+List<Nat>, Spec.leaves(x2), Spec.leaves(x), Spec.leaves([Spec.Pick{a, x}]), lv, Equal.sym(+List<Nat>, Spec.leaves([Spec.Pick{a, x}]), Spec.leaves(x), Lemma.append_nil_right(Spec.leaves(x))))))
    case LoopKid{+l, +r}:
      leaves_swap(l, Spec.Loop{x}, Spec.Loop{x2}, r, Equal.trans(+List<Nat>, Spec.leaves([Spec.Loop{x2}]), Spec.leaves(x2), Spec.leaves([Spec.Loop{x}]), Lemma.append_nil_right(Spec.leaves(x2)), Equal.trans(+List<Nat>, Spec.leaves(x2), Spec.leaves(x), Spec.leaves([Spec.Loop{x}]), lv, Equal.sym(+List<Nat>, Spec.leaves([Spec.Loop{x}]), Spec.leaves(x), Lemma.append_nil_right(Spec.leaves(x))))))

# The whole tree spells the same with the forest swapped.
law leaves_zip:
  for z: +List<Frame>
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.leaves(zip(z, x2)) == Spec.leaves(zip(z, x)) : +List<Nat>}

def leaves_zip(z, x, x2, lv):
  match z:
    case Nil{}:
      lv
    case Con{+fr, +rest}:
      leaves_zip(rest, fill(fr, x), fill(fr, x2), leaves_fill(fr, x, x2, lv))

# ======== FITTING ========
#
# The items a forest must fit follow from the frames: the root fits the q0 symbol, a
# node's children its right side, a pick's children its alternative, a loop's rounds as
# many groups of its body as there are rounds.

def itemAtOr(its: +List<Spec.Item>, n: Nat) -> Spec.Item:
  match its n:
    case Nil{} _:
      Spec.Eps{}
    case Con{+it, rest} 0n:
      it
    case Con{it, +rest} 1n+m:
      itemAtOr(rest, m)

def loopItems(it: Spec.Item, +n: Nat) -> +List<Spec.Item>:
  match it:
    case Spec.Brack{kind, +alts}:
      Spec.times(n, Spec.Brack{Spec.Group{}, alts})
    case Spec.Sym{s}:
      []
    case Spec.Eps{}:
      []

def frameLeft(fr: Frame) -> +List<Spec.Tree>:
  match fr:
    case NodeKid{+l, q, r}:
      l
    case PickKid{+l, a, r}:
      l
    case LoopKid{+l, r}:
      l

# The items of the hole of a frame whose tree stands at item `it`.
def holeAt(+grammar: +List<Spec.Production>, fr: Frame, +it: Spec.Item, +x: +List<Spec.Tree>) -> +List<Spec.Item>:
  match fr:
    case NodeKid{l, +q, r}:
      Spec.rhsOf(grammar, q)
    case PickKid{l, +a, r}:
      Gll.bracketAlt(Some{it}, a)
    case LoopKid{l, r}:
      loopItems(it, List.length(&2, Spec.Tree, x))

def holeItems(+grammar: +List<Spec.Production>, +fr: Frame, +outer: +List<Spec.Item>, +x: +List<Spec.Tree>) -> +List<Spec.Item>:
  holeAt(grammar, fr, itemAtOr(outer, List.length(&2, Spec.Tree, frameLeft(fr))), x)

def holeOf(+grammar: +List<Spec.Production>, +q0: Nat, z: +List<Frame>, +x: +List<Spec.Tree>) -> +List<Spec.Item>:
  match z:
    case Nil{}:
      Spec.rhsOf(grammar, q0)
    case Con{+fr, +rest}:
      holeItems(grammar, fr, holeOf(grammar, q0, rest, fill(fr, x)), x)

# Every level fits its items.
def zipOk(+grammar: +List<Spec.Production>, +q0: Nat, z: +List<Frame>, +x: +List<Spec.Tree>) -> Bool:
  match z:
    case Nil{}:
      Spec.fits(x, grammar, Spec.rhsOf(grammar, q0))
    case Con{+fr, +rest}:
      Bool.and(Spec.fits(x, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, fill(fr, x)), x)), zipOk(grammar, q0, rest, fill(fr, x)))

def boolSame(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

# A loop's rounds swapped keep their number and whether each consumes.
def shapeOk(fr: Frame, +x: +List<Spec.Tree>, +x2: +List<Spec.Tree>) -> Bool:
  match fr:
    case NodeKid{l, q, r}:
      True{}
    case PickKid{l, a, r}:
      True{}
    case LoopKid{l, r}:
      Bool.and(Nat.is_eq(List.length(&2, Spec.Tree, x2), List.length(&2, Spec.Tree, x)), boolSame(Spec.allConsume(x2), Spec.allConsume(x)))

def zshape(z: +List<Frame>, +x: +List<Spec.Tree>, +x2: +List<Spec.Tree>) -> Bool:
  match z:
    case Nil{}:
      True{}
    case Con{+fr, rest}:
      shapeOk(fr, x, x2)

law same_sound:
  for a: Bool
  for b: Bool
  for e: {boolSame(a, b) == True{} : Bool}
  {a == b : Bool}

def same_sound(a, b, e):
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))

# The tree at position |l| fits the item there.
law app_item:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +r: +List<Spec.Tree>
  for its: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits(List.append(&2, Spec.Tree, l, t <> r), grammar, its) == True{} : Bool}
  {Spec.fits([t], grammar, [itemAtOr(its, List.length(&2, Spec.Tree, l))]) == True{} : Bool}

def app_item(l, t, r, its, grammar, e):
  match l its:
    case Nil{} Nil{}:
      Empty.absurd({Spec.fits([t], grammar, [Spec.Eps{}]) == True{} : Bool}, Fits.fits_cons_nil(t, r, grammar, e))
    case Nil{} Con{+it, +rest}:
      Fits.fits_head(t, r, grammar, it, rest, e)
    case Con{+u, +us} Nil{}:
      Empty.absurd({Spec.fits([t], grammar, [Spec.Eps{}]) == True{} : Bool}, Fits.fits_cons_nil(u, List.append(&2, Spec.Tree, us, t <> r), grammar, e))
    case Con{+u, +us} Con{+it, +rest}:
      app_item(us, t, r, rest, grammar, Fits.fits_tail(u, List.append(&2, Spec.Tree, us, t <> r), grammar, it, rest, e))

# ... and another tree that fits it there makes the forest fit too.
law app_swap:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for its: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits(List.append(&2, Spec.Tree, l, t <> r), grammar, its) == True{} : Bool}
  for +h: {Spec.fits([t2], grammar, [itemAtOr(its, List.length(&2, Spec.Tree, l))]) == True{} : Bool}
  {Spec.fits(List.append(&2, Spec.Tree, l, t2 <> r), grammar, its) == True{} : Bool}

def app_swap(l, t, t2, r, its, grammar, e, h):
  match l its:
    case Nil{} Nil{}:
      Empty.absurd({Spec.fits(t2 <> r, grammar, []) == True{} : Bool}, Fits.fits_cons_nil(t, r, grammar, e))
    case Nil{} Con{+it, +rest}:
      Fits.fits_join(t2, r, grammar, it, rest, h, Fits.fits_tail(t, r, grammar, it, rest, e))
    case Con{+u, +us} Nil{}:
      Empty.absurd({Spec.fits(u <> List.append(&2, Spec.Tree, us, t2 <> r), grammar, []) == True{} : Bool}, Fits.fits_cons_nil(u, List.append(&2, Spec.Tree, us, t <> r), grammar, e))
    case Con{+u, +us} Con{+it, +rest}:
      +tl = List.append(&2, Spec.Tree, us, t <> r)
      Fits.fits_join(u, List.append(&2, Spec.Tree, us, t2 <> r), grammar, it, rest, Fits.fits_head(u, tl, grammar, it, rest, e), app_swap(us, t, t2, r, rest, grammar, Fits.fits_tail(u, tl, grammar, it, rest, e), h))

# [ τ ] read once: whether its one round consumes depends on what it spells.
def optOk(+w: +List<Nat>) -> Bool:
  Bool.and(Bool.not(Nat.is_lt(1n, 0n)), Bool.or(Bool.and(Bool.not(List.is_empty(&2, Nat, w)), True{}), Nat.is_eq(1n, 0n)))

def roundsVal(+kind: Spec.Bracket, +n: Nat, +c: Bool) -> Bool:
  Bool.and(Bool.not(Nat.is_lt(n, Spec.minRounds(kind))), Bool.or(c, Nat.is_eq(n, Spec.minRounds(kind))))

law rounds_val:
  for +kind: Spec.Bracket
  for +x: +List<Spec.Tree>
  {Spec.roundsOk(kind, x) == roundsVal(kind, List.length(&2, Spec.Tree, x), Spec.allConsume(x)) : Bool}

def rounds_val(kind, x):
  {==}

law rounds_same:
  for +kind: Spec.Bracket
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +sh: {Bool.and(Nat.is_eq(List.length(&2, Spec.Tree, x2), List.length(&2, Spec.Tree, x)), boolSame(Spec.allConsume(x2), Spec.allConsume(x))) == True{} : Bool}
  {Spec.roundsOk(kind, x2) == Spec.roundsOk(kind, x) : Bool}

def rounds_same(kind, x, x2, sh):
  +n2 = List.length(&2, Spec.Tree, x2)
  +n = List.length(&2, Spec.Tree, x)
  +eN = Lemma.nat_eq_sound(n2, n, Lemma.and_true_left(Nat.is_eq(n2, n), boolSame(Spec.allConsume(x2), Spec.allConsume(x)), sh))
  +eC = same_sound(Spec.allConsume(x2), Spec.allConsume(x), Lemma.and_true_right_side(Nat.is_eq(n2, n), boolSame(Spec.allConsume(x2), Spec.allConsume(x)), sh))
  Equal.trans(Bool, Spec.roundsOk(kind, x2), roundsVal(kind, n2, Spec.allConsume(x2)), Spec.roundsOk(kind, x), rounds_val(kind, x2),
    Equal.trans(Bool, roundsVal(kind, n2, Spec.allConsume(x2)), roundsVal(kind, n, Spec.allConsume(x)), Spec.roundsOk(kind, x),
      Equal.trans(Bool, roundsVal(kind, n2, Spec.allConsume(x2)), roundsVal(kind, n, Spec.allConsume(x2)), roundsVal(kind, n, Spec.allConsume(x)), Equal.cong(Nat, Bool, v => roundsVal(kind, v, Spec.allConsume(x2)), n2, n, eN), Equal.cong(Bool, Bool, v => roundsVal(kind, n, v), Spec.allConsume(x2), Spec.allConsume(x), eC)),
      Equal.sym(Bool, Spec.roundsOk(kind, x), roundsVal(kind, n, Spec.allConsume(x)), rounds_val(kind, x))))

law and3_true:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for e: {Bool.and(Bool.and(a, b), c) == True{} : Bool}
  {a == True{} : Bool}

def and3_true(a, b, c, e):
  Lemma.and_true_left(a, b, Lemma.and_true_left(Bool.and(a, b), c, e))

law loop_swap:
  for it: Spec.Item
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits([Spec.Loop{x}], grammar, [it]) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, loopItems(it, List.length(&2, Spec.Tree, x2))) == True{} : Bool}
  for +sh: {Bool.and(Nat.is_eq(List.length(&2, Spec.Tree, x2), List.length(&2, Spec.Tree, x)), boolSame(Spec.allConsume(x2), Spec.allConsume(x))) == True{} : Bool}
  {Spec.fits([Spec.Loop{x2}], grammar, [it]) == True{} : Bool}

def loop_swap(it, x, x2, grammar, e, h, sh):
  match it:
    case Spec.Brack{Spec.Closure{}, +alts}:
      +ro = Spec.roundsOk(Spec.Closure{}, x)
      +roT = and3_true(ro, Spec.fits(x, grammar, Spec.times(List.length(&2, Spec.Tree, x), Spec.Brack{Spec.Group{}, alts})), True{}, e)
      +ro2T = Equal.trans(Bool, Spec.roundsOk(Spec.Closure{}, x2), ro, True{}, rounds_same(Spec.Closure{}, x, x2, sh), roT)
      Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, x2), Spec.fits(x2, grammar, Spec.times(List.length(&2, Spec.Tree, x2), Spec.Brack{Spec.Group{}, alts}))), True{}, Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, x2), Spec.fits(x2, grammar, Spec.times(List.length(&2, Spec.Tree, x2), Spec.Brack{Spec.Group{}, alts})), ro2T, h), {==})
    case Spec.Brack{Spec.Positive{}, +alts}:
      +ro = Spec.roundsOk(Spec.Positive{}, x)
      +roT = and3_true(ro, Spec.fits(x, grammar, Spec.times(List.length(&2, Spec.Tree, x), Spec.Brack{Spec.Group{}, alts})), True{}, e)
      +ro2T = Equal.trans(Bool, Spec.roundsOk(Spec.Positive{}, x2), ro, True{}, rounds_same(Spec.Positive{}, x, x2, sh), roT)
      Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, x2), Spec.fits(x2, grammar, Spec.times(List.length(&2, Spec.Tree, x2), Spec.Brack{Spec.Group{}, alts}))), True{}, Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, x2), Spec.fits(x2, grammar, Spec.times(List.length(&2, Spec.Tree, x2), Spec.Brack{Spec.Group{}, alts})), ro2T, h), {==})
    case Spec.Brack{Spec.Group{}, alts}:
      Empty.absurd({Spec.fits([Spec.Loop{x2}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Optional{}, alts}:
      Empty.absurd({Spec.fits([Spec.Loop{x2}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Sym{s}:
      Empty.absurd({Spec.fits([Spec.Loop{x2}], grammar, [Spec.Sym{s}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits([Spec.Loop{x2}], grammar, [Spec.Eps{}]) == True{} : Bool}, Lemma.false_is_not_true(e))

law node_swap:
  for it: Spec.Item
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits([Spec.Node{q, x}], grammar, [it]) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  {Spec.fits([Spec.Node{q, x2}], grammar, [it]) == True{} : Bool}

def node_swap(it, q, x, x2, grammar, e, h):
  match it:
    case Spec.Sym{Spec.Nonterminal{+n}}:
      +lh = and3_true(Spec.lhsIs(grammar, q, n), Spec.fits(x, grammar, Spec.rhsOf(grammar, q)), True{}, e)
      Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, q, n), Spec.fits(x2, grammar, Spec.rhsOf(grammar, q))), True{}, Lemma.and_true_intro(Spec.lhsIs(grammar, q, n), Spec.fits(x2, grammar, Spec.rhsOf(grammar, q)), lh, h), {==})
    case Spec.Sym{Spec.Terminal{k}}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Sym{Spec.Terminal{k}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Group{}, alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Optional{}, alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Closure{}, alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Positive{}, alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits([Spec.Node{q, x2}], grammar, [Spec.Eps{}]) == True{} : Bool}, Lemma.false_is_not_true(e))

law pick_swap:
  for it: Spec.Item
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits([Spec.Pick{a, x}], grammar, [it]) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, Gll.bracketAlt(Some{it}, a)) == True{} : Bool}
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.fits([Spec.Pick{a, x2}], grammar, [it]) == True{} : Bool}

def pick_swap(it, a, x, x2, grammar, e, h, lv):
  match it:
    case Spec.Brack{Spec.Group{}, +alts}:
      +isA = and3_true(Spec.isAlt(alts, a), Spec.fits(x, grammar, Spec.altOf(alts, a)), True{}, e)
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(x2, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(x2, grammar, Spec.altOf(alts, a)), isA, h), {==})
    case Spec.Brack{Spec.Optional{}, +alts}:
      +ro = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, x}])
      +ro2 = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, x2}])
      +inner = and3_true(Bool.and(ro, Spec.isAlt(alts, a)), Spec.fits(x, grammar, Spec.altOf(alts, a)), True{}, e)
      +roT = Lemma.and_true_left(ro, Spec.isAlt(alts, a), inner)
      +isA = Lemma.and_true_right_side(ro, Spec.isAlt(alts, a), inner)
      +roEq = Equal.cong(+List<Nat>, Bool, v => optOk(v), List.append(&2, Nat, Spec.leaves(x2), []), List.append(&2, Nat, Spec.leaves(x), []), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(x2), Spec.leaves(x), lv))
      +ro2T = Equal.trans(Bool, ro2, ro, True{}, roEq, roT)
      Lemma.and_true_intro(Bool.and(Bool.and(ro2, Spec.isAlt(alts, a)), Spec.fits(x2, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_intro(Bool.and(ro2, Spec.isAlt(alts, a)), Spec.fits(x2, grammar, Spec.altOf(alts, a)), Lemma.and_true_intro(ro2, Spec.isAlt(alts, a), ro2T, isA), h), {==})
    case Spec.Brack{Spec.Closure{}, alts}:
      Empty.absurd({Spec.fits([Spec.Pick{a, x2}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{Spec.Positive{}, alts}:
      Empty.absurd({Spec.fits([Spec.Pick{a, x2}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Sym{s}:
      Empty.absurd({Spec.fits([Spec.Pick{a, x2}], grammar, [Spec.Sym{s}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits([Spec.Pick{a, x2}], grammar, [Spec.Eps{}]) == True{} : Bool}, Lemma.false_is_not_true(e))

# One tree: its children swapped for a forest that fits the hole.
law tree_swap:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for it: Spec.Item
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits([wrap(fr, x)], grammar, [it]) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, holeAt(grammar, fr, it, x2)) == True{} : Bool}
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for +sh: {shapeOk(fr, x, x2) == True{} : Bool}
  {Spec.fits([wrap(fr, x2)], grammar, [it]) == True{} : Bool}

def tree_swap(fr, x, x2, it, grammar, e, h, lv, sh):
  match fr:
    case NodeKid{l, +q, r}:
      node_swap(it, q, x, x2, grammar, e, h)
    case PickKid{l, +a, r}:
      pick_swap(it, a, x, x2, grammar, e, h, lv)
    case LoopKid{l, r}:
      loop_swap(it, x, x2, grammar, e, h, sh)

# A frame's forest with the hole filled by another forest that fits the hole.
law fill_swap:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +outer: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +e: {Spec.fits(fill(fr, x), grammar, outer) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, holeItems(grammar, fr, outer, x2)) == True{} : Bool}
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for +sh: {shapeOk(fr, x, x2) == True{} : Bool}
  {Spec.fits(fill(fr, x2), grammar, outer) == True{} : Bool}

def fill_swap(fr, x, x2, outer, grammar, e, h, lv, sh):
  match fr:
    case NodeKid{+l, +q, +r}:
      +it = itemAtOr(outer, List.length(&2, Spec.Tree, l))
      +te = app_item(l, Spec.Node{q, x}, r, outer, grammar, e)
      app_swap(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, outer, grammar, e, tree_swap(NodeKid{l, q, r}, x, x2, it, grammar, te, h, lv, sh))
    case PickKid{+l, +a, +r}:
      +it = itemAtOr(outer, List.length(&2, Spec.Tree, l))
      +te = app_item(l, Spec.Pick{a, x}, r, outer, grammar, e)
      app_swap(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, outer, grammar, e, tree_swap(PickKid{l, a, r}, x, x2, it, grammar, te, h, lv, sh))
    case LoopKid{+l, +r}:
      +it = itemAtOr(outer, List.length(&2, Spec.Tree, l))
      +te = app_item(l, Spec.Loop{x}, r, outer, grammar, e)
      app_swap(l, Spec.Loop{x}, Spec.Loop{x2}, r, outer, grammar, e, tree_swap(LoopKid{l, r}, x, x2, it, grammar, te, h, lv, sh))

law len_swap:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  {List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, l, t2 <> r)) == List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, l, t <> r)) : Nat}

def len_swap(l, t, t2, r):
  match l:
    case Nil{}:
      {==}
    case Con{+u, +us}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, us, t2 <> r)), List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, us, t <> r)), len_swap(us, t, t2, r))

law fill_len:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  {List.length(&2, Spec.Tree, fill(fr, x2)) == List.length(&2, Spec.Tree, fill(fr, x)) : Nat}

def fill_len(fr, x, x2):
  match fr:
    case NodeKid{+l, +q, +r}:
      len_swap(l, Spec.Node{q, x}, Spec.Node{q, x2}, r)
    case PickKid{+l, +a, +r}:
      len_swap(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r)
    case LoopKid{+l, +r}:
      len_swap(l, Spec.Loop{x}, Spec.Loop{x2}, r)

law hole_len:
  for +fr: Frame
  for +grammar: +List<Spec.Production>
  for +it: Spec.Item
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +eq: {List.length(&2, Spec.Tree, x2) == List.length(&2, Spec.Tree, x) : Nat}
  {holeAt(grammar, fr, it, x2) == holeAt(grammar, fr, it, x) : +List<Spec.Item>}

def hole_len(fr, grammar, it, x, x2, eq):
  match fr:
    case NodeKid{l, +q, r}:
      {==}
    case PickKid{l, +a, r}:
      {==}
    case LoopKid{l, r}:
      Equal.cong(Nat, +List<Spec.Item>, v => loopItems(it, v), List.length(&2, Spec.Tree, x2), List.length(&2, Spec.Tree, x), eq)

# The hole's items depend on the forest in it only through how many trees it has.
law holeof_len:
  for z: +List<Frame>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +eq: {List.length(&2, Spec.Tree, y2) == List.length(&2, Spec.Tree, y) : Nat}
  {holeOf(grammar, q0, z, y2) == holeOf(grammar, q0, z, y) : +List<Spec.Item>}

def holeof_len(z, grammar, q0, y, y2, eq):
  match z:
    case Nil{}:
      {==}
    case Con{+fr, +rest}:
      +o2 = holeOf(grammar, q0, rest, fill(fr, y2))
      +o = holeOf(grammar, q0, rest, fill(fr, y))
      +oe = holeof_len(rest, grammar, q0, fill(fr, y), fill(fr, y2), fill_len(fr, y, y2))
      +n = List.length(&2, Spec.Tree, frameLeft(fr))
      Equal.trans(+List<Spec.Item>, holeAt(grammar, fr, itemAtOr(o2, n), y2), holeAt(grammar, fr, itemAtOr(o, n), y2), holeAt(grammar, fr, itemAtOr(o, n), y),
        Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => holeAt(grammar, fr, itemAtOr(v, n), y2), o2, o, oe), hole_len(fr, grammar, itemAtOr(o, n), y, y2, eq))

law cons_swap:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +lvT: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.allConsume(List.append(&2, Spec.Tree, l, t2 <> r)) == Spec.allConsume(List.append(&2, Spec.Tree, l, t <> r)) : Bool}

def cons_swap(l, t, t2, r, lvT):
  match l:
    case Nil{}:
      Equal.cong(+List<Nat>, Bool, v => Bool.and(Bool.not(List.is_empty(&2, Nat, v)), Spec.allConsume(r)), Spec.leaves([t2]), Spec.leaves([t]), lvT)
    case Con{+u, +us}:
      Equal.cong(Bool, Bool, v => Bool.and(Spec.consumes(u), v), Spec.allConsume(List.append(&2, Spec.Tree, us, t2 <> r)), Spec.allConsume(List.append(&2, Spec.Tree, us, t <> r)), cons_swap(us, t, t2, r, lvT))

law wrap_lv:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.leaves([wrap(fr, x2)]) == Spec.leaves([wrap(fr, x)]) : +List<Nat>}

def wrap_lv(fr, x, x2, lv):
  Equal.trans(+List<Nat>, Spec.leaves([wrap(fr, x2)]), Spec.leaves(x2), Spec.leaves([wrap(fr, x)]), wrap_leaves(fr, x2), Equal.trans(+List<Nat>, Spec.leaves(x2), Spec.leaves(x), Spec.leaves([wrap(fr, x)]), lv, Equal.sym(+List<Nat>, Spec.leaves([wrap(fr, x)]), Spec.leaves(x), wrap_leaves(fr, x))))

law consume_fill:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.allConsume(fill(fr, x2)) == Spec.allConsume(fill(fr, x)) : Bool}

def consume_fill(fr, x, x2, lv):
  match fr:
    case NodeKid{+l, +q, +r}:
      cons_swap(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, wrap_lv(NodeKid{l, q, r}, x, x2, lv))
    case PickKid{+l, +a, +r}:
      cons_swap(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, wrap_lv(PickKid{l, a, r}, x, x2, lv))
    case LoopKid{+l, +r}:
      cons_swap(l, Spec.Loop{x}, Spec.Loop{x2}, r, wrap_lv(LoopKid{l, r}, x, x2, lv))

law same_refl:
  for b: Bool
  {boolSame(b, b) == True{} : Bool}

def same_refl(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law shape_next:
  for +f2: Frame
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {shapeOk(f2, fill(fr, x), fill(fr, x2)) == True{} : Bool}

def shape_next(f2, fr, x, x2, lv):
  match f2:
    case NodeKid{l, q, r}:
      {==}
    case PickKid{l, a, r}:
      {==}
    case LoopKid{l, r}:
      +y = fill(fr, x)
      +y2 = fill(fr, x2)
      +eN = Equal.trans(Bool, Nat.is_eq(List.length(&2, Spec.Tree, y2), List.length(&2, Spec.Tree, y)), Nat.is_eq(List.length(&2, Spec.Tree, y), List.length(&2, Spec.Tree, y)), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(v, List.length(&2, Spec.Tree, y)), List.length(&2, Spec.Tree, y2), List.length(&2, Spec.Tree, y), fill_len(fr, x, x2)), Lemma.nat_eq_refl(List.length(&2, Spec.Tree, y)))
      +eC = Equal.trans(Bool, boolSame(Spec.allConsume(y2), Spec.allConsume(y)), boolSame(Spec.allConsume(y), Spec.allConsume(y)), True{}, Equal.cong(Bool, Bool, v => boolSame(v, Spec.allConsume(y)), Spec.allConsume(y2), Spec.allConsume(y), consume_fill(fr, x, x2, lv)), same_refl(Spec.allConsume(y)))
      Lemma.and_true_intro(Nat.is_eq(List.length(&2, Spec.Tree, y2), List.length(&2, Spec.Tree, y)), boolSame(Spec.allConsume(y2), Spec.allConsume(y)), eN, eC)

# Filled frames keep the shape the next frame up asks for.
law zshape_next:
  for rest: +List<Frame>
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {zshape(rest, fill(fr, x), fill(fr, x2)) == True{} : Bool}

def zshape_next(rest, fr, x, x2, lv):
  match rest:
    case Nil{}:
      {==}
    case Con{+f2, r2}:
      shape_next(f2, fr, x, x2, lv)

law zip_head:
  for z: +List<Frame>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +ok: {zipOk(grammar, q0, z, y) == True{} : Bool}
  {Spec.fits(y, grammar, holeOf(grammar, q0, z, y)) == True{} : Bool}

def zip_head(z, grammar, q0, y, ok):
  match z:
    case Nil{}:
      ok
    case Con{+fr, +rest}:
      Lemma.and_true_left(Spec.fits(y, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, fill(fr, y)), y)), zipOk(grammar, q0, rest, fill(fr, y)), ok)

# PLUGGING, FITTING: a forest swapped for one that fits its hole and spells the same
# leaves every level fitting.
law zip_swap:
  for z: +List<Frame>
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +ok: {zipOk(grammar, q0, z, x) == True{} : Bool}
  for +h: {Spec.fits(x2, grammar, holeOf(grammar, q0, z, x2)) == True{} : Bool}
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for +sh: {zshape(z, x, x2) == True{} : Bool}
  {zipOk(grammar, q0, z, x2) == True{} : Bool}

def zip_swap(z, x, x2, grammar, q0, ok, h, lv, sh):
  match z:
    case Nil{}:
      h
    case Con{+fr, +rest}:
      +y = fill(fr, x)
      +y2 = fill(fr, x2)
      +okR = Lemma.and_true_right_side(Spec.fits(x, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, y), x)), zipOk(grammar, q0, rest, y), ok)
      +eY = zip_head(rest, grammar, q0, y, okR)
      +oe = holeof_len(rest, grammar, q0, y, y2, fill_len(fr, x, x2))
      +eY2 = Equal.trans(Bool, Spec.fits(y, grammar, holeOf(grammar, q0, rest, y2)), Spec.fits(y, grammar, holeOf(grammar, q0, rest, y)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(y, grammar, v), holeOf(grammar, q0, rest, y2), holeOf(grammar, q0, rest, y), oe), eY)
      +hY2 = fill_swap(fr, x, x2, holeOf(grammar, q0, rest, y2), grammar, eY2, h, lv, sh)
      Lemma.and_true_intro(Spec.fits(x2, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, y2), x2)), zipOk(grammar, q0, rest, y2), h, zip_swap(rest, y, y2, grammar, q0, okR, hY2, leaves_fill(fr, x, x2, lv), zshape_next(rest, fr, x, x2, lv)))

# ======== STEPS ========
#
# Where a forest is walked: in a sequence (r = False) from item d, or as the rounds of a
# loop (r = True), at index idx and path prefix pre, its sequence started at i, its first
# tree at k. The root's children are walked at (False, q, [], 0, 0, 0).

type Coord is Data:
  Coord{r: Bool, idx: Nat, pre: +List<Nat>, d: Nat, i: Nat, k: Nat}

def cR(c: Coord) -> Bool:
  match c:
    case Coord{+r, idx, pre, d, i, k}:
      r
def cIdx(c: Coord) -> Nat:
  match c:
    case Coord{r, +idx, pre, d, i, k}:
      idx
def cPre(c: Coord) -> +List<Nat>:
  match c:
    case Coord{r, idx, +pre, d, i, k}:
      pre
def cD(c: Coord) -> Nat:
  match c:
    case Coord{r, idx, pre, +d, i, k}:
      d
def cI(c: Coord) -> Nat:
  match c:
    case Coord{r, idx, pre, d, +i, k}:
      i
def cK(c: Coord) -> Nat:
  match c:
    case Coord{r, idx, pre, d, i, +k}:
      k

def walkAt(+c: Coord, +f: +List<Spec.Tree>) -> +List<Spec.Bsr>:
  Spec.walk(f, cR(c), cIdx(c), cPre(c), cD(c), cI(c), cK(c))

# A pick's children: in a sequence, under the item's path and the pick's alternative;
# in a loop's rounds, under the round's alternative, the sequence started where the loop did.
def pickPre(r: Bool, +pre: +List<Nat>, +d: Nat, +a: Nat) -> +List<Nat>:
  match r:
    case False{}:
      List.append(&2, Nat, pre, [d, a])
    case True{}:
      List.append(&2, Nat, pre, [a])

def pickI(r: Bool, +i: Nat, +kk: Nat) -> Nat:
  match r:
    case False{}:
      kk
    case True{}:
      i

def holeCoord(fr: Frame, +c: Coord) -> Coord:
  match fr:
    case NodeKid{+l, +q, r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      Coord{False{}, q, [], 0n, kk, kk}
    case PickKid{+l, +a, r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      Coord{False{}, cIdx(c), pickPre(cR(c), cPre(c), Nat.add(cD(c), List.length(&2, Spec.Tree, l)), a), 0n, pickI(cR(c), cI(c), kk), kk}
    case LoopKid{+l, r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      Coord{True{}, cIdx(c), List.append(&2, Nat, cPre(c), [Nat.add(cD(c), List.length(&2, Spec.Tree, l))]), 0n, kk, kk}

# The root's children are walked at (False, q0, [], 0, 0, 0).
def coordOf(+q0: Nat, z: +List<Frame>) -> Coord:
  match z:
    case Nil{}:
      Coord{False{}, q0, [], 0n, 0n, 0n}
    case Con{+fr, +rest}:
      holeCoord(fr, coordOf(q0, rest))

law member_l_pick:
  for +y: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +zs: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for cases: Either<{e == y : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for later: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Spec.bsrMember(e, List.append(&2, Spec.Bsr, rest, zs)) == True{} : Bool}
  {Spec.bsrMember(e, y <> List.append(&2, Spec.Bsr, rest, zs)) == True{} : Bool}

def member_l_pick(y, rest, zs, e, cases, later):
  match cases:
    case Inl{same0}:
      +same = {same0 : {e == y : Spec.Bsr}}
      Equal.trans(Bool, Spec.bsrMember(e, y <> List.append(&2, Spec.Bsr, rest, zs)), Spec.bsrMember(y, y <> List.append(&2, Spec.Bsr, rest, zs)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, y <> List.append(&2, Spec.Bsr, rest, zs)), e, y, same), R.bsr_member_head(y, List.append(&2, Spec.Bsr, rest, zs)))
    case Inr{m}:
      R.bsr_member_cons(e, y, List.append(&2, Spec.Bsr, rest, zs), later(m))

# ---- Sub-lists ----

law member_app_l:
  for ys: +List<Spec.Bsr>
  for +zs: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  {Spec.bsrMember(e, List.append(&2, Spec.Bsr, ys, zs)) == True{} : Bool}

def member_app_l(ys, zs, e, m):
  match ys:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(e, zs) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+y, +rest}:
      member_l_pick(y, rest, zs, e, G.ebnf_member_cases(e, y, rest, m), later => member_app_l(rest, zs, e, later))

law all_app_l:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +zs: +List<Spec.Bsr>
  for +h: {Spec.allIn(xs, ys) == True{} : Bool}
  {Spec.allIn(xs, List.append(&2, Spec.Bsr, ys, zs)) == True{} : Bool}

def all_app_l(xs, ys, zs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(x, List.append(&2, Spec.Bsr, ys, zs)), Spec.allIn(rest, List.append(&2, Spec.Bsr, ys, zs)), member_app_l(ys, zs, x, Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)), all_app_l(rest, ys, zs, Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)))

law all_app_r:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +zs: +List<Spec.Bsr>
  for +h: {Spec.allIn(xs, zs) == True{} : Bool}
  {Spec.allIn(xs, List.append(&2, Spec.Bsr, ys, zs)) == True{} : Bool}

def all_app_r(xs, ys, zs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(x, List.append(&2, Spec.Bsr, ys, zs)), Spec.allIn(rest, List.append(&2, Spec.Bsr, ys, zs)), Sub.member_app_right(ys, zs, x, Lemma.and_true_left(Spec.bsrMember(x, zs), Spec.allIn(rest, zs), h)), all_app_r(rest, ys, zs, Lemma.and_true_right_side(Spec.bsrMember(x, zs), Spec.allIn(rest, zs), h)))

law all_cons:
  for xs: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +ys: +List<Spec.Bsr>
  for +h: {Spec.allIn(xs, ys) == True{} : Bool}
  {Spec.allIn(xs, y <> ys) == True{} : Bool}

def all_cons(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(x, y <> ys), Spec.allIn(rest, y <> ys), R.bsr_member_cons(x, y, ys, Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)), all_cons(rest, y, ys, Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)))

law all_self:
  for xs: +List<Spec.Bsr>
  {Spec.allIn(xs, xs) == True{} : Bool}

def all_self(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(x, x <> rest), Spec.allIn(rest, x <> rest), R.bsr_member_head(x, rest), all_cons(rest, x, rest, all_self(rest)))

law all_trans:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +zs: +List<Spec.Bsr>
  for +h1: {Spec.allIn(xs, ys) == True{} : Bool}
  for +h2: {Spec.allIn(ys, zs) == True{} : Bool}
  {Spec.allIn(xs, zs) == True{} : Bool}

def all_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +mx = Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h1)
      Lemma.and_true_intro(Spec.bsrMember(x, zs), Spec.allIn(rest, zs), G.ebnf_all_in_member(ys, zs, x, h2, mx), all_trans(rest, ys, zs, Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h1), h2))

law len_leaves_cons:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +k: Nat
  {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), List.length(&2, Nat, Spec.leaves(ts))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))) : Nat}

def len_leaves_cons(t, ts, k):
  +a = List.length(&2, Nat, Spec.leaves([t]))
  +b = List.length(&2, Nat, Spec.leaves(ts))
  Equal.trans(Nat, Nat.add(Nat.add(k, a), b), Nat.add(k, Nat.add(a, b)), Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))), Lemma.add_assoc(k, a, b),
    Equal.cong(Nat, Nat, v => Nat.add(k, v), Nat.add(a, b), List.length(&2, Nat, Spec.leaves(t <> ts)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), Nat.add(a, b),
      Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), List.length(&2, Nat, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts))), Nat.add(a, b), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Sub.leaves_cons(t, ts)), Lemma.length_append(Spec.leaves([t]), Spec.leaves(ts))))))

# Where the walk of u <> rest goes on, as a sum.
law end_sum:
  for +u: Spec.Tree
  for +us: +List<Spec.Tree>
  for +k: Nat
  {Nat.add(Sub.endOf(u, k), List.length(&2, Nat, Spec.leaves(us))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us))) : Nat}

def end_sum(u, us, k):
  Equal.trans(Nat, Nat.add(Sub.endOf(u, k), List.length(&2, Nat, Spec.leaves(us))), Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves([u]))), List.length(&2, Nat, Spec.leaves(us))), Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us))),
    Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves(us))), Sub.endOf(u, k), Nat.add(k, List.length(&2, Nat, Spec.leaves([u]))), Sub.end_of_one(u, k)), len_leaves_cons(u, us, k))

# The walk of a sequence's tail is part of the walk of the sequence.
law seq_tail:
  for l: +List<Spec.Tree>
  for +f: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  {Spec.allIn(Spec.walk(f, False{}, idx, pre, Nat.add(d, List.length(&2, Spec.Tree, l)), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(l)))), Spec.walk(List.append(&2, Spec.Tree, l, f), False{}, idx, pre, d, i, k)) == True{} : Bool}

def seq_tail(l, f, idx, pre, d, i, k):
  match l:
    case Nil{}:
      +w = Spec.walk(f, False{}, idx, pre, d, i, k)
      +e1 = Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(f, False{}, idx, pre, v, i, Nat.add(k, 0n)), w), Nat.add(d, 0n), d, Lemma.add_zero_right(d))
      +e2 = Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(f, False{}, idx, pre, d, i, v), w), Nat.add(k, 0n), k, Lemma.add_zero_right(k))
      Equal.trans(Bool, Spec.allIn(Spec.walk(f, False{}, idx, pre, Nat.add(d, 0n), i, Nat.add(k, 0n)), w), Spec.allIn(Spec.walk(f, False{}, idx, pre, d, i, Nat.add(k, 0n)), w), True{}, e1, Equal.trans(Bool, Spec.allIn(Spec.walk(f, False{}, idx, pre, d, i, Nat.add(k, 0n)), w), Spec.allIn(w, w), True{}, e2, all_self(w)))
    case Con{+u, +us}:
      +rest = List.append(&2, Spec.Tree, us, f)
      +e = Sub.endOf(u, k)
      +ih = seq_tail(us, f, idx, pre, 1n+d, i, e)
      +dEq = Equal.sym(Nat, Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), 1n+Nat.add(d, List.length(&2, Spec.Tree, us)), Lemma.add_succ_right(d, List.length(&2, Spec.Tree, us)))
      +kEq = end_sum(u, us, k)
      +target = Spec.walk(f, False{}, idx, pre, Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us))))
      +src = Spec.walk(f, False{}, idx, pre, Nat.add(1n+d, List.length(&2, Spec.Tree, us)), i, Nat.add(e, List.length(&2, Nat, Spec.leaves(us))))
      +wEq = Equal.trans(+List<Spec.Bsr>, target, Spec.walk(f, False{}, idx, pre, Nat.add(1n+d, List.length(&2, Spec.Tree, us)), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us)))), src,
        Equal.cong(Nat, +List<Spec.Bsr>, v => Spec.walk(f, False{}, idx, pre, v, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us)))), Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), Nat.add(1n+d, List.length(&2, Spec.Tree, us)), Equal.sym(Nat, Nat.add(1n+d, List.length(&2, Spec.Tree, us)), Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), Equal.sym(Nat, Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), Nat.add(1n+d, List.length(&2, Spec.Tree, us)), Equal.sym(Nat, Nat.add(1n+d, List.length(&2, Spec.Tree, us)), Nat.add(d, 1n+List.length(&2, Spec.Tree, us)), dEq)))),
        Equal.cong(Nat, +List<Spec.Bsr>, v => Spec.walk(f, False{}, idx, pre, Nat.add(1n+d, List.length(&2, Spec.Tree, us)), i, v), Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us))), Nat.add(e, List.length(&2, Nat, Spec.leaves(us))), Equal.sym(Nat, Nat.add(e, List.length(&2, Nat, Spec.leaves(us))), Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us))), kEq)))
      +wTail = Spec.walk(rest, False{}, idx, pre, 1n+d, i, e)
      +inner = Sub.inner(u, idx, pre, d, k)
      +hd = Spec.at(idx, pre, 1n+d, i, k, e)
      +step = all_cons(src, hd, List.append(&2, Spec.Bsr, inner, wTail), all_app_r(src, inner, wTail, ih))
      +wc = Sub.walk_cons(u, rest, idx, pre, d, i, k)
      +step2 = Equal.trans(Bool, Spec.allIn(src, Spec.walk(u <> rest, False{}, idx, pre, d, i, k)), Spec.allIn(src, hd <> List.append(&2, Spec.Bsr, inner, wTail)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(src, v), Spec.walk(u <> rest, False{}, idx, pre, d, i, k), hd <> List.append(&2, Spec.Bsr, inner, wTail), wc), step)
      Equal.trans(Bool, Spec.allIn(target, Spec.walk(u <> rest, False{}, idx, pre, d, i, k)), Spec.allIn(src, Spec.walk(u <> rest, False{}, idx, pre, d, i, k)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, Spec.walk(u <> rest, False{}, idx, pre, d, i, k)), target, src, wEq), step2)

law rounds_tail_u:
  for u: Spec.Tree
  for +us: +List<Spec.Tree>
  for +f: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +mm: Nat
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +fit: {Spec.fits(u <> List.append(&2, Spec.Tree, us, f), grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(mm, Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for ih: {Spec.fits(List.append(&2, Spec.Tree, us, f), grammar, Spec.times(mm, Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} -> {Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(Sub.endOf(u, k), List.length(&2, Nat, Spec.leaves(us)))), Spec.walk(List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, Sub.endOf(u, k))) == True{} : Bool}
  {Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us)))), Spec.walk(u <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}

def rounds_tail_u(u, us, f, idx, pre, i, k, mm, alts, grammar, fit, ih):
  match u:
    case Spec.Pick{+a, +ch}:
      +rest = List.append(&2, Spec.Tree, us, f)
      +item = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +its = Spec.times(mm, item)
      +e = Sub.endOf(Spec.Pick{a, ch}, k)
      +r1 = ih(Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, item, its, fit))
      +src = Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(e, List.length(&2, Nat, Spec.leaves(us))))
      +target = Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> us))))
      +wEq = Equal.cong(Nat, +List<Spec.Bsr>, v => Spec.walk(f, True{}, idx, pre, 0n, i, v), Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> us))), Nat.add(e, List.length(&2, Nat, Spec.leaves(us))), Equal.sym(Nat, Nat.add(e, List.length(&2, Nat, Spec.leaves(us))), Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> us))), end_sum(Spec.Pick{a, ch}, us, k)))
      +r2 = all_app_r(src, Spec.walk(ch, False{}, idx, List.append(&2, Nat, pre, [a]), 0n, i, k), Spec.walk(rest, True{}, idx, pre, 0n, i, e), r1)
      Equal.trans(Bool, Spec.allIn(target, Spec.walk(Spec.Pick{a, ch} <> rest, True{}, idx, pre, 0n, i, k)), Spec.allIn(src, Spec.walk(Spec.Pick{a, ch} <> rest, True{}, idx, pre, 0n, i, k)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, Spec.walk(Spec.Pick{a, ch} <> rest, True{}, idx, pre, 0n, i, k)), target, src, wEq), r2)
    case Spec.Leaf{t}:
      Empty.absurd({Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{t} <> us)))), Spec.walk(Spec.Leaf{t} <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Spec.Node{q, ch}:
      Empty.absurd({Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> us)))), Spec.walk(Spec.Node{q, ch} <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Spec.Skip{}:
      Empty.absurd({Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> us)))), Spec.walk(Spec.Skip{} <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> us)))), Spec.walk(Spec.Loop{rs} <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}, Lemma.false_is_not_true(fit))

# The walk of a loop's later rounds is part of the walk of its rounds.
law rounds_tail:
  for l: +List<Spec.Tree>
  for +f: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +k: Nat
  for m: Nat
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +fit: {Spec.fits(List.append(&2, Spec.Tree, l, f), grammar, Spec.times(m, Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  {Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(l)))), Spec.walk(List.append(&2, Spec.Tree, l, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}

def rounds_tail(l, f, idx, pre, i, k, m, alts, grammar, fit):
  match l m:
    case Nil{} _:
      +w = Spec.walk(f, True{}, idx, pre, 0n, i, k)
      Equal.trans(Bool, Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, 0n)), w), Spec.allIn(w, w), True{}, Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, v), w), Nat.add(k, 0n), k, Lemma.add_zero_right(k)), all_self(w))
    case Con{+u, +us} 0n:
      Empty.absurd({Spec.allIn(Spec.walk(f, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(u <> us)))), Spec.walk(u <> List.append(&2, Spec.Tree, us, f), True{}, idx, pre, 0n, i, k)) == True{} : Bool}, Fits.fits_cons_nil(u, List.append(&2, Spec.Tree, us, f), grammar, fit))
    case Con{+u, +us} 1n+(+mm):
      rounds_tail_u(u, us, f, idx, pre, i, k, mm, alts, grammar, fit, ft => rounds_tail(us, f, idx, pre, i, Sub.endOf(u, k), mm, alts, grammar, ft))

# ---- The hole's walk inside its tree's walk ----

law node_head:
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  {Spec.allIn(Spec.walk(x, False{}, q, [], 0n, k, k), Spec.walk(Spec.Node{q, x} <> r, False{}, idx, pre, d, i, k)) == True{} : Bool}

def node_head(q, x, r, idx, pre, d, i, k):
  +wx = Spec.walk(x, False{}, q, [], 0n, k, k)
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(x)))
  all_cons(wx, Spec.at(idx, pre, 1n+d, i, k, e), List.append(&2, Spec.Bsr, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e)), all_app_l(wx, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e), all_self(wx)))

law pick_head:
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  {Spec.allIn(Spec.walk(x, False{}, idx, List.append(&2, Nat, pre, [d, a]), 0n, k, k), Spec.walk(Spec.Pick{a, x} <> r, False{}, idx, pre, d, i, k)) == True{} : Bool}

def pick_head(a, x, r, idx, pre, d, i, k):
  +wx = Spec.walk(x, False{}, idx, List.append(&2, Nat, pre, [d, a]), 0n, k, k)
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(x)))
  all_cons(wx, Spec.at(idx, pre, 1n+d, i, k, e), List.append(&2, Spec.Bsr, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e)), all_app_l(wx, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e), all_self(wx)))

law loop_head:
  for +x: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  {Spec.allIn(Spec.walk(x, True{}, idx, List.append(&2, Nat, pre, [d]), 0n, k, k), Spec.walk(Spec.Loop{x} <> r, False{}, idx, pre, d, i, k)) == True{} : Bool}

def loop_head(x, r, idx, pre, d, i, k):
  +wx = Spec.walk(x, True{}, idx, List.append(&2, Nat, pre, [d]), 0n, k, k)
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(x)))
  all_cons(wx, Spec.at(idx, pre, 1n+d, i, k, e), List.append(&2, Spec.Bsr, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e)), all_app_l(wx, wx, Spec.walk(r, False{}, idx, pre, 1n+d, i, e), all_self(wx)))

law round_head:
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +k: Nat
  {Spec.allIn(Spec.walk(x, False{}, idx, List.append(&2, Nat, pre, [a]), 0n, i, k), Spec.walk(Spec.Pick{a, x} <> r, True{}, idx, pre, 0n, i, k)) == True{} : Bool}

def round_head(a, x, r, idx, pre, i, k):
  +wx = Spec.walk(x, False{}, idx, List.append(&2, Nat, pre, [a]), 0n, i, k)
  all_app_l(wx, wx, Spec.walk(r, True{}, idx, pre, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(x)))), all_self(wx))

law seq_frame_fr:
  for fr: Frame
  for +c: Coord
  for +x: +List<Spec.Tree>
  for +cr: {cR(c) == False{} : Bool}
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +eIdx: {cIdx(c) == idx : Nat}
  for +ePre: {cPre(c) == pre : +List<Nat>}
  for +eD: {cD(c) == d : Nat}
  for +eI: {cI(c) == i : Nat}
  for +eK: {cK(c) == k : Nat}
  {Spec.allIn(walkAt(holeCoord(fr, c), x), walkAt(c, fill(fr, x))) == True{} : Bool}

def seq_frame_fr(fr, c, x, cr, idx, pre, d, i, k, eIdx, ePre, eD, eI, eK):
  match fr:
    case NodeKid{+l, +q, +r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      +wf = Spec.walk(List.append(&2, Spec.Tree, l, Spec.Node{q, x} <> r), False{}, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +t1 = seq_tail(l, Spec.Node{q, x} <> r, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +t2 = node_head(q, x, r, cIdx(c), cPre(c), Nat.add(cD(c), List.length(&2, Spec.Tree, l)), cI(c), kk)
      +tr = all_trans(Spec.walk(x, False{}, q, [], 0n, kk, kk), Spec.walk(Spec.Node{q, x} <> r, False{}, cIdx(c), cPre(c), Nat.add(cD(c), List.length(&2, Spec.Tree, l)), cI(c), kk), wf, t2, t1)
      Equal.trans(Bool, Spec.allIn(Spec.walk(x, False{}, q, [], 0n, kk, kk), walkAt(c, List.append(&2, Spec.Tree, l, Spec.Node{q, x} <> r))), Spec.allIn(Spec.walk(x, False{}, q, [], 0n, kk, kk), wf), True{},
        Equal.cong(Bool, Bool, v => Spec.allIn(Spec.walk(x, False{}, q, [], 0n, kk, kk), Spec.walk(List.append(&2, Spec.Tree, l, Spec.Node{q, x} <> r), v, cIdx(c), cPre(c), cD(c), cI(c), cK(c))), cR(c), False{}, cr), tr)
    case PickKid{+l, +a, +r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      +dd = Nat.add(cD(c), List.length(&2, Spec.Tree, l))
      +wf = Spec.walk(List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r), False{}, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +hx = Spec.walk(x, False{}, cIdx(c), List.append(&2, Nat, cPre(c), [dd, a]), 0n, kk, kk)
      +t1 = seq_tail(l, Spec.Pick{a, x} <> r, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +t2 = pick_head(a, x, r, cIdx(c), cPre(c), dd, cI(c), kk)
      +tr = all_trans(hx, Spec.walk(Spec.Pick{a, x} <> r, False{}, cIdx(c), cPre(c), dd, cI(c), kk), wf, t2, t1)
      +lhs = Spec.walk(x, False{}, cIdx(c), pickPre(cR(c), cPre(c), dd, a), 0n, pickI(cR(c), cI(c), kk), kk)
      +rhs = Spec.walk(List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r), cR(c), cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      Equal.trans(Bool, Spec.allIn(lhs, rhs), Spec.allIn(hx, wf), True{},
        Equal.cong(Bool, Bool, v => Spec.allIn(Spec.walk(x, False{}, cIdx(c), pickPre(v, cPre(c), dd, a), 0n, pickI(v, cI(c), kk), kk), Spec.walk(List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r), v, cIdx(c), cPre(c), cD(c), cI(c), cK(c))), cR(c), False{}, cr), tr)
    case LoopKid{+l, +r}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      +dd = Nat.add(cD(c), List.length(&2, Spec.Tree, l))
      +wf = Spec.walk(List.append(&2, Spec.Tree, l, Spec.Loop{x} <> r), False{}, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +hx = Spec.walk(x, True{}, cIdx(c), List.append(&2, Nat, cPre(c), [dd]), 0n, kk, kk)
      +t1 = seq_tail(l, Spec.Loop{x} <> r, cIdx(c), cPre(c), cD(c), cI(c), cK(c))
      +t2 = loop_head(x, r, cIdx(c), cPre(c), dd, cI(c), kk)
      +tr = all_trans(hx, Spec.walk(Spec.Loop{x} <> r, False{}, cIdx(c), cPre(c), dd, cI(c), kk), wf, t2, t1)
      Equal.trans(Bool, Spec.allIn(hx, walkAt(c, List.append(&2, Spec.Tree, l, Spec.Loop{x} <> r))), Spec.allIn(hx, wf), True{},
        Equal.cong(Bool, Bool, v => Spec.allIn(hx, Spec.walk(List.append(&2, Spec.Tree, l, Spec.Loop{x} <> r), v, cIdx(c), cPre(c), cD(c), cI(c), cK(c))), cR(c), False{}, cr), tr)

# A frame in a sequence: its hole's walk is part of its forest's walk.
law seq_frame:
  for +fr: Frame
  for +c: Coord
  for +x: +List<Spec.Tree>
  for +cr: {cR(c) == False{} : Bool}
  {Spec.allIn(walkAt(holeCoord(fr, c), x), walkAt(c, fill(fr, x))) == True{} : Bool}

def seq_frame(fr, c, x, cr):
  +idx = cIdx(c)
  +pre = cPre(c)
  +d = cD(c)
  +i = cI(c)
  +k = cK(c)
  seq_frame_fr(fr, c, x, cr, idx, pre, d, i, k, {==}, {==}, {==}, {==}, {==})

law node_times:
  for n: Nat
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Node{q, x}], grammar, [itemAtOr(Spec.times(n, Spec.Brack{Spec.Group{}, alts}), j)]) == True{} : Bool}
  Empty

def node_times(n, j, alts, q, x, grammar, e):
  match n j:
    case 0n _:
      Lemma.false_is_not_true(e)
    case 1n+m 0n:
      Lemma.false_is_not_true(e)
    case 1n+m 1n+jj:
      node_times(m, jj, alts, q, x, grammar, e)

# A node or a loop never stands where a round must be.
law node_round:
  for it: Spec.Item
  for n: Nat
  for j: Nat
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Node{q, x}], grammar, [itemAtOr(loopItems(it, n), j)]) == True{} : Bool}
  Empty

def node_round(it, n, j, q, x, grammar, e):
  match it:
    case Spec.Brack{kind, +alts}:
      node_times(n, j, alts, q, x, grammar, e)
    case Spec.Sym{sy}:
      Lemma.false_is_not_true(e)
    case Spec.Eps{}:
      Lemma.false_is_not_true(e)

law loop_times:
  for n: Nat
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Loop{x}], grammar, [itemAtOr(Spec.times(n, Spec.Brack{Spec.Group{}, alts}), j)]) == True{} : Bool}
  Empty

def loop_times(n, j, alts, x, grammar, e):
  match n j:
    case 0n _:
      Lemma.false_is_not_true(e)
    case 1n+m 0n:
      Lemma.false_is_not_true(e)
    case 1n+m 1n+jj:
      loop_times(m, jj, alts, x, grammar, e)

law loop_round:
  for it: Spec.Item
  for n: Nat
  for j: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Loop{x}], grammar, [itemAtOr(loopItems(it, n), j)]) == True{} : Bool}
  Empty

def loop_round(it, n, j, x, grammar, e):
  match it:
    case Spec.Brack{kind, +alts}:
      loop_times(n, j, alts, x, grammar, e)
    case Spec.Sym{sy}:
      Lemma.false_is_not_true(e)
    case Spec.Eps{}:
      Lemma.false_is_not_true(e)

# A pick among a loop's rounds: the rounds before it, then its round's head.
law rounds_pick:
  for +l: +List<Spec.Tree>
  for +a: Nat
  for +r: +List<Spec.Tree>
  for +c: Coord
  for +x: +List<Spec.Tree>
  for +it: Spec.Item
  for +n: Nat
  for +grammar: +List<Spec.Production>
  for +cr: {cR(c) == True{} : Bool}
  for +cd: {cD(c) == 0n : Nat}
  for +e: {Spec.fits(List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r), grammar, loopItems(it, n)) == True{} : Bool}
  {Spec.allIn(walkAt(holeCoord(PickKid{l, a, r}, c), x), walkAt(c, fill(PickKid{l, a, r}, x))) == True{} : Bool}

def rounds_pick(l, a, r, c, x, it, n, grammar, cr, cd, e):
  match it:
    case Spec.Brack{kind, +alts}:
      +kk = Nat.add(cK(c), List.length(&2, Nat, Spec.leaves(l)))
      +dd = Nat.add(cD(c), List.length(&2, Spec.Tree, l))
      +f = List.append(&2, Spec.Tree, l, Spec.Pick{a, x} <> r)
      +hx = Spec.walk(x, False{}, cIdx(c), List.append(&2, Nat, cPre(c), [a]), 0n, cI(c), kk)
      +mid = Spec.walk(Spec.Pick{a, x} <> r, True{}, cIdx(c), cPre(c), 0n, cI(c), kk)
      +wf = Spec.walk(f, True{}, cIdx(c), cPre(c), 0n, cI(c), cK(c))
      +t1 = rounds_tail(l, Spec.Pick{a, x} <> r, cIdx(c), cPre(c), cI(c), cK(c), n, alts, grammar, e)
      +t2 = round_head(a, x, r, cIdx(c), cPre(c), cI(c), kk)
      +tr = all_trans(hx, mid, wf, t2, t1)
      +s1 = Equal.cong(Nat, Bool, w => Spec.allIn(Spec.walk(x, False{}, cIdx(c), pickPre(cR(c), cPre(c), dd, a), 0n, pickI(cR(c), cI(c), kk), kk), Spec.walk(f, cR(c), cIdx(c), cPre(c), w, cI(c), cK(c))), cD(c), 0n, cd)
      +s2 = Equal.cong(Bool, Bool, v => Spec.allIn(Spec.walk(x, False{}, cIdx(c), pickPre(v, cPre(c), dd, a), 0n, pickI(v, cI(c), kk), kk), Spec.walk(f, v, cIdx(c), cPre(c), 0n, cI(c), cK(c))), cR(c), True{}, cr)
      +lhs = Spec.walk(x, False{}, cIdx(c), pickPre(cR(c), cPre(c), dd, a), 0n, pickI(cR(c), cI(c), kk), kk)
      Equal.trans(Bool, Spec.allIn(lhs, Spec.walk(f, cR(c), cIdx(c), cPre(c), cD(c), cI(c), cK(c))), Spec.allIn(lhs, Spec.walk(f, cR(c), cIdx(c), cPre(c), 0n, cI(c), cK(c))), True{}, s1,
        Equal.trans(Bool, Spec.allIn(lhs, Spec.walk(f, cR(c), cIdx(c), cPre(c), 0n, cI(c), cK(c))), Spec.allIn(hx, wf), True{}, s2, tr))
    case Spec.Sym{sy}:
      Empty.absurd({Spec.allIn(walkAt(holeCoord(PickKid{l, a, r}, c), x), walkAt(c, fill(PickKid{l, a, r}, x))) == True{} : Bool}, Lemma.false_is_not_true(app_item(l, Spec.Pick{a, x}, r, [], grammar, e)))
    case Spec.Eps{}:
      Empty.absurd({Spec.allIn(walkAt(holeCoord(PickKid{l, a, r}, c), x), walkAt(c, fill(PickKid{l, a, r}, x))) == True{} : Bool}, Lemma.false_is_not_true(app_item(l, Spec.Pick{a, x}, r, [], grammar, e)))

# A frame among a loop's rounds: only a pick can stand there.
law rounds_frame:
  for fr: Frame
  for +c: Coord
  for +x: +List<Spec.Tree>
  for +it: Spec.Item
  for +n: Nat
  for +grammar: +List<Spec.Production>
  for +cr: {cR(c) == True{} : Bool}
  for +cd: {cD(c) == 0n : Nat}
  for +e: {Spec.fits(fill(fr, x), grammar, loopItems(it, n)) == True{} : Bool}
  {Spec.allIn(walkAt(holeCoord(fr, c), x), walkAt(c, fill(fr, x))) == True{} : Bool}

def rounds_frame(fr, c, x, it, n, grammar, cr, cd, e):
  match fr:
    case NodeKid{+l, +q, +r}:
      Empty.absurd({Spec.allIn(walkAt(holeCoord(NodeKid{l, q, r}, c), x), walkAt(c, fill(NodeKid{l, q, r}, x))) == True{} : Bool}, node_round(it, n, List.length(&2, Spec.Tree, l), q, x, grammar, app_item(l, Spec.Node{q, x}, r, loopItems(it, n), grammar, e)))
    case PickKid{+l, +a, +r}:
      rounds_pick(l, a, r, c, x, it, n, grammar, cr, cd, e)
    case LoopKid{+l, +r}:
      Empty.absurd({Spec.allIn(walkAt(holeCoord(LoopKid{l, r}, c), x), walkAt(c, fill(LoopKid{l, r}, x))) == True{} : Bool}, loop_round(it, n, List.length(&2, Spec.Tree, l), x, grammar, app_item(l, Spec.Loop{x}, r, loopItems(it, n), grammar, e)))

law level_steps_in:
  for +f2: Frame
  for +rest2: +List<Frame>
  for +fr: Frame
  for +q0: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +okR: {zipOk(grammar, q0, f2 <> rest2, fill(fr, x)) == True{} : Bool}
  {Spec.allIn(walkAt(holeCoord(fr, holeCoord(f2, coordOf(q0, rest2))), x), walkAt(holeCoord(f2, coordOf(q0, rest2)), fill(fr, x))) == True{} : Bool}

def level_steps_in(f2, rest2, fr, q0, x, grammar, okR):
  match f2:
    case NodeKid{+l2, +q2, +r2}:
      seq_frame(fr, holeCoord(NodeKid{l2, q2, r2}, coordOf(q0, rest2)), x, {==})
    case PickKid{+l2, +a2, +r2}:
      seq_frame(fr, holeCoord(PickKid{l2, a2, r2}, coordOf(q0, rest2)), x, {==})
    case LoopKid{+l2, +r2}:
      +y = fill(fr, x)
      +it = itemAtOr(holeOf(grammar, q0, rest2, fill(LoopKid{l2, r2}, y)), List.length(&2, Spec.Tree, l2))
      rounds_frame(fr, holeCoord(LoopKid{l2, r2}, coordOf(q0, rest2)), x, it, List.length(&2, Spec.Tree, y), grammar, {==}, {==}, zip_head(LoopKid{l2, r2} <> rest2, grammar, q0, y, okR))

# One level of the zipper: the hole's walk is part of the walk of the forest around it.
law level_steps:
  for +fr: Frame
  for rest: +List<Frame>
  for +q0: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +okR: {zipOk(grammar, q0, rest, fill(fr, x)) == True{} : Bool}
  {Spec.allIn(walkAt(holeCoord(fr, coordOf(q0, rest)), x), walkAt(coordOf(q0, rest), fill(fr, x))) == True{} : Bool}

def level_steps(fr, rest, q0, x, grammar, okR):
  match rest:
    case Nil{}:
      seq_frame(fr, Coord{False{}, q0, [], 0n, 0n, 0n}, x, {==})
    case Con{+f2, +rest2}:
      level_steps_in(f2, rest2, fr, q0, x, grammar, okR)

# PLUGGING, STEPS: the walk of a forest set in a zipper is part of the whole tree's walk.
law zip_steps:
  for z: +List<Frame>
  for +q0: Nat
  for +x: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +ok: {zipOk(grammar, q0, z, x) == True{} : Bool}
  {Spec.allIn(walkAt(coordOf(q0, z), x), Spec.walk(zip(z, x), False{}, q0, [], 0n, 0n, 0n)) == True{} : Bool}

def zip_steps(z, q0, x, grammar, ok):
  match z:
    case Nil{}:
      all_self(Spec.walk(x, False{}, q0, [], 0n, 0n, 0n))
    case Con{+fr, +rest}:
      +y = fill(fr, x)
      +okR = Lemma.and_true_right_side(Spec.fits(x, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, y), x)), zipOk(grammar, q0, rest, y), ok)
      all_trans(walkAt(holeCoord(fr, coordOf(q0, rest)), x), walkAt(coordOf(q0, rest), y), Spec.walk(zip(rest, y), False{}, q0, [], 0n, 0n, 0n), level_steps(fr, rest, q0, x, grammar, okR), zip_steps(rest, q0, y, grammar, okR))

# ======== PLUGGING, ADMISSIBLE ========
# Where a forest stands in the tree: in a sequence, among a loop's rounds, or under an
# item that doesn't match (then nothing is asked of it).
type Ctx is Data:
  SeqCtx{own: +List<Spec.Guard>, its: +List<Spec.Item>, idx: Nat, pre: +List<Nat>, above: +List<Nat>, span: +List<Nat>, after: +List<Nat>}
  RoundCtx{alts: +List<+List<Spec.Item>>, idx: Nat, pre: +List<Nat>, above: +List<Nat>, span: +List<Nat>, after: +List<Nat>}
  NoCtx{}

# The items left after the trees l, and the dot after them.
def itemsAfter(l: +List<Spec.Tree>, its: +List<Spec.Item>) -> +List<Spec.Item>:
  match l:
    case Nil{}:
      its
    case Con{u, l2}:
      match its:
        case Nil{}:
          []
        case Con{it, rest}:
          itemsAfter(l2, rest)

def dotAfter(l: +List<Spec.Tree>, d: Nat) -> Nat:
  match l:
    case Nil{}:
      d
    case Con{u, l2}:
      dotAfter(l2, 1n+d)

def nodeCtx(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +q: Nat, ys: +List<Spec.Item>, +above: +List<Nat>, +span: +List<Nat>, +next: +List<Nat>, +x: +List<Spec.Tree>) -> Ctx:
  match ys:
    case Con{Spec.Sym{Spec.Nonterminal{+xn}}, rest}:
      SeqCtx{Spec.prodGuards(guards, q), Spec.rhsOf(grammar, q), q, [], xn <> Spec.sameAbove(above, span, Spec.leaves(x)), Spec.leaves(x), next}
    case _:
      NoCtx{}

def pickCtx(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +a: Nat, ys: +List<Spec.Item>, +idx: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +next: +List<Nat>, +x: +List<Spec.Tree>) -> Ctx:
  match ys:
    case Con{Spec.Brack{kind, +alts}, rest}:
      SeqCtx{Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), Spec.sameAbove(above, span, Spec.leaves(x)), Spec.leaves(x), next}
    case _:
      NoCtx{}

def loopCtx(ys: +List<Spec.Item>, +idx: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +next: +List<Nat>) -> Ctx:
  match ys:
    case Con{Spec.Brack{kind, +alts}, rest}:
      RoundCtx{alts, idx, path, above, span, next}
    case _:
      NoCtx{}

def seqHole(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, fr: Frame, +its: +List<Spec.Item>, +idx: Nat, +pre: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>, +x: +List<Spec.Tree>) -> Ctx:
  match fr:
    case NodeKid{+l, +q, +r}:
      nodeCtx(grammar, guards, q, itemsAfter(l, its), above, span, List.append(&2, Nat, Spec.leaves(r), after), x)
    case PickKid{+l, +a, +r}:
      pickCtx(grammar, guards, a, itemsAfter(l, its), idx, List.append(&2, Nat, pre, [dotAfter(l, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x)
    case LoopKid{+l, +r}:
      loopCtx(itemsAfter(l, its), idx, List.append(&2, Nat, pre, [dotAfter(l, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(r), after))

def roundHole(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, fr: Frame, +alts: +List<+List<Spec.Item>>, +idx: Nat, +path: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>, +x: +List<Spec.Tree>) -> Ctx:
  match fr:
    case PickKid{l, +a, +r}:
      SeqCtx{Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), Spec.sameAbove(above, span, Spec.leaves(x)), Spec.leaves(x), List.append(&2, Nat, Spec.leaves(r), after)}
    case NodeKid{l, q, r}:
      NoCtx{}
    case LoopKid{l, r}:
      NoCtx{}

# Where the hole of a frame stands, given where the frame's forest stands.
def holeCtx(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, fr: Frame, c: Ctx, +x: +List<Spec.Tree>) -> Ctx:
  match c:
    case SeqCtx{own, +its, +idx, +pre, +above, +span, +after}:
      seqHole(grammar, guards, fr, its, idx, pre, above, span, after, x)
    case RoundCtx{+alts, +idx, +pre, +above, +span, +after}:
      roundHole(grammar, guards, fr, alts, idx, pre, above, span, after, x)
    case NoCtx{}:
      NoCtx{}

# The root's children, and the hole of a zipper.
def rootCtx(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +start: Nat, +q0: Nat, +x: +List<Spec.Tree>) -> Ctx:
  SeqCtx{Spec.prodGuards(guards, q0), Spec.rhsOf(grammar, q0), q0, [], start <> Spec.sameAbove([], [], Spec.leaves(x)), Spec.leaves(x), []}

def ctxOf(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +start: Nat, +q0: Nat, z: +List<Frame>, +x: +List<Spec.Tree>) -> Ctx:
  match z:
    case Nil{}:
      rootCtx(grammar, guards, start, q0, x)
    case Con{+fr, +rest}:
      holeCtx(grammar, guards, fr, ctxOf(grammar, guards, start, q0, rest, fill(fr, x)), x)

# What phase 1 asks of a forest where it stands.
def HoldAt(+grammar: +List<Spec.Production>, c: Ctx, +y: +List<Spec.Tree>) -> Type:
  match c:
    case SeqCtx{+own, +its, idx, pre, above, span, +after}:
      Spec.AllHold(grammar, own, its, y, List.append(&2, Nat, Spec.leaves(y), after))
    case RoundCtx{alts, idx, pre, above, span, after}:
      Unit
    case NoCtx{}:
      Unit

def AdmAt(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, c: Ctx, +y: +List<Spec.Tree>) -> Type:
  match c:
    case SeqCtx{own, +its, +idx, +pre, above, span, +after}:
      Spec.Admissible(grammar, guards, y, its, idx, pre, 0n, after)
    case RoundCtx{+alts, +idx, +pre, above, span, +after}:
      Spec.RoundsAdmissible(grammar, guards, y, alts, idx, pre, after)
    case NoCtx{}:
      Unit

def HA(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +c: Ctx, +y: +List<Spec.Tree>) -> Type:
  HoldAt(grammar, c, y) & AdmAt(grammar, guards, c, y)

# Rewriting the tokens after.
law hold_rw:
  for +grammar: +List<Spec.Production>
  for +gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.AllHold(grammar, gs, items, ch, old)
  Spec.AllHold(grammar, gs, items, ch, nw)

def hold_rw(grammar, gs, items, ch, old, nw, e, h):
  %e : Spec.AllHold(grammar, gs, items, ch, _)
  h

law adm_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +ch: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.Admissible(grammar, guards, ch, items, idx, pre, dot, old)
  Spec.Admissible(grammar, guards, ch, items, idx, pre, dot, nw)

def adm_rw(grammar, guards, ch, items, idx, pre, dot, old, nw, e, h):
  %e : Spec.Admissible(grammar, guards, ch, items, idx, pre, dot, _)
  h

law radm_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +rs: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +idx: Nat
  for +path: +List<Nat>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.RoundsAdmissible(grammar, guards, rs, alts, idx, path, old)
  Spec.RoundsAdmissible(grammar, guards, rs, alts, idx, path, nw)

def radm_rw(grammar, guards, rs, alts, idx, path, old, nw, e, h):
  %e : Spec.RoundsAdmissible(grammar, guards, rs, alts, idx, path, _)
  h

# The tokens after a tree in l stay the same when a later tree is swapped.
law next_swap:
  for +l2: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +after: +List<Nat>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after) == List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after) : +List<Nat>}

def next_swap(l2, t, t2, r, after, lv):
  Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)),
    Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), leaves_swap(l2, t, t2, r, lv)))

law ahead_swap:
  for +ch: +List<Spec.Tree>
  for +nO: +List<Nat>
  for +nN: +List<Nat>
  for +en: {nO == nN : +List<Nat>}
  {List.append(&2, Nat, Spec.leaves(ch), nO) == List.append(&2, Nat, Spec.leaves(ch), nN) : +List<Nat>}

def ahead_swap(ch, nO, nN, en):
  Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, Spec.leaves(ch), v), nO, nN, en)
# The head swap, lifted past the trees before it.
law adm_lift:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +its: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +after: +List<Nat>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  for head: Spec.Admissible(grammar, guards, t <> r, itemsAfter(l, its), idx, pre, dotAfter(l, d), after) -> Spec.Admissible(grammar, guards, t2 <> r, itemsAfter(l, its), idx, pre, dotAfter(l, d), after)
  for adm: Spec.Admissible(grammar, guards, List.append(&2, Spec.Tree, l, t <> r), its, idx, pre, d, after)
  Spec.Admissible(grammar, guards, List.append(&2, Spec.Tree, l, t2 <> r), its, idx, pre, d, after)

def adm_lift(l, t, t2, r, its, grammar, guards, idx, pre, d, after, lv, head, adm):
  match l:
    case Nil{}:
      head(adm)
    case Con{+u, +l2}:
      match u:
        case Spec.Leaf{k0}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Nonterminal{xn}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Optional{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Closure{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Positive{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Eps{}:
                  adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
        case Spec.Node{+q, +ch}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Nonterminal{xn}:
                      match adm:
                        case (hA, (hB, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (hold_rw(grammar, Spec.prodGuards(guards, q), Spec.rhsOf(grammar, q), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                            (adm_rw(grammar, guards, ch, Spec.rhsOf(grammar, q), q, [], 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC)))
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Optional{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Closure{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Positive{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Eps{}:
                  adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
        case Spec.Pick{+a, +ch}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Nonterminal{xn}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      match adm:
                        case (hA, (hB, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          (hold_rw(grammar, Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                            (adm_rw(grammar, guards, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC)))
                    case Spec.Optional{}:
                      match adm:
                        case (hA, (hB, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          (hold_rw(grammar, Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                            (adm_rw(grammar, guards, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC)))
                    case Spec.Closure{}:
                      match adm:
                        case (hA, (hB, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          (hold_rw(grammar, Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                            (adm_rw(grammar, guards, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC)))
                    case Spec.Positive{}:
                      match adm:
                        case (hA, (hB, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          (hold_rw(grammar, Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                            (adm_rw(grammar, guards, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC)))
                case Spec.Eps{}:
                  adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
        case Spec.Skip{}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Nonterminal{xn}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Optional{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Closure{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Positive{}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Eps{}:
                  adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
        case Spec.Loop{+rs}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                    case Spec.Nonterminal{xn}:
                      adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      match adm:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (radm_rw(grammar, guards, rs, alts, idx, List.append(&2, Nat, pre, [d]), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC))
                    case Spec.Optional{}:
                      match adm:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (radm_rw(grammar, guards, rs, alts, idx, List.append(&2, Nat, pre, [d]), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC))
                    case Spec.Closure{}:
                      match adm:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (radm_rw(grammar, guards, rs, alts, idx, List.append(&2, Nat, pre, [d]), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC))
                    case Spec.Positive{}:
                      match adm:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (radm_rw(grammar, guards, rs, alts, idx, List.append(&2, Nat, pre, [d]), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, hC))
                case Spec.Eps{}:
                  adm_lift(l2, t, t2, r, rest, grammar, guards, idx, pre, 1n+d, after, lv, head, adm)
# ... and past the rounds before it.
law radm_lift:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +path: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  for head: Spec.RoundsAdmissible(grammar, guards, t <> r, alts, idx, path, after) -> Spec.RoundsAdmissible(grammar, guards, t2 <> r, alts, idx, path, after)
  for adm: Spec.RoundsAdmissible(grammar, guards, List.append(&2, Spec.Tree, l, t <> r), alts, idx, path, after)
  Spec.RoundsAdmissible(grammar, guards, List.append(&2, Spec.Tree, l, t2 <> r), alts, idx, path, after)

def radm_lift(l, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, adm):
  match l:
    case Nil{}:
      head(adm)
    case Con{+u, +l2}:
      match u:
        case Spec.Leaf{k0}:
          radm_lift(l2, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, adm)
        case Spec.Node{+q, +ch}:
          radm_lift(l2, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, adm)
        case Spec.Pick{+a, +ch}:
          match adm:
            case (hA, (hB, hC)):
              +en = next_swap(l2, t, t2, r, after, lv)
              (hold_rw(grammar, Spec.altGuards(guards, idx, path, a), Spec.altOf(alts, a), ch, List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after)), List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after)), ahead_swap(ch, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en), hA),
                (adm_rw(grammar, guards, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hB), radm_lift(l2, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, hC)))
        case Spec.Skip{}:
          radm_lift(l2, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, adm)
        case Spec.Loop{+rs}:
          radm_lift(l2, t, t2, r, alts, grammar, guards, idx, path, after, lv, head, adm)
# Rebuilding a head from the new children's facts.
law node_build:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +xn: Nat
  for +rest: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for p: HA(grammar, guards, nodeCtx(grammar, guards, q, Spec.Sym{Spec.Nonterminal{xn}} <> rest, above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for c: Spec.Admissible(grammar, guards, r, rest, idx, pre, 1n+dot, after)
  Spec.Admissible(grammar, guards, Spec.Node{q, x2} <> r, Spec.Sym{Spec.Nonterminal{xn}} <> rest, idx, pre, dot, after)

def node_build(grammar, guards, q, x, x2, r, xn, rest, idx, pre, dot, above, span, after, p, c):
  match p:
    case (a2, b2):
      (a2, (b2, c))

law adm_head_node:
  for ys: +List<Spec.Item>
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for k: HA(grammar, guards, nodeCtx(grammar, guards, q, ys, above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x) -> HA(grammar, guards, nodeCtx(grammar, guards, q, ys, above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for h: Spec.Admissible(grammar, guards, Spec.Node{q, x} <> r, ys, idx, pre, dot, after)
  Spec.Admissible(grammar, guards, Spec.Node{q, x2} <> r, ys, idx, pre, dot, after)

def adm_head_node(ys, q, x, x2, r, grammar, guards, idx, pre, dot, above, span, after, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{+xn}:
              match h:
                case (hA, (hB, hC)):
                  node_build(grammar, guards, q, x, x2, r, xn, rest, idx, pre, dot, above, span, after, k((hA, hB)), hC)
        case Spec.Brack{kind, alts}:
          match kind:
            case Spec.Group{}:
              h
            case Spec.Optional{}:
              h
            case Spec.Closure{}:
              h
            case Spec.Positive{}:
              h
        case Spec.Eps{}:
          h
law pick_build:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for p: HA(grammar, guards, pickCtx(grammar, guards, a, Spec.Brack{kind, alts} <> rest, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for c: Spec.Admissible(grammar, guards, r, rest, idx, pre, 1n+dot, after)
  Spec.Admissible(grammar, guards, Spec.Pick{a, x2} <> r, Spec.Brack{kind, alts} <> rest, idx, pre, dot, after)

def pick_build(grammar, guards, a, x, x2, r, kind, alts, rest, idx, pre, dot, above, span, after, p, c):
  match kind:
    case Spec.Group{}:
      match p:
        case (a2, b2):
          (a2, (b2, c))
    case Spec.Optional{}:
      match p:
        case (a2, b2):
          (a2, (b2, c))
    case Spec.Closure{}:
      match p:
        case (a2, b2):
          (a2, (b2, c))
    case Spec.Positive{}:
      match p:
        case (a2, b2):
          (a2, (b2, c))

law adm_head_pick:
  for ys: +List<Spec.Item>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for k: HA(grammar, guards, pickCtx(grammar, guards, a, ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x) -> HA(grammar, guards, pickCtx(grammar, guards, a, ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for h: Spec.Admissible(grammar, guards, Spec.Pick{a, x} <> r, ys, idx, pre, dot, after)
  Spec.Admissible(grammar, guards, Spec.Pick{a, x2} <> r, ys, idx, pre, dot, after)

def adm_head_pick(ys, a, x, x2, r, grammar, guards, idx, pre, dot, above, span, after, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{xn}:
              h
        case Spec.Brack{+kind, +alts}:
          match kind:
            case Spec.Group{}:
              match h:
                case (hA, (hB, hC)):
                  pick_build(grammar, guards, a, x, x2, r, Spec.Group{}, alts, rest, idx, pre, dot, above, span, after, k((hA, hB)), hC)
            case Spec.Optional{}:
              match h:
                case (hA, (hB, hC)):
                  pick_build(grammar, guards, a, x, x2, r, Spec.Optional{}, alts, rest, idx, pre, dot, above, span, after, k((hA, hB)), hC)
            case Spec.Closure{}:
              match h:
                case (hA, (hB, hC)):
                  pick_build(grammar, guards, a, x, x2, r, Spec.Closure{}, alts, rest, idx, pre, dot, above, span, after, k((hA, hB)), hC)
            case Spec.Positive{}:
              match h:
                case (hA, (hB, hC)):
                  pick_build(grammar, guards, a, x, x2, r, Spec.Positive{}, alts, rest, idx, pre, dot, above, span, after, k((hA, hB)), hC)
        case Spec.Eps{}:
          h
law loop_build:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for p: HA(grammar, guards, loopCtx(Spec.Brack{kind, alts} <> rest, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after)), x2)
  for c: Spec.Admissible(grammar, guards, r, rest, idx, pre, 1n+dot, after)
  Spec.Admissible(grammar, guards, Spec.Loop{x2} <> r, Spec.Brack{kind, alts} <> rest, idx, pre, dot, after)

def loop_build(grammar, guards, x2, r, kind, alts, rest, idx, pre, dot, above, span, after, p, c):
  match kind:
    case Spec.Group{}:
      match p:
        case (u0, b2):
          (b2, c)
    case Spec.Optional{}:
      match p:
        case (u0, b2):
          (b2, c)
    case Spec.Closure{}:
      match p:
        case (u0, b2):
          (b2, c)
    case Spec.Positive{}:
      match p:
        case (u0, b2):
          (b2, c)

law adm_head_loop:
  for ys: +List<Spec.Item>
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for k: HA(grammar, guards, loopCtx(ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after)), x) -> HA(grammar, guards, loopCtx(ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after)), x2)
  for h: Spec.Admissible(grammar, guards, Spec.Loop{x} <> r, ys, idx, pre, dot, after)
  Spec.Admissible(grammar, guards, Spec.Loop{x2} <> r, ys, idx, pre, dot, after)

def adm_head_loop(ys, x, x2, r, grammar, guards, idx, pre, dot, above, span, after, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{xn}:
              h
        case Spec.Brack{+kind, +alts}:
          match kind:
            case Spec.Group{}:
              match h:
                case (hR, hC):
                  loop_build(grammar, guards, x2, r, Spec.Group{}, alts, rest, idx, pre, dot, above, span, after, k((Unit{}, hR)), hC)
            case Spec.Optional{}:
              match h:
                case (hR, hC):
                  loop_build(grammar, guards, x2, r, Spec.Optional{}, alts, rest, idx, pre, dot, above, span, after, k((Unit{}, hR)), hC)
            case Spec.Closure{}:
              match h:
                case (hR, hC):
                  loop_build(grammar, guards, x2, r, Spec.Closure{}, alts, rest, idx, pre, dot, above, span, after, k((Unit{}, hR)), hC)
            case Spec.Positive{}:
              match h:
                case (hR, hC):
                  loop_build(grammar, guards, x2, r, Spec.Positive{}, alts, rest, idx, pre, dot, above, span, after, k((Unit{}, hR)), hC)
        case Spec.Eps{}:
          h
law rpick_build:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +idx: Nat
  for +path: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for p: HA(grammar, guards, roundHole(grammar, guards, PickKid{[], a, r}, alts, idx, path, above, span, after, x), x2)
  for c: Spec.RoundsAdmissible(grammar, guards, r, alts, idx, path, after)
  Spec.RoundsAdmissible(grammar, guards, Spec.Pick{a, x2} <> r, alts, idx, path, after)

def rpick_build(grammar, guards, a, x, x2, r, alts, idx, path, above, span, after, p, c):
  match p:
    case (a2, b2):
      (a2, (b2, c))

law radm_head_pick:
  for +l: +List<Spec.Tree>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +idx: Nat
  for +path: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for k: HA(grammar, guards, roundHole(grammar, guards, PickKid{l, a, r}, alts, idx, path, above, span, after, x), x) -> HA(grammar, guards, roundHole(grammar, guards, PickKid{l, a, r}, alts, idx, path, above, span, after, x), x2)
  for h: Spec.RoundsAdmissible(grammar, guards, Spec.Pick{a, x} <> r, alts, idx, path, after)
  Spec.RoundsAdmissible(grammar, guards, Spec.Pick{a, x2} <> r, alts, idx, path, after)

def radm_head_pick(l, a, x, x2, r, alts, grammar, guards, idx, path, above, span, after, k, h):
  match h:
    case (hA, (hB, hC)):
      rpick_build(grammar, guards, a, x, x2, r, alts, idx, path, above, span, after, k((hA, hB)), hC)

# One level: the frame's forest keeps phase 1 when its hole's forest is swapped.
law level_adm:
  for c: Ctx
  for fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: HA(grammar, guards, holeCtx(grammar, guards, fr, c, x), x) -> HA(grammar, guards, holeCtx(grammar, guards, fr, c, x), x2)
  for h: AdmAt(grammar, guards, c, fill(fr, x))
  AdmAt(grammar, guards, c, fill(fr, x2))

def level_adm(c, fr, x, x2, grammar, guards, lv, k, h):
  match c:
    case SeqCtx{+own, +its, +idx, +pre, +above, +span, +after}:
      match fr:
        case NodeKid{+l, +q, +r}:
          adm_lift(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, its, grammar, guards, idx, pre, 0n, after, wrap_lv(NodeKid{l, q, r}, x, x2, lv), hh => adm_head_node(itemsAfter(l, its), q, x, x2, r, grammar, guards, idx, pre, dotAfter(l, 0n), above, span, after, k, hh), h)
        case PickKid{+l, +a, +r}:
          adm_lift(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, its, grammar, guards, idx, pre, 0n, after, wrap_lv(PickKid{l, a, r}, x, x2, lv), hh => adm_head_pick(itemsAfter(l, its), a, x, x2, r, grammar, guards, idx, pre, dotAfter(l, 0n), above, span, after, k, hh), h)
        case LoopKid{+l, +r}:
          adm_lift(l, Spec.Loop{x}, Spec.Loop{x2}, r, its, grammar, guards, idx, pre, 0n, after, wrap_lv(LoopKid{l, r}, x, x2, lv), hh => adm_head_loop(itemsAfter(l, its), x, x2, r, grammar, guards, idx, pre, dotAfter(l, 0n), above, span, after, k, hh), h)
    case RoundCtx{+alts, +idx, +pre, +above, +span, +after}:
      match fr:
        case NodeKid{+l, +q, +r}:
          radm_lift(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, alts, grammar, guards, idx, pre, after, wrap_lv(NodeKid{l, q, r}, x, x2, lv), hh => hh, h)
        case PickKid{+l, +a, +r}:
          radm_lift(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, alts, grammar, guards, idx, pre, after, wrap_lv(PickKid{l, a, r}, x, x2, lv), hh => radm_head_pick(l, a, x, x2, r, alts, grammar, guards, idx, pre, above, span, after, k, hh), h)
        case LoopKid{+l, +r}:
          radm_lift(l, Spec.Loop{x}, Spec.Loop{x2}, r, alts, grammar, guards, idx, pre, after, wrap_lv(LoopKid{l, r}, x, x2, lv), hh => hh, h)
    case NoCtx{}:
      Unit{}

# The first and last spelling of a frame's forest stay when its hole is swapped.
law first_app:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.firstSpell(List.append(&2, Spec.Tree, l, t2 <> r)) == Spec.firstSpell(List.append(&2, Spec.Tree, l, t <> r)) : Maybe<&2, +List<Nat>>}

def first_app(l, t, t2, r, lv):
  match l:
    case Nil{}:
      Equal.cong(+List<Nat>, Maybe<&2, +List<Nat>>, v => Some{v}, Spec.leaves([t2]), Spec.leaves([t]), lv)
    case Con{+u, +l2}:
      {==}

law last_of_swap:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.leaves([Spec.lastOf(ts, t2)]) == Spec.leaves([Spec.lastOf(ts, t)]) : +List<Nat>}

def last_of_swap(ts, t, t2, lv):
  match ts:
    case Nil{}:
      lv
    case Con{+u, +us}:
      {==}

law lastof_app:
  for l2: +List<Spec.Tree>
  for +u: Spec.Tree
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.leaves([Spec.lastOf(List.append(&2, Spec.Tree, l2, t2 <> r), u)]) == Spec.leaves([Spec.lastOf(List.append(&2, Spec.Tree, l2, t <> r), u)]) : +List<Nat>}

def lastof_app(l2, u, t, t2, r, lv):
  match l2:
    case Nil{}:
      last_of_swap(r, t, t2, lv)
    case Con{+v, +l3}:
      lastof_app(l3, v, t, t2, r, lv)

law last_app:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.lastSpell(List.append(&2, Spec.Tree, l, t2 <> r)) == Spec.lastSpell(List.append(&2, Spec.Tree, l, t <> r)) : Maybe<&2, +List<Nat>>}

def last_app(l, t, t2, r, lv):
  match l:
    case Nil{}:
      Equal.cong(+List<Nat>, Maybe<&2, +List<Nat>>, v => Some{v}, Spec.leaves([Spec.lastOf(r, t2)]), Spec.leaves([Spec.lastOf(r, t)]), last_of_swap(r, t, t2, lv))
    case Con{+u, +l2}:
      Equal.cong(+List<Nat>, Maybe<&2, +List<Nat>>, v => Some{v}, Spec.leaves([Spec.lastOf(List.append(&2, Spec.Tree, l2, t2 <> r), u)]), Spec.leaves([Spec.lastOf(List.append(&2, Spec.Tree, l2, t <> r), u)]), lastof_app(l2, u, t, t2, r, lv))

law first_fill:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.firstSpell(fill(fr, x2)) == Spec.firstSpell(fill(fr, x)) : Maybe<&2, +List<Nat>>}

def first_fill(fr, x, x2, lv):
  match fr:
    case NodeKid{+l, +q, +r}:
      first_app(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, wrap_lv(NodeKid{l, q, r}, x, x2, lv))
    case PickKid{+l, +a, +r}:
      first_app(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, wrap_lv(PickKid{l, a, r}, x, x2, lv))
    case LoopKid{+l, +r}:
      first_app(l, Spec.Loop{x}, Spec.Loop{x2}, r, wrap_lv(LoopKid{l, r}, x, x2, lv))

law last_fill:
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  {Spec.lastSpell(fill(fr, x2)) == Spec.lastSpell(fill(fr, x)) : Maybe<&2, +List<Nat>>}

def last_fill(fr, x, x2, lv):
  match fr:
    case NodeKid{+l, +q, +r}:
      last_app(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, wrap_lv(NodeKid{l, q, r}, x, x2, lv))
    case PickKid{+l, +a, +r}:
      last_app(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, wrap_lv(PickKid{l, a, r}, x, x2, lv))
    case LoopKid{+l, +r}:
      last_app(l, Spec.Loop{x}, Spec.Loop{x2}, r, wrap_lv(LoopKid{l, r}, x, x2, lv))

# The frame's own rules read only its first and last child (as Laws.holds_local).
law p_hold_one:
  for g: Spec.Guard
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for +eF: {Spec.firstSpell(f2) == Spec.firstSpell(f) : Maybe<&2, +List<Nat>>}
  for +eL: {Spec.lastSpell(f2) == Spec.lastSpell(f) : Maybe<&2, +List<Nat>>}
  for h: Spec.Holds(grammar, g, items, f, ahead)
  Spec.Holds(grammar, g, items, f2, ahead)

def p_hold_one(g, grammar, items, f, f2, ahead, eF, eL, h):
  match g:
    case Spec.Ahead{ids}:
      h
    case Spec.NotAhead{ids}:
      h
    case Spec.LeftAssoc{+ids}:
      %Equal.sym(Maybe<&2, +List<Nat>>, Spec.lastSpell(f2), Spec.lastSpell(f), eL) : Spec.EdgeFree(grammar, ids, items, _)
      h
    case Spec.RightAssoc{+ids}:
      %Equal.sym(Maybe<&2, +List<Nat>>, Spec.firstSpell(f2), Spec.firstSpell(f), eF) : Spec.EdgeFree(grammar, ids, items, _)
      h

law p_holds:
  for +grammar: +List<Spec.Production>
  for gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for +eF: {Spec.firstSpell(f2) == Spec.firstSpell(f) : Maybe<&2, +List<Nat>>}
  for +eL: {Spec.lastSpell(f2) == Spec.lastSpell(f) : Maybe<&2, +List<Nat>>}
  for h: Spec.AllHold(grammar, gs, items, f, ahead)
  Spec.AllHold(grammar, gs, items, f2, ahead)

def p_holds(grammar, gs, items, f, f2, ahead, eF, eL, h):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, rest}:
      match h:
        case (hg, hr):
          (p_hold_one(g, grammar, items, f, f2, ahead, eF, eL, hg), p_holds(grammar, rest, items, f, f2, ahead, eF, eL, hr))

law hold_level:
  for c: Ctx
  for +fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for h: HoldAt(grammar, c, fill(fr, x))
  HoldAt(grammar, c, fill(fr, x2))

def hold_level(c, fr, x, x2, grammar, lv, h):
  match c:
    case SeqCtx{+own, +its, idx, pre, above, span, +after}:
      +old = List.append(&2, Nat, Spec.leaves(fill(fr, x)), after)
      +nw = List.append(&2, Nat, Spec.leaves(fill(fr, x2)), after)
      +eA = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(fill(fr, x)), Spec.leaves(fill(fr, x2)), Equal.sym(+List<Nat>, Spec.leaves(fill(fr, x2)), Spec.leaves(fill(fr, x)), leaves_fill(fr, x, x2, lv)))
      p_holds(grammar, own, its, fill(fr, x), fill(fr, x2), nw, first_fill(fr, x, x2, lv), last_fill(fr, x, x2, lv), hold_rw(grammar, own, its, fill(fr, x), old, nw, eA, h))
    case RoundCtx{alts, idx, pre, above, span, after}:
      Unit{}
    case NoCtx{}:
      Unit{}

law level_ha:
  for +fr: Frame
  for +c: Ctx
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: HA(grammar, guards, holeCtx(grammar, guards, fr, c, x), x) -> HA(grammar, guards, holeCtx(grammar, guards, fr, c, x), x2)
  for hh: HA(grammar, guards, c, fill(fr, x))
  HA(grammar, guards, c, fill(fr, x2))

def level_ha(fr, c, x, x2, grammar, guards, lv, k, hh):
  match hh:
    case (hH, hA):
      (hold_level(c, fr, x, x2, grammar, lv, hH), level_adm(c, fr, x, x2, grammar, guards, lv, k, hA))

law root_build:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +start: Nat
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for p: HA(grammar, guards, rootCtx(grammar, guards, start, q0, y), y2)
  for c: Spec.Admissible(grammar, guards, [], [], 0n, [], 1n, [])
  Spec.Admissible(grammar, guards, [Spec.Node{q0, y2}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])

def root_build(grammar, guards, start, q0, y, y2, p, c):
  match p:
    case (a2, b2):
      (a2, (b2, c))

# PLUGGING, ADMISSIBLE: the tree keeps phase 1 when the forest in its hole is swapped for
# one over the same tokens that keeps phase 1 where it stands (k turns the old forest's
# facts into the new one's).
law plug_adm:
  for z: +List<Frame>
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +start: Nat
  for +q0: Nat
  for +lv: {Spec.leaves(y2) == Spec.leaves(y) : +List<Nat>}
  for k: HA(grammar, guards, ctxOf(grammar, guards, start, q0, z, y), y) -> HA(grammar, guards, ctxOf(grammar, guards, start, q0, z, y), y2)
  for whole: Spec.Admissible(grammar, guards, [Spec.Node{q0, zip(z, y)}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])
  Spec.Admissible(grammar, guards, [Spec.Node{q0, zip(z, y2)}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])

def plug_adm(z, y, y2, grammar, guards, start, q0, lv, k, whole):
  match z:
    case Nil{}:
      match whole:
        case (hA, (hB, hC)):
          root_build(grammar, guards, start, q0, y, y2, k((hA, hB)), hC)
    case Con{+fr, +rest}:
      plug_adm(rest, fill(fr, y), fill(fr, y2), grammar, guards, start, q0, leaves_fill(fr, y, y2, lv), hh => level_ha(fr, ctxOf(grammar, guards, start, q0, rest, fill(fr, y)), y, y2, grammar, guards, lv, k, hh), whole)

# ======== PLUGGING, UNBEATEN ========
def UnbAt(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, c: Ctx, +y: +List<Spec.Tree>) -> Type:
  match c:
    case SeqCtx{own, +its, +idx, +pre, +above, +span, +after}:
      Spec.Unbeaten(grammar, guards, marks, y, its, idx, pre, 0n, above, span, after)
    case RoundCtx{+alts, +idx, +pre, +above, +span, +after}:
      Spec.RoundsUnbeaten(grammar, guards, marks, y, alts, idx, pre, above, span, after)
    case NoCtx{}:
      Unit

# The rivals and children of a node or pick read its tokens, as in PROOF_LOCAL.
law p_rival_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +x: Nat
  for +q: Nat
  for +w: +List<Nat>
  for +w2: +List<Nat>
  for +next: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +lv: {w2 == w : +List<Nat>}
  for nr: Spec.ProdRival(grammar, guards, marks, x, q, w, next, x <> Spec.sameAbove(above, span, w)) -> Empty
  Spec.ProdRival(grammar, guards, marks, x, q, w2, next, x <> Spec.sameAbove(above, span, w2)) -> Empty

def p_rival_swap_node(grammar, guards, marks, x, q, w, w2, next, above, span, lv, nr):
  %Equal.sym(+List<Nat>, w2, w, lv) : Spec.ProdRival(grammar, guards, marks, x, q, _, next, x <> Spec.sameAbove(above, span, _)) -> Empty
  nr

law p_unb_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +x: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +next: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), next)
  Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, Spec.leaves(ch2)), Spec.leaves(ch2), next)

def p_unb_swap_node(grammar, guards, marks, q, ch, ch2, x, above, span, next, lv, unb2):
  %Equal.sym(+List<Nat>, Spec.leaves(ch2), Spec.leaves(ch), lv) : Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, _), _, next)
  unb2

law p_rival_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +w: +List<Nat>
  for +w2: +List<Nat>
  for +next: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +lv: {w2 == w : +List<Nat>}
  for nr: Spec.AltRival(grammar, guards, marks, alts, index, path, a, w, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, w)) -> Empty
  Spec.AltRival(grammar, guards, marks, alts, index, path, a, w2, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, w2)) -> Empty

def p_rival_swap_pick(grammar, guards, marks, alts, index, path, a, w, w2, next, above, span, lv, nr):
  %Equal.sym(+List<Nat>, w2, w, lv) : Spec.AltRival(grammar, guards, marks, alts, index, path, a, _, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, _)) -> Empty
  nr

law p_unb_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +index: Nat
  for +pre: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +next: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), next)
  Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, Spec.leaves(ch2)), Spec.leaves(ch2), next)

def p_unb_swap_pick(grammar, guards, marks, alts, a, index, pre, ch, ch2, above, span, next, lv, unb2):
  %Equal.sym(+List<Nat>, Spec.leaves(ch2), Spec.leaves(ch), lv) : Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, _), _, next)
  unb2

law prival_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +xn: Nat
  for +q: Nat
  for +wd: +List<Nat>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +xs: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.ProdRival(grammar, guards, marks, xn, q, wd, old, xs) -> Empty
  Spec.ProdRival(grammar, guards, marks, xn, q, wd, nw, xs) -> Empty

def prival_rw(grammar, guards, marks, xn, q, wd, old, nw, xs, e, h):
  %e : Spec.ProdRival(grammar, guards, marks, xn, q, wd, _, xs) -> Empty
  h

law arival_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +idx: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +wd: +List<Nat>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +xs: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.AltRival(grammar, guards, marks, alts, idx, path, a, wd, old, xs) -> Empty
  Spec.AltRival(grammar, guards, marks, alts, idx, path, a, wd, nw, xs) -> Empty

def arival_rw(grammar, guards, marks, alts, idx, path, a, wd, old, nw, xs, e, h):
  %e : Spec.AltRival(grammar, guards, marks, alts, idx, path, a, wd, _, xs) -> Empty
  h

law unb_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +ch: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.Unbeaten(grammar, guards, marks, ch, items, idx, pre, dot, above, span, old)
  Spec.Unbeaten(grammar, guards, marks, ch, items, idx, pre, dot, above, span, nw)

def unb_rw(grammar, guards, marks, ch, items, idx, pre, dot, above, span, old, nw, e, h):
  %e : Spec.Unbeaten(grammar, guards, marks, ch, items, idx, pre, dot, above, span, _)
  h

law runb_rw:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +rs: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +idx: Nat
  for +path: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +old: +List<Nat>
  for +nw: +List<Nat>
  for +e: {old == nw : +List<Nat>}
  for h: Spec.RoundsUnbeaten(grammar, guards, marks, rs, alts, idx, path, above, span, old)
  Spec.RoundsUnbeaten(grammar, guards, marks, rs, alts, idx, path, above, span, nw)

def runb_rw(grammar, guards, marks, rs, alts, idx, path, above, span, old, nw, e, h):
  %e : Spec.RoundsUnbeaten(grammar, guards, marks, rs, alts, idx, path, above, span, _)
  h
law unb_lift:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +its: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +d: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  for head: Spec.Unbeaten(grammar, guards, marks, t <> r, itemsAfter(l, its), idx, pre, dotAfter(l, d), above, span, after) -> Spec.Unbeaten(grammar, guards, marks, t2 <> r, itemsAfter(l, its), idx, pre, dotAfter(l, d), above, span, after)
  for unb: Spec.Unbeaten(grammar, guards, marks, List.append(&2, Spec.Tree, l, t <> r), its, idx, pre, d, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, List.append(&2, Spec.Tree, l, t2 <> r), its, idx, pre, d, above, span, after)

def unb_lift(l, t, t2, r, its, grammar, guards, marks, idx, pre, d, above, span, after, lv, head, unb):
  match l:
    case Nil{}:
      head(unb)
    case Con{+u, +l2}:
      match u:
        case Spec.Leaf{k0}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Nonterminal{+xn}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Optional{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Closure{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Positive{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Eps{}:
                  unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
        case Spec.Node{+q, +ch}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Nonterminal{+xn}:
                      match unb:
                        case (hR, (hU, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +xs = {xn <> Spec.sameAbove(above, span, Spec.leaves(ch)) : +List<Nat>}
                          (prival_rw(grammar, guards, marks, xn, q, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), xs, en, hR),
                            (unb_rw(grammar, guards, marks, ch, Spec.rhsOf(grammar, q), q, [], 0n, xs, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC)))
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Optional{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Closure{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Positive{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Eps{}:
                  unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
        case Spec.Pick{+a, +ch}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Nonterminal{+xn}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      match unb:
                        case (hR, (hU, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          +same = Spec.sameAbove(above, span, Spec.leaves(ch))
                          (arival_rw(grammar, guards, marks, alts, idx, path, a, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), Spec.lhsOf(grammar, idx) <> same, en, hR),
                            (unb_rw(grammar, guards, marks, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, same, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC)))
                    case Spec.Optional{}:
                      match unb:
                        case (hR, (hU, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          +same = Spec.sameAbove(above, span, Spec.leaves(ch))
                          (arival_rw(grammar, guards, marks, alts, idx, path, a, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), Spec.lhsOf(grammar, idx) <> same, en, hR),
                            (unb_rw(grammar, guards, marks, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, same, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC)))
                    case Spec.Closure{}:
                      match unb:
                        case (hR, (hU, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          +same = Spec.sameAbove(above, span, Spec.leaves(ch))
                          (arival_rw(grammar, guards, marks, alts, idx, path, a, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), Spec.lhsOf(grammar, idx) <> same, en, hR),
                            (unb_rw(grammar, guards, marks, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, same, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC)))
                    case Spec.Positive{}:
                      match unb:
                        case (hR, (hU, hC)):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          +path = List.append(&2, Nat, pre, [d])
                          +same = Spec.sameAbove(above, span, Spec.leaves(ch))
                          (arival_rw(grammar, guards, marks, alts, idx, path, a, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), Spec.lhsOf(grammar, idx) <> same, en, hR),
                            (unb_rw(grammar, guards, marks, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, same, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC)))
                case Spec.Eps{}:
                  unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
        case Spec.Skip{}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Nonterminal{+xn}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Optional{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Closure{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Positive{}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Eps{}:
                  unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
        case Spec.Loop{+rs}:
          match its:
            case Nil{}:
              Unit{}
            case Con{it, +rest}:
              match it:
                case Spec.Sym{sy}:
                  match sy:
                    case Spec.Terminal{k1}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                    case Spec.Nonterminal{+xn}:
                      unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)
                case Spec.Brack{kind, +alts}:
                  match kind:
                    case Spec.Group{}:
                      match unb:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (runb_rw(grammar, guards, marks, rs, alts, idx, List.append(&2, Nat, pre, [d]), above, span, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC))
                    case Spec.Optional{}:
                      match unb:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (runb_rw(grammar, guards, marks, rs, alts, idx, List.append(&2, Nat, pre, [d]), above, span, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC))
                    case Spec.Closure{}:
                      match unb:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (runb_rw(grammar, guards, marks, rs, alts, idx, List.append(&2, Nat, pre, [d]), above, span, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC))
                    case Spec.Positive{}:
                      match unb:
                        case (hR, hC):
                          +en = next_swap(l2, t, t2, r, after, lv)
                          (runb_rw(grammar, guards, marks, rs, alts, idx, List.append(&2, Nat, pre, [d]), above, span, List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hR), unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, hC))
                case Spec.Eps{}:
                  unb_lift(l2, t, t2, r, rest, grammar, guards, marks, idx, pre, 1n+d, above, span, after, lv, head, unb)

law runb_lift:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +r: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +path: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  for head: Spec.RoundsUnbeaten(grammar, guards, marks, t <> r, alts, idx, path, above, span, after) -> Spec.RoundsUnbeaten(grammar, guards, marks, t2 <> r, alts, idx, path, above, span, after)
  for unb: Spec.RoundsUnbeaten(grammar, guards, marks, List.append(&2, Spec.Tree, l, t <> r), alts, idx, path, above, span, after)
  Spec.RoundsUnbeaten(grammar, guards, marks, List.append(&2, Spec.Tree, l, t2 <> r), alts, idx, path, above, span, after)

def runb_lift(l, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, unb):
  match l:
    case Nil{}:
      head(unb)
    case Con{+u, +l2}:
      match u:
        case Spec.Leaf{k0}:
          runb_lift(l2, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, unb)
        case Spec.Node{+q, +ch}:
          runb_lift(l2, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, unb)
        case Spec.Pick{+a, +ch}:
          match unb:
            case (hR, (hU, hC)):
              +en = next_swap(l2, t, t2, r, after, lv)
              +same = Spec.sameAbove(above, span, Spec.leaves(ch))
              (arival_rw(grammar, guards, marks, alts, idx, path, a, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), Spec.lhsOf(grammar, idx) <> same, en, hR),
                (unb_rw(grammar, guards, marks, ch, Spec.altOf(alts, a), idx, List.append(&2, Nat, path, [a]), 0n, same, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t <> r)), after), List.append(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l2, t2 <> r)), after), en, hU), runb_lift(l2, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, hC)))
        case Spec.Skip{}:
          runb_lift(l2, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, unb)
        case Spec.Loop{+rs}:
          runb_lift(l2, t, t2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, head, unb)

law unb_head_node:
  for ys: +List<Spec.Item>
  for +q: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: UnbAt(grammar, guards, marks, nodeCtx(grammar, guards, q, ys, above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x) -> UnbAt(grammar, guards, marks, nodeCtx(grammar, guards, q, ys, above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for h: Spec.Unbeaten(grammar, guards, marks, Spec.Node{q, x} <> r, ys, idx, pre, dot, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, Spec.Node{q, x2} <> r, ys, idx, pre, dot, above, span, after)

def unb_head_node(ys, q, x, x2, r, grammar, guards, marks, idx, pre, dot, above, span, after, lv, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{+xn}:
              match h:
                case (hR, (hU, hC)):
                  +next = List.append(&2, Nat, Spec.leaves(r), after)
                  (p_rival_swap_node(grammar, guards, marks, xn, q, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
                    (p_unb_swap_node(grammar, guards, marks, q, x, x2, xn, above, span, next, lv, k(hU)), hC))
        case Spec.Brack{kind, alts}:
          match kind:
            case Spec.Group{}:
              h
            case Spec.Optional{}:
              h
            case Spec.Closure{}:
              h
            case Spec.Positive{}:
              h
        case Spec.Eps{}:
          h

law unb_head_pick:
  for ys: +List<Spec.Item>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: UnbAt(grammar, guards, marks, pickCtx(grammar, guards, a, ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x) -> UnbAt(grammar, guards, marks, pickCtx(grammar, guards, a, ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after), x), x2)
  for h: Spec.Unbeaten(grammar, guards, marks, Spec.Pick{a, x} <> r, ys, idx, pre, dot, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, Spec.Pick{a, x2} <> r, ys, idx, pre, dot, above, span, after)

def unb_head_pick(ys, a, x, x2, r, grammar, guards, marks, idx, pre, dot, above, span, after, lv, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{xn}:
              h
        case Spec.Brack{+kind, +alts}:
          match kind:
            case Spec.Group{}:
              match h:
                case (hR, (hU, hC)):
                  +next = List.append(&2, Nat, Spec.leaves(r), after)
                  +path = List.append(&2, Nat, pre, [dot])
                  (p_rival_swap_pick(grammar, guards, marks, alts, idx, path, a, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
                    (p_unb_swap_pick(grammar, guards, marks, alts, a, idx, List.append(&2, Nat, path, [a]), x, x2, above, span, next, lv, k(hU)), hC))
            case Spec.Optional{}:
              match h:
                case (hR, (hU, hC)):
                  +next = List.append(&2, Nat, Spec.leaves(r), after)
                  +path = List.append(&2, Nat, pre, [dot])
                  (p_rival_swap_pick(grammar, guards, marks, alts, idx, path, a, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
                    (p_unb_swap_pick(grammar, guards, marks, alts, a, idx, List.append(&2, Nat, path, [a]), x, x2, above, span, next, lv, k(hU)), hC))
            case Spec.Closure{}:
              match h:
                case (hR, (hU, hC)):
                  +next = List.append(&2, Nat, Spec.leaves(r), after)
                  +path = List.append(&2, Nat, pre, [dot])
                  (p_rival_swap_pick(grammar, guards, marks, alts, idx, path, a, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
                    (p_unb_swap_pick(grammar, guards, marks, alts, a, idx, List.append(&2, Nat, path, [a]), x, x2, above, span, next, lv, k(hU)), hC))
            case Spec.Positive{}:
              match h:
                case (hR, (hU, hC)):
                  +next = List.append(&2, Nat, Spec.leaves(r), after)
                  +path = List.append(&2, Nat, pre, [dot])
                  (p_rival_swap_pick(grammar, guards, marks, alts, idx, path, a, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
                    (p_unb_swap_pick(grammar, guards, marks, alts, a, idx, List.append(&2, Nat, path, [a]), x, x2, above, span, next, lv, k(hU)), hC))
        case Spec.Eps{}:
          h

law unb_head_loop:
  for ys: +List<Spec.Item>
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +pre: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for k: UnbAt(grammar, guards, marks, loopCtx(ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after)), x) -> UnbAt(grammar, guards, marks, loopCtx(ys, idx, List.append(&2, Nat, pre, [dot]), above, span, List.append(&2, Nat, Spec.leaves(r), after)), x2)
  for h: Spec.Unbeaten(grammar, guards, marks, Spec.Loop{x} <> r, ys, idx, pre, dot, above, span, after)
  Spec.Unbeaten(grammar, guards, marks, Spec.Loop{x2} <> r, ys, idx, pre, dot, above, span, after)

def unb_head_loop(ys, x, x2, r, grammar, guards, marks, idx, pre, dot, above, span, after, k, h):
  match ys:
    case Nil{}:
      Unit{}
    case Con{it, +rest}:
      match it:
        case Spec.Sym{sy}:
          match sy:
            case Spec.Terminal{k1}:
              h
            case Spec.Nonterminal{xn}:
              h
        case Spec.Brack{+kind, +alts}:
          match kind:
            case Spec.Group{}:
              match h:
                case (hR, hC):
                  (k(hR), hC)
            case Spec.Optional{}:
              match h:
                case (hR, hC):
                  (k(hR), hC)
            case Spec.Closure{}:
              match h:
                case (hR, hC):
                  (k(hR), hC)
            case Spec.Positive{}:
              match h:
                case (hR, hC):
                  (k(hR), hC)
        case Spec.Eps{}:
          h

law runb_head_pick:
  for +l: +List<Spec.Tree>
  for +a: Nat
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +alts: +List<+List<Spec.Item>>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +idx: Nat
  for +path: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: UnbAt(grammar, guards, marks, roundHole(grammar, guards, PickKid{l, a, r}, alts, idx, path, above, span, after, x), x) -> UnbAt(grammar, guards, marks, roundHole(grammar, guards, PickKid{l, a, r}, alts, idx, path, above, span, after, x), x2)
  for h: Spec.RoundsUnbeaten(grammar, guards, marks, Spec.Pick{a, x} <> r, alts, idx, path, above, span, after)
  Spec.RoundsUnbeaten(grammar, guards, marks, Spec.Pick{a, x2} <> r, alts, idx, path, above, span, after)

def runb_head_pick(l, a, x, x2, r, alts, grammar, guards, marks, idx, path, above, span, after, lv, k, h):
  match h:
    case (hR, (hU, hC)):
      +next = List.append(&2, Nat, Spec.leaves(r), after)
      (p_rival_swap_pick(grammar, guards, marks, alts, idx, path, a, Spec.leaves(x), Spec.leaves(x2), next, above, span, lv, hR),
        (p_unb_swap_pick(grammar, guards, marks, alts, a, idx, List.append(&2, Nat, path, [a]), x, x2, above, span, next, lv, k(hU)), hC))

law level_unb:
  for c: Ctx
  for fr: Frame
  for +x: +List<Spec.Tree>
  for +x2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +lv: {Spec.leaves(x2) == Spec.leaves(x) : +List<Nat>}
  for k: UnbAt(grammar, guards, marks, holeCtx(grammar, guards, fr, c, x), x) -> UnbAt(grammar, guards, marks, holeCtx(grammar, guards, fr, c, x), x2)
  for h: UnbAt(grammar, guards, marks, c, fill(fr, x))
  UnbAt(grammar, guards, marks, c, fill(fr, x2))

def level_unb(c, fr, x, x2, grammar, guards, marks, lv, k, h):
  match c:
    case SeqCtx{+own, +its, +idx, +pre, +above, +span, +after}:
      match fr:
        case NodeKid{+l, +q, +r}:
          unb_lift(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, its, grammar, guards, marks, idx, pre, 0n, above, span, after, wrap_lv(NodeKid{l, q, r}, x, x2, lv), hh => unb_head_node(itemsAfter(l, its), q, x, x2, r, grammar, guards, marks, idx, pre, dotAfter(l, 0n), above, span, after, lv, k, hh), h)
        case PickKid{+l, +a, +r}:
          unb_lift(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, its, grammar, guards, marks, idx, pre, 0n, above, span, after, wrap_lv(PickKid{l, a, r}, x, x2, lv), hh => unb_head_pick(itemsAfter(l, its), a, x, x2, r, grammar, guards, marks, idx, pre, dotAfter(l, 0n), above, span, after, lv, k, hh), h)
        case LoopKid{+l, +r}:
          unb_lift(l, Spec.Loop{x}, Spec.Loop{x2}, r, its, grammar, guards, marks, idx, pre, 0n, above, span, after, wrap_lv(LoopKid{l, r}, x, x2, lv), hh => unb_head_loop(itemsAfter(l, its), x, x2, r, grammar, guards, marks, idx, pre, dotAfter(l, 0n), above, span, after, k, hh), h)
    case RoundCtx{+alts, +idx, +pre, +above, +span, +after}:
      match fr:
        case NodeKid{+l, +q, +r}:
          runb_lift(l, Spec.Node{q, x}, Spec.Node{q, x2}, r, alts, grammar, guards, marks, idx, pre, above, span, after, wrap_lv(NodeKid{l, q, r}, x, x2, lv), hh => hh, h)
        case PickKid{+l, +a, +r}:
          runb_lift(l, Spec.Pick{a, x}, Spec.Pick{a, x2}, r, alts, grammar, guards, marks, idx, pre, above, span, after, wrap_lv(PickKid{l, a, r}, x, x2, lv), hh => runb_head_pick(l, a, x, x2, r, alts, grammar, guards, marks, idx, pre, above, span, after, lv, k, hh), h)
        case LoopKid{+l, +r}:
          runb_lift(l, Spec.Loop{x}, Spec.Loop{x2}, r, alts, grammar, guards, marks, idx, pre, above, span, after, wrap_lv(LoopKid{l, r}, x, x2, lv), hh => hh, h)
    case NoCtx{}:
      Unit{}

# PLUGGING, UNBEATEN: the tree keeps phase 2 when the forest in its hole is swapped for
# one over the same tokens that keeps phase 2 where it stands.
law plug_unb:
  for z: +List<Frame>
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +q0: Nat
  for +lv: {Spec.leaves(y2) == Spec.leaves(y) : +List<Nat>}
  for k: UnbAt(grammar, guards, marks, ctxOf(grammar, guards, start, q0, z, y), y) -> UnbAt(grammar, guards, marks, ctxOf(grammar, guards, start, q0, z, y), y2)
  for whole: Spec.Unbeaten(grammar, guards, marks, [Spec.Node{q0, zip(z, y)}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  Spec.Unbeaten(grammar, guards, marks, [Spec.Node{q0, zip(z, y2)}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])

def plug_unb(z, y, y2, grammar, guards, marks, start, q0, lv, k, whole):
  match z:
    case Nil{}:
      match whole:
        case (hR, (hU, hC)):
          (p_rival_swap_node(grammar, guards, marks, start, q0, Spec.leaves(y), Spec.leaves(y2), [], [], [], lv, hR),
            (p_unb_swap_node(grammar, guards, marks, q0, y, y2, start, [], [], [], lv, k(hU)), hC))
    case Con{+fr, +rest}:
      plug_unb(rest, fill(fr, y), fill(fr, y2), grammar, guards, marks, start, q0, leaves_fill(fr, y, y2, lv), hh => level_unb(ctxOf(grammar, guards, start, q0, rest, fill(fr, y)), fr, y, y2, grammar, guards, marks, lv, k, hh), whole)

# ======== PLUGGING, THE WHOLE TREE ========
# Every level fitting: the root's children fit its production.
law zip_top:
  for z: +List<Frame>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +ok: {zipOk(grammar, q0, z, y) == True{} : Bool}
  {Spec.fits(zip(z, y), grammar, Spec.rhsOf(grammar, q0)) == True{} : Bool}

def zip_top(z, grammar, q0, y, ok):
  match z:
    case Nil{}:
      ok
    case Con{+fr, +rest}:
      zip_top(rest, grammar, q0, fill(fr, y), Lemma.and_true_right_side(Spec.fits(y, grammar, holeItems(grammar, fr, holeOf(grammar, q0, rest, fill(fr, y)), y)), zipOk(grammar, q0, rest, fill(fr, y)), ok))

# The root keeps its production when its children are swapped for others that fit it.
law root_fit:
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +start: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +old: {Spec.fits([Spec.Node{q0, ch}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +nw: {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q0)) == True{} : Bool}
  {Spec.fits([Spec.Node{q0, ch2}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}

def root_fit(grammar, q0, start, ch, ch2, old, nw):
  +inner = Bool.and(Spec.lhsIs(grammar, q0, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q0)))
  +eL = Lemma.and_true_left(Spec.lhsIs(grammar, q0, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q0)), Lemma.and_true_left(inner, True{}, old))
  %Equal.sym(Bool, Spec.lhsIs(grammar, q0, start), True{}, eL) : {Bool.and(Bool.and(_, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q0))), True{}) == True{} : Bool}
  %Equal.sym(Bool, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q0)), True{}, nw) : {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
  {==}

law root_leaves:
  for +z: +List<Frame>
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +input: +List<Nat>
  for +lv: {Spec.leaves(y2) == Spec.leaves(y) : +List<Nat>}
  for +old: {Spec.leaves([Spec.Node{q0, zip(z, y)}]) == input : +List<Nat>}
  {Spec.leaves([Spec.Node{q0, zip(z, y2)}]) == input : +List<Nat>}

def root_leaves(z, q0, y, y2, input, lv, old):
  Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, zip(z, y2)}]), Spec.leaves([Spec.Node{q0, zip(z, y)}]), input,
    Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(zip(z, y2)), Spec.leaves(zip(z, y)), leaves_zip(z, y, y2, lv)), old)

# PLUGGING. An unbeaten tree with a forest swapped, at a hole of the zipper z, for one
# that fits the hole, reads the same tokens and keeps phases 1 and 2 where it stands, is
# still unbeaten; and the new forest's steps, walked where it stands, are the tree's.
law plug_tree:
  for +z: +List<Frame>
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +q0: Nat
  for +input: +List<Nat>
  for +ok: {zipOk(grammar, q0, z, y) == True{} : Bool}
  for +fitH: {Spec.fits(y2, grammar, holeOf(grammar, q0, z, y2)) == True{} : Bool}
  for +lv: {Spec.leaves(y2) == Spec.leaves(y) : +List<Nat>}
  for +sh: {zshape(z, y, y2) == True{} : Bool}
  for holdN: HoldAt(grammar, ctxOf(grammar, guards, start, q0, z, y), y2)
  for admN: AdmAt(grammar, guards, ctxOf(grammar, guards, start, q0, z, y), y2)
  for unbN: UnbAt(grammar, guards, marks, ctxOf(grammar, guards, start, q0, z, y), y2)
  for whole: Spec.UnbeatenTree(grammar, guards, marks, start, input, Spec.Node{q0, zip(z, y)})
  Spec.UnbeatenTree(grammar, guards, marks, start, input, Spec.Node{q0, zip(z, y2)}) & {Spec.allIn(walkAt(coordOf(q0, z), y2), Spec.steps(Spec.Node{q0, zip(z, y2)}, 0n)) == True{} : Bool}

def plug_tree(z, y, y2, grammar, guards, marks, start, q0, input, ok, fitH, lv, sh, holdN, admN, unbN, whole):
  match whole:
    case ((fit, (lvs, adm)), unb):
      +okN = zip_swap(z, y, y2, grammar, q0, ok, fitH, lv, sh)
      (((root_fit(grammar, q0, start, zip(z, y), zip(z, y2), fit, zip_top(z, grammar, q0, y2, okN)),
          (root_leaves(z, q0, y, y2, input, lv, lvs),
            plug_adm(z, y, y2, grammar, guards, start, q0, lv, hh => (holdN, admN), adm))),
        plug_unb(z, y, y2, grammar, guards, marks, start, q0, lv, hh => unbN, unb)),
        zip_steps(z, q0, y2, grammar, okN))

law plug_back:
  for +z: +List<Frame>
  for +y2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +q0: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for pt: Spec.UnbeatenTree(grammar, guards, marks, start, input, Spec.Node{q0, zip(z, y2)}) & {Spec.allIn(walkAt(coordOf(q0, z), y2), Spec.steps(Spec.Node{q0, zip(z, y2)}, 0n)) == True{} : Bool}
  for back: @t: Spec.Tree -> {Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool} -> {Spec.leaves([t]) == input : +List<Nat>} -> Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) -> Spec.Unbeaten(grammar, guards, marks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool}
  {Spec.allIn(walkAt(coordOf(q0, z), y2), set) == True{} : Bool}

def plug_back(z, y2, grammar, guards, marks, start, q0, input, set, pt, back):
  match pt:
    case (((fit0, (lv0, adm)), unb), st0):
      +st = {st0 : {Spec.allIn(walkAt(coordOf(q0, z), y2), Spec.steps(Spec.Node{q0, zip(z, y2)}, 0n)) == True{} : Bool}}
      +t2 = {Spec.Node{q0, zip(z, y2)} : Spec.Tree}
      +fit = {fit0 : {Spec.fits([t2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}}
      +lvs = {lv0 : {Spec.leaves([t2]) == input : +List<Nat>}}
      all_trans(walkAt(coordOf(q0, z), y2), Spec.steps(t2, 0n), set, st, back(t2, fit, lvs, adm, unb))

# A RIVAL'S STEPS. A forest that may take the hole's place, in an unbeaten tree of a set
# that holds the steps of every unbeaten tree: its steps, walked where it stands, are in
# the set.
law plug_rival:
  for +z: +List<Frame>
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +q0: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +ok: {zipOk(grammar, q0, z, y) == True{} : Bool}
  for +fitH: {Spec.fits(y2, grammar, holeOf(grammar, q0, z, y2)) == True{} : Bool}
  for +lv: {Spec.leaves(y2) == Spec.leaves(y) : +List<Nat>}
  for +sh: {zshape(z, y, y2) == True{} : Bool}
  for holdN: HoldAt(grammar, ctxOf(grammar, guards, start, q0, z, y), y2)
  for admN: AdmAt(grammar, guards, ctxOf(grammar, guards, start, q0, z, y), y2)
  for unbN: UnbAt(grammar, guards, marks, ctxOf(grammar, guards, start, q0, z, y), y2)
  for whole: Spec.UnbeatenTree(grammar, guards, marks, start, input, Spec.Node{q0, zip(z, y)})
  for back: @t: Spec.Tree -> {Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool} -> {Spec.leaves([t]) == input : +List<Nat>} -> Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) -> Spec.Unbeaten(grammar, guards, marks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool}
  {Spec.allIn(walkAt(coordOf(q0, z), y2), set) == True{} : Bool}

def plug_rival(z, y, y2, grammar, guards, marks, start, q0, input, set, ok, fitH, lv, sh, holdN, admN, unbN, whole, back):
  plug_back(z, y2, grammar, guards, marks, start, q0, input, set, plug_tree(z, y, y2, grammar, guards, marks, start, q0, input, ok, fitH, lv, sh, holdN, admN, unbN, whole), back)

# ======== THE ZIPPER ALONG A WALK ========

law and_both:
  for a: Bool
  for b: Bool
  for +ea: {a == True{} : Bool}
  for +eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_both(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# A frame's forest fits its items: so does the hole.
law node_fit:
  for it: Spec.Item
  for +q: Nat
  for +y: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Node{q, y}], grammar, [it]) == True{} : Bool}
  {Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}

def node_fit(it, q, y, grammar, e):
  match it:
    case Spec.Sym{sy}:
      match sy:
        case Spec.Terminal{k}:
          Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Nonterminal{+x}:
          Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(y, grammar, Spec.rhsOf(grammar, q)), Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(y, grammar, Spec.rhsOf(grammar, q))), True{}, e))
    case Spec.Brack{kind, +alts}:
      match kind:
        case Spec.Group{}:
          Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Optional{}:
          Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Closure{}:
          Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Positive{}:
          Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits(y, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, Lemma.false_is_not_true(e))

law pick_fit:
  for it: Spec.Item
  for +a: Nat
  for +y: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Pick{a, y}], grammar, [it]) == True{} : Bool}
  {Spec.fits(y, grammar, Gll.bracketAlt(Some{it}, a)) == True{} : Bool}

def pick_fit(it, a, y, grammar, e):
  match it:
    case Spec.Sym{sy}:
      match sy:
        case Spec.Terminal{k}:
          Empty.absurd({Spec.fits(y, grammar, Gll.bracketAlt(Some{Spec.Sym{Spec.Terminal{k}}}, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Nonterminal{+x}:
          Empty.absurd({Spec.fits(y, grammar, Gll.bracketAlt(Some{Spec.Sym{Spec.Nonterminal{x}}}, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{kind, +alts}:
      match kind:
        case Spec.Group{}:
          Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(y, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(y, grammar, Spec.altOf(alts, a))), True{}, e))
        case Spec.Optional{}:
          Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, y}]), Spec.isAlt(alts, a)), Spec.fits(y, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, y}]), Spec.isAlt(alts, a)), Spec.fits(y, grammar, Spec.altOf(alts, a))), True{}, e))
        case Spec.Closure{}:
          Empty.absurd({Spec.fits(y, grammar, Gll.bracketAlt(Some{Spec.Brack{Spec.Closure{}, alts}}, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Positive{}:
          Empty.absurd({Spec.fits(y, grammar, Gll.bracketAlt(Some{Spec.Brack{Spec.Positive{}, alts}}, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits(y, grammar, Gll.bracketAlt(Some{Spec.Eps{}}, a)) == True{} : Bool}, Lemma.false_is_not_true(e))

law loop_fit:
  for it: Spec.Item
  for +y: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([Spec.Loop{y}], grammar, [it]) == True{} : Bool}
  {Spec.fits(y, grammar, loopItems(it, List.length(&2, Spec.Tree, y))) == True{} : Bool}

def loop_fit(it, y, grammar, e):
  match it:
    case Spec.Sym{sy}:
      match sy:
        case Spec.Terminal{k}:
          Empty.absurd({Spec.fits(y, grammar, loopItems(Spec.Sym{Spec.Terminal{k}}, List.length(&2, Spec.Tree, y))) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Nonterminal{+x}:
          Empty.absurd({Spec.fits(y, grammar, loopItems(Spec.Sym{Spec.Nonterminal{x}}, List.length(&2, Spec.Tree, y))) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Brack{kind, +alts}:
      match kind:
        case Spec.Group{}:
          Empty.absurd({Spec.fits(y, grammar, loopItems(Spec.Brack{Spec.Group{}, alts}, List.length(&2, Spec.Tree, y))) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Optional{}:
          Empty.absurd({Spec.fits(y, grammar, loopItems(Spec.Brack{Spec.Optional{}, alts}, List.length(&2, Spec.Tree, y))) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Spec.Closure{}:
          Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, y), Spec.fits(y, grammar, Spec.times(List.length(&2, Spec.Tree, y), Spec.Brack{Spec.Group{}, alts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, y), Spec.fits(y, grammar, Spec.times(List.length(&2, Spec.Tree, y), Spec.Brack{Spec.Group{}, alts}))), True{}, e))
        case Spec.Positive{}:
          Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, y), Spec.fits(y, grammar, Spec.times(List.length(&2, Spec.Tree, y), Spec.Brack{Spec.Group{}, alts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, y), Spec.fits(y, grammar, Spec.times(List.length(&2, Spec.Tree, y), Spec.Brack{Spec.Group{}, alts}))), True{}, e))
    case Spec.Eps{}:
      Empty.absurd({Spec.fits(y, grammar, loopItems(Spec.Eps{}, List.length(&2, Spec.Tree, y))) == True{} : Bool}, Lemma.false_is_not_true(e))

law fr_fit:
  for +fr: Frame
  for +y: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +outer: +List<Spec.Item>
  for +e: {Spec.fits(fill(fr, y), grammar, outer) == True{} : Bool}
  {Spec.fits(y, grammar, holeItems(grammar, fr, outer, y)) == True{} : Bool}

def fr_fit(fr, y, grammar, outer, e):
  match fr:
    case NodeKid{+l, +q, +r}:
      node_fit(itemAtOr(outer, List.length(&2, Spec.Tree, l)), q, y, grammar, app_item(l, Spec.Node{q, y}, r, outer, grammar, e))
    case PickKid{+l, +a, +r}:
      pick_fit(itemAtOr(outer, List.length(&2, Spec.Tree, l)), a, y, grammar, app_item(l, Spec.Pick{a, y}, r, outer, grammar, e))
    case LoopKid{+l, +r}:
      loop_fit(itemAtOr(outer, List.length(&2, Spec.Tree, l)), y, grammar, app_item(l, Spec.Loop{y}, r, outer, grammar, e))

# A tree's fit gives every level's.
law unzip_ok:
  for z: +List<Frame>
  for +y: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +top: {Spec.fits(zip(z, y), grammar, Spec.rhsOf(grammar, q0)) == True{} : Bool}
  {zipOk(grammar, q0, z, y) == True{} : Bool}

def unzip_ok(z, y, grammar, q0, top):
  match z:
    case Nil{}:
      top
    case Con{+fr, +rest}:
      +ih = unzip_ok(rest, fill(fr, y), grammar, q0, top)
      +outer = holeOf(grammar, q0, rest, fill(fr, y))
      and_both(Spec.fits(y, grammar, holeItems(grammar, fr, outer, y)), zipOk(grammar, q0, rest, fill(fr, y)), fr_fit(fr, y, grammar, outer, zip_head(rest, grammar, q0, fill(fr, y), ih)), ih)

# One more tree before the hole.
law app_snoc:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, l, [t]), ts) == List.append(&2, Spec.Tree, l, t <> ts) : +List<Spec.Tree>}

def app_snoc(l, t, ts):
  match l:
    case Nil{}:
      {==}
    case Con{+u, +l2}:
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => u <> v, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, l2, [t]), ts), List.append(&2, Spec.Tree, l2, t <> ts), app_snoc(l2, t, ts))

law da_snoc:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +d: Nat
  {dotAfter(List.append(&2, Spec.Tree, l, [t]), d) == 1n+dotAfter(l, d) : Nat}

def da_snoc(l, t, d):
  match l:
    case Nil{}:
      {==}
    case Con{+u, +l2}:
      da_snoc(l2, t, 1n+d)

law da_len:
  for l: +List<Spec.Tree>
  for +d: Nat
  {dotAfter(l, d) == Nat.add(d, List.length(&2, Spec.Tree, l)) : Nat}

def da_len(l, d):
  match l:
    case Nil{}:
      Equal.sym(Nat, Nat.add(d, 0n), d, Lemma.add_zero_right(d))
    case Con{+u, +l2}:
      Equal.trans(Nat, dotAfter(l2, 1n+d), Nat.add(1n+d, List.length(&2, Spec.Tree, l2)), Nat.add(d, 1n+List.length(&2, Spec.Tree, l2)), da_len(l2, 1n+d), Equal.sym(Nat, Nat.add(d, 1n+List.length(&2, Spec.Tree, l2)), 1n+Nat.add(d, List.length(&2, Spec.Tree, l2)), Lemma.add_succ_right(d, List.length(&2, Spec.Tree, l2))))

def isNilI(xs: +List<Spec.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      False{}

def tailI(xs: +List<Spec.Item>) -> +List<Spec.Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, +rest}:
      rest

law ia_snoc:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for its: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +e: {itemsAfter(l, its) == it <> rest : +List<Spec.Item>}
  {itemsAfter(List.append(&2, Spec.Tree, l, [t]), its) == rest : +List<Spec.Item>}

def ia_snoc(l, t, its, it, rest, e):
  match l:
    case Nil{}:
      match its:
        case Nil{}:
          Empty.absurd({itemsAfter([t], []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => isNilI(v), [], it <> rest, e)))
        case Con{+x, +xs}:
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => tailI(v), x <> xs, it <> rest, e)
    case Con{+u, +l2}:
      match its:
        case Nil{}:
          Empty.absurd({itemsAfter(List.append(&2, Spec.Tree, u <> l2, [t]), []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => isNilI(v), [], it <> rest, e)))
        case Con{+x, +xs}:
          ia_snoc(l2, t, xs, it, rest, e)

def headI(xs: +List<Spec.Item>) -> Spec.Item:
  match xs:
    case Nil{}:
      Spec.Eps{}
    case Con{+x, rest}:
      x

law ia_at:
  for l: +List<Spec.Tree>
  for its: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +e: {itemsAfter(l, its) == it <> rest : +List<Spec.Item>}
  {itemAtOr(its, List.length(&2, Spec.Tree, l)) == it : Spec.Item}

def ia_at(l, its, it, rest, e):
  match l:
    case Nil{}:
      match its:
        case Nil{}:
          Empty.absurd({itemAtOr([], 0n) == it : Spec.Item}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => isNilI(v), [], it <> rest, e)))
        case Con{+x, +xs}:
          Equal.cong(+List<Spec.Item>, Spec.Item, v => headI(v), x <> xs, it <> rest, e)
    case Con{+u, +l2}:
      match its:
        case Nil{}:
          Empty.absurd({itemAtOr([], List.length(&2, Spec.Tree, u <> l2)) == it : Spec.Item}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => isNilI(v), [], it <> rest, e)))
        case Con{+x, +xs}:
          ia_at(l2, xs, it, rest, e)

# Where the next tree starts.
law k_snoc:
  for +l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +k0: Nat
  for +k: Nat
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(l))) : Nat}
  {Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))) == Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t])))) : Nat}

def k_snoc(l, t, k0, k, kE):
  +a = List.length(&2, Nat, Spec.leaves(l))
  +b = List.length(&2, Nat, Spec.leaves([t]))
  +lenE = Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t]))), List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(l), Spec.leaves([t]))), Nat.add(a, b), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(List.append(&2, Spec.Tree, l, [t])), List.append(&2, Nat, Spec.leaves(l), Spec.leaves([t])), leaves_app(l, [t])), Lemma.length_append(Spec.leaves(l), Spec.leaves([t])))
  Equal.trans(Nat, Nat.add(k, b), Nat.add(Nat.add(k0, a), b), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t])))), Equal.cong(Nat, Nat, v => Nat.add(v, b), k, Nat.add(k0, a), kE),
    Equal.trans(Nat, Nat.add(Nat.add(k0, a), b), Nat.add(k0, Nat.add(a, b)), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t])))), Lemma.add_assoc(k0, a, b), Equal.cong(Nat, Nat, v => Nat.add(k0, v), Nat.add(a, b), List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t]))), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, l, [t]))), Nat.add(a, b), lenE))))
