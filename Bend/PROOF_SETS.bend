import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./FIRST.bend as First
import ./LEMMAS.bend as Lemma

# LOOKAHEAD SETS: membership through union, `lsIf`, `restOr` and subsets.

# ---- Token lists ----

law nat_in_pick:
  for b: Bool
  for +x: Nat
  for +x0: Nat
  for +zs: +List<Nat>
  for m: {Gll.natIn(x, zs) == True{} : Bool}
  {Gll.natIn(x, Gll.natAddPick(b, x0, zs)) == True{} : Bool}

def nat_in_pick(b, x, x0, zs, m):
  match b:
    case True{}:
      m
    case False{}:
      Lemma.or_true_right_intro(Nat.is_eq(x, x0), Gll.natIn(x, zs), m)

law nat_in_pick_self:
  for b: Bool
  for +x0: Nat
  for +zs: +List<Nat>
  for +bEq: {Gll.natIn(x0, zs) == b : Bool}
  {Gll.natIn(x0, Gll.natAddPick(b, x0, zs)) == True{} : Bool}

def nat_in_pick_self(b, x0, zs, bEq):
  match b:
    case True{}:
      bEq
    case False{}:
      Lemma.or_true_left_intro(Nat.is_eq(x0, x0), Gll.natIn(x0, zs), Lemma.nat_eq_refl(x0))

law nat_in_union_right:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +x: Nat
  for m: {Gll.natIn(x, ys) == True{} : Bool}
  {Gll.natIn(x, Gll.natsUnion(xs, ys)) == True{} : Bool}

def nat_in_union_right(xs, ys, x, m):
  match xs:
    case Nil{}:
      m
    case Con{+x0, +rest}:
      +zs = Gll.natsUnion(rest, ys)
      nat_in_pick(Gll.natIn(x0, zs), x, x0, zs, nat_in_union_right(rest, ys, x, m))

law nat_in_head_pick:
  for +x: Nat
  for +x0: Nat
  for +rest: +List<Nat>
  for +ys: +List<Nat>
  for c: Either<{Nat.is_eq(x, x0) == True{} : Bool}, {Gll.natIn(x, rest) == True{} : Bool}>
  for later: {Gll.natIn(x, rest) == True{} : Bool} -> {Gll.natIn(x, Gll.natsUnion(rest, ys)) == True{} : Bool}
  {Gll.natIn(x, Gll.natAddPick(Gll.natIn(x0, Gll.natsUnion(rest, ys)), x0, Gll.natsUnion(rest, ys))) == True{} : Bool}

def nat_in_head_pick(x, x0, rest, ys, c, later):
  match c:
    case Inl{same}:
      +zs = Gll.natsUnion(rest, ys)
      +ex = Equal.sym(Nat, x, x0, Lemma.nat_eq_sound(x, x0, same))
      %ex : {Gll.natIn(_, Gll.natAddPick(Gll.natIn(x0, zs), x0, zs)) == True{} : Bool}
      nat_in_pick_self(Gll.natIn(x0, zs), x0, zs, {==})
    case Inr{inRest}:
      +zs = Gll.natsUnion(rest, ys)
      nat_in_pick(Gll.natIn(x0, zs), x, x0, zs, later(inRest))

law nat_in_union_left:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +x: Nat
  for m: {Gll.natIn(x, xs) == True{} : Bool}
  {Gll.natIn(x, Gll.natsUnion(xs, ys)) == True{} : Bool}

def nat_in_union_left(xs, ys, x, m):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.natIn(x, Gll.natsUnion([], ys)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+x0, +rest}:
      nat_in_head_pick(x, x0, rest, ys, Lemma.or_true_cases(Nat.is_eq(x, x0), Gll.natIn(x, rest), m),
        inRest => nat_in_union_left(rest, ys, x, inRest))

law nat_sub_in_pick:
  for +x: Nat
  for +x0: Nat
  for +rest: +List<Nat>
  for +ys: +List<Nat>
  for c: Either<{Nat.is_eq(x, x0) == True{} : Bool}, {Gll.natIn(x, rest) == True{} : Bool}>
  for here: {Gll.natIn(x0, ys) == True{} : Bool}
  for later: {Gll.natIn(x, rest) == True{} : Bool} -> {Gll.natIn(x, ys) == True{} : Bool}
  {Gll.natIn(x, ys) == True{} : Bool}

def nat_sub_in_pick(x, x0, rest, ys, c, here, later):
  match c:
    case Inl{same}:
      +ex = Equal.sym(Nat, x, x0, Lemma.nat_eq_sound(x, x0, same))
      %ex : {Gll.natIn(_, ys) == True{} : Bool}
      here
    case Inr{inRest}:
      later(inRest)

law nat_sub_in:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +x: Nat
  for sub: {First.natsSub(xs, ys) == True{} : Bool}
  for m: {Gll.natIn(x, xs) == True{} : Bool}
  {Gll.natIn(x, ys) == True{} : Bool}

def nat_sub_in(xs, ys, x, sub, m):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.natIn(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+x0, +rest}:
      +both = sub
      nat_sub_in_pick(x, x0, rest, ys, Lemma.or_true_cases(Nat.is_eq(x, x0), Gll.natIn(x, rest), m),
        Lemma.and_true_left(Gll.natIn(x0, ys), First.natsSub(rest, ys), both),
        inRest => nat_sub_in(rest, ys, x, Lemma.and_true_right_side(Gll.natIn(x0, ys), First.natsSub(rest, ys), both), inRest))

# ---- Lookahead sets ----

# x or y gives (x or z) or (y or w).
law or_or_left:
  for +x: Bool
  for +y: Bool
  for +z: Bool
  for +w: Bool
  for e: {Bool.or(x, y) == True{} : Bool}
  {Bool.or(Bool.or(x, z), Bool.or(y, w)) == True{} : Bool}

def or_or_left(x, y, z, w, e):
  match x:
    case True{}:
      {==}
    case False{}:
      Lemma.or_true_right_intro(z, Bool.or(y, w), Lemma.or_true_left_intro(y, w, e))

law or_or_right_pick:
  for +x: Bool
  for +y: Bool
  for +z: Bool
  for +w: Bool
  for c: Either<{z == True{} : Bool}, {w == True{} : Bool}>
  {Bool.or(Bool.or(x, z), Bool.or(y, w)) == True{} : Bool}

def or_or_right_pick(x, y, z, w, c):
  match c:
    case Inl{ez}:
      Lemma.or_true_left_intro(Bool.or(x, z), Bool.or(y, w), Lemma.or_true_right_intro(x, z, ez))
    case Inr{ew}:
      Lemma.or_true_right_intro(Bool.or(x, z), Bool.or(y, w), Lemma.or_true_right_intro(y, w, ew))

# z or w gives (x or z) or (y or w).
law or_or_right:
  for +x: Bool
  for +y: Bool
  for +z: Bool
  for +w: Bool
  for e: {Bool.or(z, w) == True{} : Bool}
  {Bool.or(Bool.or(x, z), Bool.or(y, w)) == True{} : Bool}

def or_or_right(x, y, z, w, e):
  or_or_right_pick(x, y, z, w, Lemma.or_true_cases(z, w, e))

# any1 or t in t1 gives (any1 or any2) or t in (t1 ∪ t2).
law or_in_left_pick:
  for +a1: Bool
  for +a2: Bool
  for +t: Nat
  for +t1: +List<Nat>
  for +t2: +List<Nat>
  for c: Either<{a1 == True{} : Bool}, {Gll.natIn(t, t1) == True{} : Bool}>
  {Bool.or(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2))) == True{} : Bool}

def or_in_left_pick(a1, a2, t, t1, t2, c):
  match c:
    case Inl{ea}:
      Lemma.or_true_left_intro(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2)), Lemma.or_true_left_intro(a1, a2, ea))
    case Inr{et}:
      Lemma.or_true_right_intro(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2)), nat_in_union_left(t1, t2, t, et))

law or_in_left:
  for +a1: Bool
  for +a2: Bool
  for +t: Nat
  for +t1: +List<Nat>
  for +t2: +List<Nat>
  for h: {Bool.or(a1, Gll.natIn(t, t1)) == True{} : Bool}
  {Bool.or(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2))) == True{} : Bool}

def or_in_left(a1, a2, t, t1, t2, h):
  or_in_left_pick(a1, a2, t, t1, t2, Lemma.or_true_cases(a1, Gll.natIn(t, t1), h))

law or_in_right_pick:
  for +a1: Bool
  for +a2: Bool
  for +t: Nat
  for +t1: +List<Nat>
  for +t2: +List<Nat>
  for c: Either<{a2 == True{} : Bool}, {Gll.natIn(t, t2) == True{} : Bool}>
  {Bool.or(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2))) == True{} : Bool}

def or_in_right_pick(a1, a2, t, t1, t2, c):
  match c:
    case Inl{ea}:
      Lemma.or_true_left_intro(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2)), Lemma.or_true_right_intro(a1, a2, ea))
    case Inr{et}:
      Lemma.or_true_right_intro(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2)), nat_in_union_right(t1, t2, t, et))

law or_in_right:
  for +a1: Bool
  for +a2: Bool
  for +t: Nat
  for +t1: +List<Nat>
  for +t2: +List<Nat>
  for h: {Bool.or(a2, Gll.natIn(t, t2)) == True{} : Bool}
  {Bool.or(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2))) == True{} : Bool}

def or_in_right(a1, a2, t, t1, t2, h):
  or_in_right_pick(a1, a2, t, t1, t2, Lemma.or_true_cases(a2, Gll.natIn(t, t2), h))

# The token is in the union when it is in the left set.
law ls_has_union_left:
  for +tok: Maybe<&2, Nat>
  for +a: Gll.LSet
  for +b: Gll.LSet
  for h: {Gll.lsHas(tok, a) == True{} : Bool}
  {Gll.lsHas(tok, Gll.lsUnion(a, b)) == True{} : Bool}

def ls_has_union_left(tok, a, b, h):
  match tok a b:
    case None{} Gll.LSet{a1, t1, e1} Gll.LSet{a2, t2, e2}:
      or_or_left(a1, e1, a2, e2, h)
    case Some{+t} Gll.LSet{a1, +t1, e1} Gll.LSet{a2, +t2, e2}:
      or_in_left(a1, a2, t, t1, t2, h)

law ls_has_union_right:
  for +tok: Maybe<&2, Nat>
  for +a: Gll.LSet
  for +b: Gll.LSet
  for h: {Gll.lsHas(tok, b) == True{} : Bool}
  {Gll.lsHas(tok, Gll.lsUnion(a, b)) == True{} : Bool}

def ls_has_union_right(tok, a, b, h):
  match tok a b:
    case None{} Gll.LSet{a1, t1, e1} Gll.LSet{a2, t2, e2}:
      or_or_right(a1, e1, a2, e2, h)
    case Some{+t} Gll.LSet{a1, +t1, e1} Gll.LSet{a2, +t2, e2}:
      or_in_right(a1, a2, t, t1, t2, h)

law ls_has_if:
  for +b: Bool
  for +tok: Maybe<&2, Nat>
  for +s: Gll.LSet
  for bEq: {b == True{} : Bool}
  for h: {Gll.lsHas(tok, s) == True{} : Bool}
  {Gll.lsHas(tok, Gll.lsIf(b, s)) == True{} : Bool}

def ls_has_if(b, tok, s, bEq, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({Gll.lsHas(tok, Gll.lsIf(False{}, s)) == True{} : Bool}, Lemma.false_is_not_true(bEq))

# A token of the first set of a sequence, or of what comes after it when it can be empty,
# is in `restOr`.
law rest_or_first:
  for +tok: Maybe<&2, Nat>
  for +i: Gll.Info
  for +after: Gll.LSet
  for h: {Gll.lsHas(tok, Gll.firstOf(i)) == True{} : Bool}
  {Gll.lsHas(tok, Gll.restOr(i, after)) == True{} : Bool}

def rest_or_first(tok, i, after, h):
  ls_has_union_left(tok, Gll.firstOf(i), Gll.lsIf(Gll.nulOf(i), after), h)

law rest_or_after:
  for +tok: Maybe<&2, Nat>
  for +i: Gll.Info
  for +after: Gll.LSet
  for nul: {Gll.nulOf(i) == True{} : Bool}
  for h: {Gll.lsHas(tok, after) == True{} : Bool}
  {Gll.lsHas(tok, Gll.restOr(i, after)) == True{} : Bool}

def rest_or_after(tok, i, after, nul, h):
  ls_has_union_right(tok, Gll.firstOf(i), Gll.lsIf(Gll.nulOf(i), after), ls_has_if(Gll.nulOf(i), tok, after, nul, h))

# e1 and (not e1 or e2) give e2.
law end_pick:
  for +e1: Bool
  for +e2: Bool
  for h: {e1 == True{} : Bool}
  for ee: {Bool.or(Bool.not(e1), e2) == True{} : Bool}
  {e2 == True{} : Bool}

def end_pick(e1, e2, h, ee):
  match e1:
    case True{}:
      ee
    case False{}:
      Empty.absurd({e2 == True{} : Bool}, Lemma.false_is_not_true(h))

# A subset keeps what the smaller set has: the parts, once the "everything" flag of the
# bigger set is known to be off.
law sub_has_parts:
  for +tok: Maybe<&2, Nat>
  for +a1: Bool
  for +t1: +List<Nat>
  for +e1: Bool
  for +a2: Bool
  for +t2: +List<Nat>
  for +e2: Bool
  for rest: {Bool.and(Bool.not(a1), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2))) == True{} : Bool}
  for h: {Gll.lsHas(tok, Gll.LSet{a1, t1, e1}) == True{} : Bool}
  {Gll.lsHas(tok, Gll.LSet{a2, t2, e2}) == True{} : Bool}

def sub_has_parts(tok, a1, t1, e1, a2, t2, e2, rest, h):
  match tok a1:
    case None{} False{}:
      +r2 = Lemma.and_true_right_side(Bool.not(False{}), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2)), rest)
      ee = Lemma.and_true_right_side(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2), r2)
      Lemma.or_true_right_intro(a2, e2, end_pick(e1, e2, h, ee))
    case Some{+t} False{}:
      +r2 = Lemma.and_true_right_side(Bool.not(False{}), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2)), rest)
      sub = Lemma.and_true_left(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2), r2)
      Lemma.or_true_right_intro(a2, Gll.natIn(t, t2), nat_sub_in(t1, t2, t, sub, h))
    case _ True{}:
      Empty.absurd({Gll.lsHas(tok, Gll.LSet{a2, t2, e2}) == True{} : Bool}, Lemma.false_is_not_true(Lemma.and_true_left(Bool.not(True{}), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2)), rest)))

# The set of everything has every token.
law any_has:
  for +tok: Maybe<&2, Nat>
  for +a2: Bool
  for +t2: +List<Nat>
  for +e2: Bool
  for ea: {a2 == True{} : Bool}
  {Gll.lsHas(tok, Gll.LSet{a2, t2, e2}) == True{} : Bool}

def any_has(tok, a2, t2, e2, ea):
  match tok:
    case None{}:
      Lemma.or_true_left_intro(a2, e2, ea)
    case Some{+t}:
      Lemma.or_true_left_intro(a2, Gll.natIn(t, t2), ea)

law sub_has_pick:
  for +tok: Maybe<&2, Nat>
  for +a1: Bool
  for +t1: +List<Nat>
  for +e1: Bool
  for +a2: Bool
  for +t2: +List<Nat>
  for +e2: Bool
  for c: Either<{a2 == True{} : Bool}, {Bool.and(Bool.not(a1), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2))) == True{} : Bool}>
  for h: {Gll.lsHas(tok, Gll.LSet{a1, t1, e1}) == True{} : Bool}
  {Gll.lsHas(tok, Gll.LSet{a2, t2, e2}) == True{} : Bool}

def sub_has_pick(tok, a1, t1, e1, a2, t2, e2, c, h):
  match c:
    case Inl{ea}:
      any_has(tok, a2, t2, e2, ea)
    case Inr{rest}:
      sub_has_parts(tok, a1, t1, e1, a2, t2, e2, rest, h)

# A subset has every token of the smaller set.
law ls_sub_has:
  for +tok: Maybe<&2, Nat>
  for +a: Gll.LSet
  for +b: Gll.LSet
  for sub: {First.lsSub(a, b) == True{} : Bool}
  for h: {Gll.lsHas(tok, a) == True{} : Bool}
  {Gll.lsHas(tok, b) == True{} : Bool}

def ls_sub_has(tok, a, b, sub, h):
  match a b:
    case Gll.LSet{+a1, +t1, +e1} Gll.LSet{+a2, +t2, +e2}:
      sub_has_pick(tok, a1, t1, e1, a2, t2, e2, Lemma.or_true_cases(a2, Bool.and(Bool.not(a1), Bool.and(First.natsSub(t1, t2), Bool.or(Bool.not(e1), e2))), sub), h)

# ---- Inversions: a token of a union is in one of its sides ----

law nat_in_pick_inv:
  for b: Bool
  for +x: Nat
  for +x0: Nat
  for +zs: +List<Nat>
  for m: {Gll.natIn(x, Gll.natAddPick(b, x0, zs)) == True{} : Bool}
  Either<{Nat.is_eq(x, x0) == True{} : Bool}, {Gll.natIn(x, zs) == True{} : Bool}>

def nat_in_pick_inv(b, x, x0, zs, m):
  match b:
    case True{}:
      Inr{m}
    case False{}:
      Lemma.or_true_cases(Nat.is_eq(x, x0), Gll.natIn(x, zs), m)

law nat_in_rest_or:
  for +x: Nat
  for +x0: Nat
  for +rest: +List<Nat>
  for +ys: +List<Nat>
  for c: Either<{Gll.natIn(x, rest) == True{} : Bool}, {Gll.natIn(x, ys) == True{} : Bool}>
  Either<{Gll.natIn(x, x0 <> rest) == True{} : Bool}, {Gll.natIn(x, ys) == True{} : Bool}>

def nat_in_rest_or(x, x0, rest, ys, c):
  match c:
    case Inl{inR}:
      Inl{Lemma.or_true_right_intro(Nat.is_eq(x, x0), Gll.natIn(x, rest), inR)}
    case Inr{inY}:
      Inr{inY}

law nat_in_union_inv_pick:
  for +x: Nat
  for +x0: Nat
  for +rest: +List<Nat>
  for +ys: +List<Nat>
  for c: Either<{Nat.is_eq(x, x0) == True{} : Bool}, {Gll.natIn(x, Gll.natsUnion(rest, ys)) == True{} : Bool}>
  for later: {Gll.natIn(x, Gll.natsUnion(rest, ys)) == True{} : Bool} -> Either<{Gll.natIn(x, rest) == True{} : Bool}, {Gll.natIn(x, ys) == True{} : Bool}>
  Either<{Gll.natIn(x, x0 <> rest) == True{} : Bool}, {Gll.natIn(x, ys) == True{} : Bool}>

def nat_in_union_inv_pick(x, x0, rest, ys, c, later):
  match c:
    case Inl{same}:
      Inl{Lemma.or_true_left_intro(Nat.is_eq(x, x0), Gll.natIn(x, rest), same)}
    case Inr{inU}:
      nat_in_rest_or(x, x0, rest, ys, later(inU))

law nat_in_union_inv:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +x: Nat
  for m: {Gll.natIn(x, Gll.natsUnion(xs, ys)) == True{} : Bool}
  Either<{Gll.natIn(x, xs) == True{} : Bool}, {Gll.natIn(x, ys) == True{} : Bool}>

def nat_in_union_inv(xs, ys, x, m):
  match xs:
    case Nil{}:
      Inr{m}
    case Con{+x0, +rest}:
      +zs = Gll.natsUnion(rest, ys)
      nat_in_union_inv_pick(x, x0, rest, ys, nat_in_pick_inv(Gll.natIn(x0, zs), x, x0, zs, m),
        inU => nat_in_union_inv(rest, ys, x, inU))

law or4_left:
  for +a1: Bool
  for +a2: Bool
  for +e1: Bool
  for +e2: Bool
  for c: Either<{a1 == True{} : Bool}, {a2 == True{} : Bool}>
  Either<{Bool.or(a1, e1) == True{} : Bool}, {Bool.or(a2, e2) == True{} : Bool}>

def or4_left(a1, a2, e1, e2, c):
  match c:
    case Inl{x}:
      Inl{Lemma.or_true_left_intro(a1, e1, x)}
    case Inr{y}:
      Inr{Lemma.or_true_left_intro(a2, e2, y)}

law or4_right:
  for +a1: Bool
  for +a2: Bool
  for +e1: Bool
  for +e2: Bool
  for c: Either<{e1 == True{} : Bool}, {e2 == True{} : Bool}>
  Either<{Bool.or(a1, e1) == True{} : Bool}, {Bool.or(a2, e2) == True{} : Bool}>

def or4_right(a1, a2, e1, e2, c):
  match c:
    case Inl{x}:
      Inl{Lemma.or_true_right_intro(a1, e1, x)}
    case Inr{y}:
      Inr{Lemma.or_true_right_intro(a2, e2, y)}

law or_in_split:
  for +a1: Bool
  for +a2: Bool
  for +t: Nat
  for +t1: +List<Nat>
  for +t2: +List<Nat>
  for c: Either<{Bool.or(a1, a2) == True{} : Bool}, {Gll.natIn(t, Gll.natsUnion(t1, t2)) == True{} : Bool}>
  Either<{Bool.or(a1, Gll.natIn(t, t1)) == True{} : Bool}, {Bool.or(a2, Gll.natIn(t, t2)) == True{} : Bool}>

def or_in_split(a1, a2, t, t1, t2, c):
  match c:
    case Inl{ea}:
      or4_left(a1, a2, Gll.natIn(t, t1), Gll.natIn(t, t2), Lemma.or_true_cases(a1, a2, ea))
    case Inr{en}:
      or4_right(a1, a2, Gll.natIn(t, t1), Gll.natIn(t, t2), nat_in_union_inv(t1, t2, t, en))

law or4_split:
  for +a1: Bool
  for +a2: Bool
  for +e1: Bool
  for +e2: Bool
  for c: Either<{Bool.or(a1, a2) == True{} : Bool}, {Bool.or(e1, e2) == True{} : Bool}>
  Either<{Bool.or(a1, e1) == True{} : Bool}, {Bool.or(a2, e2) == True{} : Bool}>

def or4_split(a1, a2, e1, e2, c):
  match c:
    case Inl{ea}:
      or4_left(a1, a2, e1, e2, Lemma.or_true_cases(a1, a2, ea))
    case Inr{ee}:
      or4_right(a1, a2, e1, e2, Lemma.or_true_cases(e1, e2, ee))

law ls_has_union_inv:
  for +tok: Maybe<&2, Nat>
  for +a: Gll.LSet
  for +b: Gll.LSet
  for h: {Gll.lsHas(tok, Gll.lsUnion(a, b)) == True{} : Bool}
  Either<{Gll.lsHas(tok, a) == True{} : Bool}, {Gll.lsHas(tok, b) == True{} : Bool}>

def ls_has_union_inv(tok, a, b, h):
  match tok a b:
    case None{} Gll.LSet{+a1, t1, +e1} Gll.LSet{+a2, t2, +e2}:
      or4_split(a1, a2, e1, e2, Lemma.or_true_cases(Bool.or(a1, a2), Bool.or(e1, e2), h))
    case Some{+t} Gll.LSet{+a1, +t1, e1} Gll.LSet{+a2, +t2, e2}:
      or_in_split(a1, a2, t, t1, t2, Lemma.or_true_cases(Bool.or(a1, a2), Gll.natIn(t, Gll.natsUnion(t1, t2)), h))
