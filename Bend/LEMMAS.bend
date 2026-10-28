import Base

# General lemmas, independent of the grammar. Base has few lemmas that turn a
# Bool test into a proof, so the ones we need are proven here.

# ---- Bool ----

# The motive used to refute False == True: it sends False to Unit and True to Empty.
def TrueIsEmpty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False and True are different constructors, so an equality between them is impossible.
law false_is_not_true:
  for e: {False{} == True{} : Bool}
  Empty

# Rewriting True to False in the goal TrueIsEmpty(True) = Empty leaves TrueIsEmpty(False) = Unit.
def false_is_not_true(e):
  %e : TrueIsEmpty(_)
  Unit{}

law true_is_not_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_is_not_false(e):
  false_is_not_true(Equal.sym(Bool, True{}, False{}, e))

# A conjunction is True when both sides are True.
law and_true_intro:
  for x: Bool
  for -y: Bool
  for ex: {x == True{} : Bool}
  for ey: {y == True{} : Bool}
  {Bool.and(x, y) == True{} : Bool}

def and_true_intro(x, y, ex, ey):
  match x:
    case False{}:
      ex
    case True{}:
      ey

# A True conjunction has a True left side.
law and_true_left:
  for x: Bool
  for -y: Bool
  for e: {Bool.and(x, y) == True{} : Bool}
  {x == True{} : Bool}

def and_true_left(x, y, e):
  match x:
    case False{}:
      e
    case True{}:
      {==}

# A True conjunction has a True right side.
law and_true_right_side:
  for x: Bool
  for -y: Bool
  for e: {Bool.and(x, y) == True{} : Bool}
  {y == True{} : Bool}

def and_true_right_side(x, y, e):
  match x:
    case False{}:
      Empty.absurd({y == True{} : Bool}, false_is_not_true(e))
    case True{}:
      e

# A disjunction is True when its left side is True.
law or_true_left_intro:
  for x: Bool
  for -y: Bool
  for ex: {x == True{} : Bool}
  {Bool.or(x, y) == True{} : Bool}

def or_true_left_intro(x, y, ex):
  match x:
    case False{}:
      Empty.absurd({y == True{} : Bool}, false_is_not_true(ex))
    case True{}:
      {==}

# A disjunction is True when its right side is True.
law or_true_right_intro:
  for x: Bool
  for -y: Bool
  for ey: {y == True{} : Bool}
  {Bool.or(x, y) == True{} : Bool}

def or_true_right_intro(x, y, ey):
  match x:
    case False{}:
      ey
    case True{}:
      {==}

# A True disjunction has a True left side or a True right side; the result says which.
law or_true_cases:
  for x: Bool
  for -y: Bool
  for e: {Bool.or(x, y) == True{} : Bool}
  Either<{x == True{} : Bool}, {y == True{} : Bool}>

def or_true_cases(x, y, e):
  match x:
    case False{}:
      Inr{e}
    case True{}:
      Inl{{==}}

law or_false_left:
  for x: Bool
  for -y: Bool
  for ex: {x == False{} : Bool}
  for e: {Bool.or(x, y) == True{} : Bool}
  {y == True{} : Bool}

def or_false_left(x, y, ex, e):
  match x:
    case False{}:
      e
    case True{}:
      Empty.absurd({y == True{} : Bool}, true_is_not_false(ex))

# If x or y holds and y gives z, then x or z holds.
law or_mono_right:
  for x: Bool
  for -y: Bool
  for -z: Bool
  for e: {Bool.or(x, y) == True{} : Bool}
  for f: {y == True{} : Bool} -> {z == True{} : Bool}
  {Bool.or(x, z) == True{} : Bool}

def or_mono_right(x, y, z, e, f):
  match x:
    case True{}:
      {==}
    case False{}:
      f(e)

law or_false_right:
  for x: Bool
  for e: {Bool.or(x, False{}) == True{} : Bool}
  {x == True{} : Bool}

def or_false_right(x, e):
  match x:
    case False{}:
      e
    case True{}:
      {==}

law or_and_false:
  for x: Bool
  for -m: Bool
  for e: {Bool.or(Bool.and(x, False{}), m) == True{} : Bool}
  {m == True{} : Bool}

def or_and_false(x, m, e):
  match x:
    case False{}:
      e
    case True{}:
      e

# ---- Nat ----

# Nat.is_eq says True for equal numbers.
law nat_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def nat_eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

# Nat.is_eq says True only for equal numbers.
law nat_eq_sound:
  for a: Nat
  for b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def nat_eq_sound(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, false_is_not_true(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, false_is_not_true(e))
    case 1n+ap 1n+bp:
      %nat_eq_sound(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

law nat_eq_symm:
  for a: Nat
  for b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def nat_eq_symm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat_eq_symm(p, q)

law zero_le:
  for b: Nat
  {Nat.is_le(0n, b) == True{} : Bool}

def zero_le(b):
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

law le_refl:
  for n: Nat
  {Nat.is_le(n, n) == True{} : Bool}

def le_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

law le_succ_right:
  for x: Nat
  for y: Nat
  for e: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.is_le(x, 1n+y) == True{} : Bool}

def le_succ_right(x, y, e):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, false_is_not_true(e))
    case 1n+p 1n+q:
      le_succ_right(p, q, e)

law le_add_right:
  for a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

def le_add_right(a, b):
  match a:
    case 0n:
      zero_le(b)
    case 1n+q:
      le_add_right(q, b)

law le_add_left:
  for a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}

def le_add_left(a, b):
  match a:
    case 0n:
      le_refl(b)
    case 1n+(+q):
      le_succ_right(b, Nat.add(q, b), le_add_left(q, b))

law lt_zero_false:
  for s: Nat
  for e: {Nat.is_lt(s, 0n) == True{} : Bool}
  Empty

def lt_zero_false(s, e):
  match s:
    case 0n:
      false_is_not_true(e)
    case 1n+p:
      false_is_not_true(e)

# s < st + 1 and st != s give s < st.
law lt_succ_ne:
  for s: Nat
  for st: Nat
  for lt: {Nat.is_lt(s, 1n+st) == True{} : Bool}
  for ne: {Nat.is_eq(st, s) == False{} : Bool}
  {Nat.is_lt(s, st) == True{} : Bool}

def lt_succ_ne(s, st, lt, ne):
  match s st:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, true_is_not_false(ne))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, lt_zero_false(p, lt))
    case 1n+p 1n+q:
      lt_succ_ne(p, q, lt, ne)

# p <= f and f != p give p + 1 <= f.
law le_succ_ne:
  for p: Nat
  for f: Nat
  for le: {Nat.is_le(p, f) == True{} : Bool}
  for ne: {Nat.is_eq(f, p) == False{} : Bool}
  {Nat.is_le(1n+p, f) == True{} : Bool}

def le_succ_ne(p, f, le, ne):
  match p f:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, true_is_not_false(ne))
    case 0n 1n+q:
      zero_le(q)
    case 1n+r 0n:
      Empty.absurd({Nat.is_le(1n+1n+r, 0n) == True{} : Bool}, false_is_not_true(le))
    case 1n+r 1n+q:
      le_succ_ne(r, q, le, ne)

# Nat arithmetic.
law add_succ_right:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ_right(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_right(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law add_one_right:
  for n: Nat
  {Nat.add(n, 1n) == 1n+n : Nat}

def add_one_right(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_one_right(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def predOf(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law add_cancel_left:
  for a: Nat
  for -b: Nat
  for -c: Nat
  for e: {Nat.add(a, b) == Nat.add(a, c) : Nat}
  {b == c : Nat}

def add_cancel_left(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+p:
      add_cancel_left(p, b, c, Equal.cong(Nat, Nat, n => predOf(n), 1n+Nat.add(p, b), 1n+Nat.add(p, c), e))

law add_succ_ne:
  for i: Nat
  for +n: Nat
  {Nat.is_eq(Nat.add(i, 1n+n), i) == False{} : Bool}

def add_succ_ne(i, n):
  match i:
    case 0n:
      {==}
    case 1n+p:
      add_succ_ne(p, n)

law add_zero_right:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero_right(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_right(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_assoc:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      zero_le(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, false_is_not_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_is_not_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

law lt_pos:
  for s: Nat
  for n: Nat
  for lt: {Nat.is_lt(s, n) == True{} : Bool}
  {Nat.is_le(1n, n) == True{} : Bool}

def lt_pos(s, n, lt):
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, lt_zero_false(s, lt))
    case 1n+q:
      zero_le(q)

#
# Every element of the set is either a leaf step Bsr{Slot{p, 1}, s, s, s + 1} whose
# production is p = "t" with t the token at s, or a step Bsr{Slot{p, 2}, i, k, j}
# whose production is p = B C, with B in the table cell for i .. k and C in the
# cell for k .. j. All three BSR laws start from this fact.

law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law sub_add_left:
  for i: Nat
  for +x: Nat
  {Nat.sub(Nat.add(i, x), i) == x : Nat}

def sub_add_left(i, x):
  match i:
    case 0n:
      sub_zero(x)
    case 1n+p:
      sub_add_left(p, x)

law sub_add_add:
  for i: Nat
  for +x: Nat
  for +y: Nat
  {Nat.sub(Nat.add(i, Nat.add(x, y)), Nat.add(i, x)) == y : Nat}

def sub_add_add(i, x, y):
  match i:
    case 0n:
      sub_add_left(x, y)
    case 1n+p:
      sub_add_add(p, x, y)

law lt_self_add:
  for a: Nat
  for +r: Nat
  {Nat.is_lt(a, Nat.add(a, 1n+r)) == True{} : Bool}

def lt_self_add(a, r):
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_self_add(p, r)

law lt_offset:
  for i: Nat
  for +a: Nat
  for +r: Nat
  {Nat.is_lt(Nat.add(i, a), Nat.add(i, Nat.add(a, 1n+r))) == True{} : Bool}

def lt_offset(i, a, r):
  match i:
    case 0n:
      lt_self_add(a, r)
    case 1n+p:
      lt_offset(p, a, r)

law add_sub_cancel:
  for i: Nat
  for k: Nat
  for lt: {Nat.is_lt(i, k) == True{} : Bool}
  {Nat.add(i, Nat.sub(k, i)) == k : Nat}

def add_sub_cancel(i, k, lt):
  match i k:
    case 0n _:
      sub_zero(k)
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, false_is_not_true(lt))
    case 1n+p 1n+q:
      %add_sub_cancel(p, q, lt) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

law lt_of_succ_le:
  for a: Nat
  for b: Nat
  for e: {Nat.is_le(1n+a, b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def lt_of_succ_le(a, b, e):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, false_is_not_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_of_succ_le(p, q, e)

law le_of_succ_le:
  for a: Nat
  for b: Nat
  for e: {Nat.is_le(1n+a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_succ_le(a, b, e):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(a, 0n) == True{} : Bool}, false_is_not_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      le_of_succ_le(p, q, e)

law add_congr:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for ab: {a == b : Nat}
  for cd: {c == d : Nat}
  {Nat.add(a, c) == Nat.add(b, d) : Nat}

def add_congr(a, b, c, d, ab, cd):
  %Equal.sym(Nat, a, b, ab) : {Nat.add(_, c) == Nat.add(b, d) : Nat}
  %Equal.sym(Nat, c, d, cd) : {Nat.add(b, _) == Nat.add(b, d) : Nat}
  {==}

law nat_eq_of_eq:
  for +a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {Nat.is_eq(a, b) == True{} : Bool}

def nat_eq_of_eq(a, b, e):
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  nat_eq_refl(a)

# ---- Maybe ----

# None and Some are different, and Some is injective (for Maybe<Nat>).
def SomeNatIsEmpty(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{value}:
      Empty

law none_is_not_some_nat:
  for -value: Nat
  for e: {None{} == Some{value} : Maybe<&2, Nat>}
  Empty

def none_is_not_some_nat(value, e):
  %e : SomeNatIsEmpty(_)
  Unit{}

def valueOr(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{value}:
      value

law some_injective:
  for -a: Nat
  for -b: Nat
  for e: {Some{a} == Some{b} : Maybe<&2, Nat>}
  {a == b : Nat}

def some_injective(a, b, e):
  Equal.cong(Maybe<&2, Nat>, Nat, m => valueOr(m), Some{a}, Some{b}, e)

# ---- Lists of tokens ----

# The motive used to refute [] == h <> t.
def ConsIsEmpty(l: +List<Nat>) -> Type:
  match l:
    case Nil{}:
      Unit
    case Con{h, t}:
      Empty

law nil_is_not_cons:
  for -h: Nat
  for -t: +List<Nat>
  for e: {[] == h <> t : +List<Nat>}
  Empty

def nil_is_not_cons(h, t, e):
  %e : ConsIsEmpty(_)
  Unit{}

def headOr(l: +List<Nat>, default: Nat) -> Nat:
  match l:
    case Nil{}:
      default
    case Con{h, t}:
      h

law append_nil_right:
  for p: +List<Nat>
  {List.append(&2, Nat, p, []) == p : +List<Nat>}

def append_nil_right(p):
  match p:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_nil_right(t) : {h <> List.append(&2, Nat, t, []) == h <> _ : +List<Nat>}
      {==}

law append_congr:
  for -x: +List<Nat>
  for -y: +List<Nat>
  for -x2: +List<Nat>
  for -y2: +List<Nat>
  for ex: {x == x2 : +List<Nat>}
  for ey: {y == y2 : +List<Nat>}
  {List.append(&2, Nat, x, y) == List.append(&2, Nat, x2, y2) : +List<Nat>}

def append_congr(x, y, x2, y2, ex, ey):
  %ex : {List.append(&2, Nat, x, y) == List.append(&2, Nat, _, y2) : +List<Nat>}
  %ey : {List.append(&2, Nat, x, y) == List.append(&2, Nat, x, _) : +List<Nat>}
  {==}

law length_append:
  for +x: +List<Nat>
  for +y: +List<Nat>
  {List.length(&2, Nat, List.append(&2, Nat, x, y)) == Nat.add(List.length(&2, Nat, x), List.length(&2, Nat, y)) : Nat}

def length_append(x, y):
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      %length_append(t, y) : {1n+List.length(&2, Nat, List.append(&2, Nat, t, y)) == 1n+_ : Nat}
      {==}

law nonempty_append:
  for x: +List<Nat>
  for -y: +List<Nat>
  for e: {List.is_empty(&2, Nat, x) == False{} : Bool}
  {List.is_empty(&2, Nat, List.append(&2, Nat, x, y)) == False{} : Bool}

def nonempty_append(x, y, e):
  match x:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, Nat, y) == False{} : Bool}, true_is_not_false(e))
    case Con{h, t}:
      {==}

# ---- Take and drop ----

# Own versions of drop and take that look at the count first, so that dropping or
# taking 0 elements computes without knowing the list.

def dropN(n: Nat, xs: +List<Nat>) -> +List<Nat>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          dropN(p, t)

def takeN(n: Nat, xs: +List<Nat>) -> +List<Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          h <> takeN(p, t)

law take_nil:
  for n: Nat
  {takeN(n, []) == [] : +List<Nat>}

def take_nil(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law drop_nil:
  for n: Nat
  {dropN(n, []) == [] : +List<Nat>}

def drop_nil(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Taking k and then m more is taking k + m.
law take_drop_split:
  for +k: Nat
  for +m: Nat
  for +d: +List<Nat>
  {List.append(&2, Nat, takeN(k, d), takeN(m, dropN(k, d))) == takeN(Nat.add(k, m), d) : +List<Nat>}

def take_drop_split(k, m, d):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match d:
        case Nil{}:
          take_nil(m)
        case Con{h, t}:
          %take_drop_split(p, m, t) : {h <> List.append(&2, Nat, takeN(p, t), takeN(m, dropN(p, t))) == h <> _ : +List<Nat>}
          {==}

# Dropping s + k is dropping s, then k.
law drop_add:
  for +s: Nat
  for +k: Nat
  for +x: +List<Nat>
  {dropN(Nat.add(s, k), x) == dropN(k, dropN(s, x)) : +List<Nat>}

def drop_add(s, k, x):
  match s:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case Nil{}:
          Equal.sym(+List<Nat>, dropN(k, []), [], drop_nil(k))
        case Con{h, t}:
          drop_add(p, k, t)

# Taking the whole list gives the list.
law take_length:
  for +x: +List<Nat>
  {takeN(List.length(&2, Nat, x), x) == x : +List<Nat>}

def take_length(x):
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      %take_length(t) : {h <> takeN(List.length(&2, Nat, t), t) == h <> _ : +List<Nat>}
      {==}

law take_take:
  for +k: Nat
  for +m: Nat
  for +d: +List<Nat>
  {takeN(k, takeN(Nat.add(k, m), d)) == takeN(k, d) : +List<Nat>}

def take_take(k, m, d):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match d:
        case Nil{}:
          {==}
        case Con{h, t}:
          %take_take(p, m, t) : {h <> takeN(p, takeN(Nat.add(p, m), t)) == h <> _ : +List<Nat>}
          {==}

law drop_take:
  for +k: Nat
  for +m: Nat
  for +d: +List<Nat>
  {dropN(k, takeN(Nat.add(k, m), d)) == takeN(m, dropN(k, d)) : +List<Nat>}

def drop_take(k, m, d):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match d:
        case Nil{}:
          Equal.sym(+List<Nat>, takeN(m, []), [], take_nil(m))
        case Con{h, t}:
          drop_take(p, m, t)

law take_append_length:
  for +x: +List<Nat>
  for +y: +List<Nat>
  {takeN(List.length(&2, Nat, x), List.append(&2, Nat, x, y)) == x : +List<Nat>}

def take_append_length(x, y):
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      %take_append_length(t, y) : {h <> takeN(List.length(&2, Nat, t), List.append(&2, Nat, t, y)) == h <> _ : +List<Nat>}
      {==}

law drop_append_length:
  for +x: +List<Nat>
  for +y: +List<Nat>
  {dropN(List.length(&2, Nat, x), List.append(&2, Nat, x, y)) == y : +List<Nat>}

def drop_append_length(x, y):
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      drop_append_length(t, y)

law length_take_le:
  for n: Nat
  for +d: +List<Nat>
  {Nat.is_le(List.length(&2, Nat, takeN(n, d)), List.length(&2, Nat, d)) == True{} : Bool}

def length_take_le(n, d):
  match n:
    case 0n:
      zero_le(List.length(&2, Nat, d))
    case 1n+p:
      match d:
        case Nil{}:
          {==}
        case Con{h, t}:
          length_take_le(p, t)

law length_drop_le:
  for s: Nat
  for +x: +List<Nat>
  {Nat.is_le(List.length(&2, Nat, dropN(s, x)), List.length(&2, Nat, x)) == True{} : Bool}

def length_drop_le(s, x):
  match s:
    case 0n:
      le_refl(List.length(&2, Nat, x))
    case 1n+(+p):
      match x:
        case Nil{}:
          {==}
        case Con{h, +t}:
          le_succ_right(List.length(&2, Nat, dropN(p, t)), List.length(&2, Nat, t), length_drop_le(p, t))

# ---- Slices: the `length` tokens of an input from position `start` ----

# The `length` tokens of the input from position `start`.
def slice(+inputTokens: +List<Nat>, +start: Nat, +length: Nat) -> +List<Nat>:
  takeN(length, dropN(start, inputTokens))

# Adjacent slices join into one.
law slice_split:
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +k: Nat
  for +m: Nat
  {List.append(&2, Nat, slice(inputTokens, s, k), slice(inputTokens, Nat.add(s, k), m)) == slice(inputTokens, s, Nat.add(k, m)) : +List<Nat>}

def slice_split(inputTokens, s, k, m):
  %Equal.sym(+List<Nat>, dropN(Nat.add(s, k), inputTokens), dropN(k, dropN(s, inputTokens)), drop_add(s, k, inputTokens)) : {List.append(&2, Nat, takeN(k, dropN(s, inputTokens)), takeN(m, _)) == takeN(Nat.add(k, m), dropN(s, inputTokens)) : +List<Nat>}
  take_drop_split(k, m, dropN(s, inputTokens))

# The token at position s is the slice of length 1 at s.
law get_slice:
  for +inputTokens: +List<Nat>
  for +s: Nat
  for -kind: Nat
  for e: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  {slice(inputTokens, s, 1n) == [kind] : +List<Nat>}

def get_slice(inputTokens, s, kind, e):
  match inputTokens s:
    case Nil{} _:
      Empty.absurd({slice([], s, 1n) == [kind] : +List<Nat>}, none_is_not_some_nat(kind, e))
    case Con{h, t} 0n:
      %some_injective(h, kind, e) : {[h] == [_] : +List<Nat>}
      {==}
    case Con{h, t} 1n+p:
      get_slice(t, p, kind, e)

# A slice of length 1 is the token at its start.
law slice_get:
  for +inputTokens: +List<Nat>
  for s: Nat
  for +kind: Nat
  for e: {slice(inputTokens, s, 1n) == [kind] : +List<Nat>}
  {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}

def slice_get(inputTokens, s, kind, e):
  match inputTokens s:
    case Nil{} 0n:
      Empty.absurd({List.get(&2, Nat, [], 0n) == Some{kind} : Maybe<&2, Nat>}, nil_is_not_cons(kind, [], e))
    case Nil{} 1n+q:
      Empty.absurd({List.get(&2, Nat, [], 1n+q) == Some{kind} : Maybe<&2, Nat>}, nil_is_not_cons(kind, [], e))
    case Con{+x, xs} 0n:
      %Equal.cong(+List<Nat>, Nat, l => headOr(l, 0n), [x], [kind], e) : {Some{x} == Some{_} : Maybe<&2, Nat>}
      {==}
    case Con{x, xs} 1n+q:
      slice_get(xs, q, kind, e)

# A non-empty slice starts inside the input.
law slice_start_lt:
  for +inputTokens: +List<Nat>
  for s: Nat
  for +l: Nat
  for -h: Nat
  for -r: +List<Nat>
  for e: {slice(inputTokens, s, l) == h <> r : +List<Nat>}
  {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}

def slice_start_lt(inputTokens, s, l, h, r, e):
  match inputTokens s:
    case Nil{} 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, nil_is_not_cons(h, r, Equal.trans(+List<Nat>, [], takeN(l, []), h <> r, Equal.sym(+List<Nat>, takeN(l, []), [], take_nil(l)), e)))
    case Nil{} 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, nil_is_not_cons(h, r, Equal.trans(+List<Nat>, [], takeN(l, []), h <> r, Equal.sym(+List<Nat>, takeN(l, []), [], take_nil(l)), e)))
    case Con{x, xs} 0n:
      {==}
    case Con{x, xs} 1n+q:
      slice_start_lt(xs, q, l, h, r, e)

law slice_left:
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for eq: {slice(inputTokens, s, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))) == List.append(&2, Nat, w1, w2) : +List<Nat>}
  {slice(inputTokens, s, List.length(&2, Nat, w1)) == w1 : +List<Nat>}

def slice_left(inputTokens, s, w1, w2, eq):
  +k = List.length(&2, Nat, w1)
  +total = Nat.add(k, List.length(&2, Nat, w2))
  +d = dropN(s, inputTokens)
  Equal.trans(
    +List<Nat>,
    takeN(k, d),
    takeN(k, takeN(total, d)),
    w1,
    Equal.sym(+List<Nat>, takeN(k, takeN(total, d)), takeN(k, d), take_take(k, List.length(&2, Nat, w2), d)),
    Equal.trans(
      +List<Nat>,
      takeN(k, takeN(total, d)),
      takeN(k, List.append(&2, Nat, w1, w2)),
      w1,
      Equal.cong(+List<Nat>, +List<Nat>, x => takeN(k, x), takeN(total, d), List.append(&2, Nat, w1, w2), eq),
      take_append_length(w1, w2)))

law slice_right:
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for eq: {slice(inputTokens, s, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))) == List.append(&2, Nat, w1, w2) : +List<Nat>}
  {slice(inputTokens, Nat.add(s, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)) == w2 : +List<Nat>}

def slice_right(inputTokens, s, w1, w2, eq):
  +k = List.length(&2, Nat, w1)
  +m = List.length(&2, Nat, w2)
  +total = Nat.add(k, m)
  +d = dropN(s, inputTokens)
  Equal.trans(
    +List<Nat>,
    takeN(m, dropN(Nat.add(s, k), inputTokens)),
    takeN(m, dropN(k, d)),
    w2,
    Equal.cong(+List<Nat>, +List<Nat>, x => takeN(m, x), dropN(Nat.add(s, k), inputTokens), dropN(k, d), drop_add(s, k, inputTokens)),
    Equal.trans(
      +List<Nat>,
      takeN(m, dropN(k, d)),
      dropN(k, takeN(total, d)),
      w2,
      Equal.sym(+List<Nat>, dropN(k, takeN(total, d)), takeN(m, dropN(k, d)), drop_take(k, m, d)),
      Equal.trans(
        +List<Nat>,
        dropN(k, takeN(total, d)),
        dropN(k, List.append(&2, Nat, w1, w2)),
        w2,
        Equal.cong(+List<Nat>, +List<Nat>, x => dropN(k, x), takeN(total, d), List.append(&2, Nat, w1, w2), eq),
        drop_append_length(w1, w2))))

law slice_len_le:
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +l: Nat
  for -w: +List<Nat>
  for e: {slice(inputTokens, s, l) == w : +List<Nat>}
  for len: {List.length(&2, Nat, w) == l : Nat}
  {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool}

def slice_len_le(inputTokens, s, l, w, e, len):
  +d = dropN(s, inputTokens)
  lenSlice = Equal.trans(Nat, List.length(&2, Nat, slice(inputTokens, s, l)), List.length(&2, Nat, w), l, Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), slice(inputTokens, s, l), w, e), len)
  %lenSlice : {Nat.is_le(_, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  le_trans(List.length(&2, Nat, takeN(l, d)), List.length(&2, Nat, d), List.length(&2, Nat, inputTokens), length_take_le(l, d), length_drop_le(s, inputTokens))

# True is the unit of a conjunction.
law and_true_unit:
  for x: Bool
  {Bool.and(x, True{}) == x : Bool}

def and_true_unit(x):
  match x:
    case False{}:
      {==}
    case True{}:
      {==}
