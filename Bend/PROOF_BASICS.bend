import Base
import ./LEMMAS.bend as Lemma

# SMALL FACTS SHARED BY THE CORE'S PROOFS: about Bool, Nat and lists of naturals.

law succ_not_zero:
  for +n: Nat
  for +e: {1n+n == 0n : Nat}
  Empty

def succ_not_zero(n, e):
  Lemma.false_is_not_true(Equal.cong(Nat, Bool, v => Nat.is_eq(v, 0n), 1n+n, 0n, e))

law succ_inj:
  for +a: Nat
  for +b: Nat
  for +e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, v => Lemma.predOf(v), 1n+a, 1n+b, e)

law eq_is_eq:
  for +a: Nat
  for +b: Nat
  for +e: {a == b : Nat}
  {Nat.is_eq(a, b) == True{} : Bool}

def eq_is_eq(a, b, e):
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

law or_not_true:
  for b: Bool
  for +y: Bool
  for +hb: {b == True{} : Bool}
  for +h: {Bool.or(Bool.not(b), y) == True{} : Bool}
  {y == True{} : Bool}

def or_not_true(b, y, hb, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({y == True{} : Bool}, Lemma.false_is_not_true(hb))

law not_both:
  for b: Bool
  for +hb: {b == True{} : Bool}
  for +hn: {Bool.not(b) == True{} : Bool}
  Empty

def not_both(b, hb, hn):
  match b:
    case True{}:
      Lemma.false_is_not_true(hn)
    case False{}:
      Lemma.false_is_not_true(hb)

law append_nil_left:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +e: {List.append(&2, Nat, a, b) == [] : +List<Nat>}
  {a == [] : +List<Nat>}

def append_nil_left(a, b, e):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Empty.absurd({x <> rest == [] : +List<Nat>}, Lemma.nil_is_not_cons(x, List.append(&2, Nat, rest, b), Equal.sym(+List<Nat>, x <> List.append(&2, Nat, rest, b), [], e)))

law append_nil_right:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +e: {List.append(&2, Nat, a, b) == [] : +List<Nat>}
  {b == [] : +List<Nat>}

def append_nil_right(a, b, e):
  match a:
    case Nil{}:
      e
    case Con{+x, +rest}:
      Empty.absurd({b == [] : +List<Nat>}, Lemma.nil_is_not_cons(x, List.append(&2, Nat, rest, b), Equal.sym(+List<Nat>, x <> List.append(&2, Nat, rest, b), [], e)))

