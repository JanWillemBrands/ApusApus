import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./LEMMAS.bend as Lemma
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_SUBPARSE.bend as Sub
import ./PROOF_PREFER.bend as Pf
import ./PROOF_LL1.bend as L
import ./FITS.bend as Fits

# AN LL(1) GRAMMAR IS UNAMBIGUOUS. Compare two parse trees of the same input from the left.
# At the same position both see the same next token, since they spell the same input.
# Where they first make different choices, each choice predicts that token: by FIRST when
# its part reads something, else it derives nothing and FOLLOW has the token (read from
# the tree's own steps). That is a clash, which LL(1) rules out. The comparison itself does
# not use LL(1); the law uses it once, on the clash.

# ======== LISTS OF STEPS ========

law all_in_left:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_left(xs, ys, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +m = Spec.bsrMember(x, set)
      Lemma.and_true_intro(m, Spec.allIn(rest, set), Lemma.and_true_left(m, Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), h),
        all_in_left(rest, ys, set, Lemma.and_true_right_side(m, Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), h)))

law all_in_right:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(ys, set) == True{} : Bool}

def all_in_right(xs, ys, set, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      all_in_right(rest, ys, set, Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), h))

law all_in_tail:
  for +x: Spec.Bsr
  for +xs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for h: {Spec.allIn(x <> xs, set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_tail(x, xs, set, h):
  Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(xs, set), h)

# ======== SEQUENCES FROM THE DOT ========

def headItem(xs: +List<Spec.Item>) -> Maybe<&2, Spec.Item>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      Some{x}

def tailItems(xs: +List<Spec.Item>) -> +List<Spec.Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      rest


law items_from_head:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.itemsFrom(n, seq) == it <> rest : +List<Spec.Item>}
  {Spec.itemAt(seq, n) == Some{it} : Maybe<&2, Spec.Item>}

def items_from_head(n, seq, it, rest, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({Spec.itemAt([], 0n) == Some{it} : Maybe<&2, Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> rest, e)))
    case 0n Con{+x, +xs}:
      Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => headItem(v), x <> xs, it <> rest, e)
    case 1n+m Nil{}:
      Empty.absurd({Spec.itemAt([], 1n+m) == Some{it} : Maybe<&2, Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> rest, e)))
    case 1n+(+m) Con{x, +xs}:
      items_from_head(m, xs, it, rest, e)

law items_from_tail:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.itemsFrom(n, seq) == it <> rest : +List<Spec.Item>}
  {Spec.itemsFrom(1n+n, seq) == rest : +List<Spec.Item>}

def items_from_tail(n, seq, it, rest, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({Spec.itemsFrom(1n, []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> rest, e)))
    case 0n Con{+x, +xs}:
      Equal.trans(+List<Spec.Item>, Spec.itemsFrom(0n, xs), tailItems(x <> xs), rest, {==}, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => tailItems(v), x <> xs, it <> rest, e))
    case 1n+m Nil{}:
      Empty.absurd({Spec.itemsFrom(2n+m, []) == rest : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> rest, e)))
    case 1n+(+m) Con{x, +xs}:
      items_from_tail(m, xs, it, rest, e)

# The last item: the sequence has dot + 1 items.
law items_from_last:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for e: {Spec.itemsFrom(n, seq) == [it] : +List<Spec.Item>}
  {List.length(&2, Spec.Item, seq) == 1n+n : Nat}

def items_from_last(n, seq, it, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({0n == 1n : Nat}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> [], e)))
    case 0n Con{+x, +xs}:
      +rest = Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => tailItems(v), x <> xs, [it], e)
      Equal.cong(+List<Spec.Item>, Nat, v => 1n+List.length(&2, Spec.Item, v), xs, [], rest)
    case 1n+m Nil{}:
      Empty.absurd({0n == 2n+m : Nat}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, Spec.Item, v), [], it <> [], e)))
    case 1n+(+m) Con{x, +xs}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Item, xs), 1n+m, items_from_last(m, xs, it, e))

# The empty sequence: no items.
law items_from_none:
  for seq: +List<Spec.Item>
  for e: {Spec.itemsFrom(0n, seq) == [] : +List<Spec.Item>}
  {List.length(&2, Spec.Item, seq) == 0n : Nat}

def items_from_none(seq, e):
  Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), seq, [], e)
