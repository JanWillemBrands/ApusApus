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

# ======== THE END STEP OF A SEQUENCE ========

# The walk of a sequence has the step of its last slot, ending where the forest ends.
def EndAt(+grammar: +List<Spec.Production>, +index: Nat, +prefix: +List<Nat>, +i: Nat, +fin: Nat, +ws: +List<Spec.Bsr>) -> Type:
  &K: Nat -> {Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, K, fin), ws) == True{} : Bool}

law fits_nil_items:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([], grammar, items) == True{} : Bool}
  {items == [] : +List<Spec.Item>}

def fits_nil_items(items, grammar, e):
  match items:
    case Nil{}:
      {==}
    case Con{it, rest}:
      Empty.absurd({it <> rest == [] : +List<Spec.Item>}, Lemma.false_is_not_true(e))

# The head step is the end step: the sequence has dot + 1 items and the forest ends at e.
law end_here:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +fin: Nat
  for +ws: +List<Spec.Bsr>
  for +lenEq: {List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)) == 1n+dot : Nat}
  for +finE: {fin == e : Nat}
  EndAt(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, e) <> ws)

def end_here(grammar, index, prefix, dot, i, k, e, fin, ws, lenEq, finE):
  +here = Spec.at(index, prefix, 1n+dot, i, k, e)
  (k, Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, fin), here <> ws), Spec.bsrMember(here, here <> ws), True{},
    Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, fin), here <> ws), Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, fin), here <> ws), Spec.bsrMember(here, here <> ws),
      Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, k, fin), here <> ws), List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), 1n+dot, lenEq),
      Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, v), here <> ws), fin, e, finE)),
    R.bsr_member_head(here, ws)))

# The end step is later: it is in the tail's walk.
law end_later:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +fin: Nat
  for +h: Spec.Bsr
  for +pre: +List<Spec.Bsr>
  for +ws: +List<Spec.Bsr>
  for got: EndAt(grammar, index, prefix, i, fin, ws)
  EndAt(grammar, index, prefix, i, fin, h <> List.append(&2, Spec.Bsr, pre, ws))

def end_later(grammar, index, prefix, i, fin, h, pre, ws, got):
  match got:
    case (K0, m):
      +K = {K0 : Nat}
      (K, R.bsr_member_cons(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, K, fin), h, List.append(&2, Spec.Bsr, pre, ws), Sub.member_app_right(pre, ws, Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, K, fin), m)))

law end_walk:
  for forest: +List<Spec.Tree>
  for items: +List<Spec.Item>
  for +dot: Nat
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +fin: Nat
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == items : +List<Spec.Item>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ok: {Bool.or(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, forest))) == True{} : Bool}
  EndAt(grammar, index, prefix, i, fin, Spec.walk(forest, False{}, index, prefix, dot, i, k))

def end_walk(forest, items, dot, grammar, index, prefix, i, k, fin, fit, itemsEq, finEq, ok):
  match forest items dot:
    case Nil{} _ 0n:
      +none = fits_nil_items(items, grammar, fit)
      +lenEq = items_from_none(Spec.sequenceAt(grammar, index, prefix), Equal.trans(+List<Spec.Item>, Spec.itemsFrom(0n, Spec.sequenceAt(grammar, index, prefix)), items, [], itemsEq, none))
      +here = Spec.at(index, prefix, 0n, i, k, k)
      +finK = Equal.trans(Nat, fin, Nat.add(k, 0n), k, Equal.sym(Nat, Nat.add(k, 0n), fin, finEq), Lemma.add_zero_right(k))
      (k, Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, fin), [here]), Spec.bsrMember(here, [here]), True{},
        Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, fin), [here]), Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, fin), [here]), Spec.bsrMember(here, [here]),
          Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, k, fin), [here]), List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), 0n, lenEq),
          Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, v), [here]), fin, k, finK)),
        R.bsr_member_head(here, [])))
    case Nil{} _ 1n+d:
      Empty.absurd(EndAt(grammar, index, prefix, i, fin, []), Lemma.false_is_not_true(ok))
    case Con{t, ts} Nil{} _:
      Empty.absurd(EndAt(grammar, index, prefix, i, fin, Spec.walk(t <> ts, False{}, index, prefix, dot, i, k)), Fits.fits_cons_nil(t, ts, grammar, fit))
    case Con{Spec.Leaf{+kind}, Nil{}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Leaf{kind}, [], grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, Spec.sequenceAt(grammar, index, prefix), it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, 1n+k, fin, Spec.walk([], False{}, index, prefix, 1n+dot, i, 1n+k), lenEq, Equal.trans(Nat, fin, Nat.add(k, 1n), 1n+k, Equal.sym(Nat, Nat.add(k, 1n), fin, finEq), Lemma.add_one_right(k)))
    case Con{Spec.Leaf{+kind}, Con{+t2, +ts2}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Leaf{kind}, t2 <> ts2, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      end_later(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, 1n+k), [], Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, 1n+k), end_walk(t2 <> ts2, rest, 1n+dot, grammar, index, prefix, i, 1n+k, fin, ftail, restEq, Equal.trans(Nat, Nat.add(1n+k, List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(t2 <> ts2))), fin, Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(t2 <> ts2))), 1n+Nat.add(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Lemma.add_succ_right(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), finEq), {==}))
    case Con{Spec.Node{+q, +ch}, Nil{}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Node{q, ch}, [], grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, Spec.sequenceAt(grammar, index, prefix), it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), fin, List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), lenEq, Equal.trans(Nat, fin, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), fin, finEq), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), G.end_alone(k, Spec.leaves(ch)))))
    case Con{Spec.Node{+q, +ch}, Con{+t2, +ts2}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Node{q, ch}, t2 <> ts2, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      end_later(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), end_walk(t2 <> ts2, rest, 1n+dot, grammar, index, prefix, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), fin, ftail, restEq, Equal.trans(Nat, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(t2 <> ts2)))), fin, G.end_split(k, Spec.leaves(ch), Spec.leaves(t2 <> ts2)), finEq), {==}))
    case Con{Spec.Pick{+a, +ch}, Nil{}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Pick{a, ch}, [], grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, Spec.sequenceAt(grammar, index, prefix), it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), fin, List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), lenEq, Equal.trans(Nat, fin, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), fin, finEq), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), G.end_alone(k, Spec.leaves(ch)))))
    case Con{Spec.Pick{+a, +ch}, Con{+t2, +ts2}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Pick{a, ch}, t2 <> ts2, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      end_later(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), end_walk(t2 <> ts2, rest, 1n+dot, grammar, index, prefix, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), fin, ftail, restEq, Equal.trans(Nat, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(t2 <> ts2)))), fin, G.end_split(k, Spec.leaves(ch), Spec.leaves(t2 <> ts2)), finEq), {==}))
    case Con{Spec.Skip{}, Nil{}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Skip{}, [], grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, Spec.sequenceAt(grammar, index, prefix), it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, k, fin, Spec.walk([], False{}, index, prefix, 1n+dot, i, k), lenEq, Equal.trans(Nat, fin, Nat.add(k, 0n), k, Equal.sym(Nat, Nat.add(k, 0n), fin, finEq), Lemma.add_zero_right(k)))
    case Con{Spec.Skip{}, Con{+t2, +ts2}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Skip{}, t2 <> ts2, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      end_later(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, k), [], Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, k), end_walk(t2 <> ts2, rest, 1n+dot, grammar, index, prefix, i, k, fin, ftail, restEq, finEq, {==}))
    case Con{Spec.Loop{+rs}, Nil{}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Loop{rs}, [], grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, Spec.sequenceAt(grammar, index, prefix), it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), fin, List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))), lenEq, Equal.trans(Nat, fin, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), []))), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), []))), fin, finEq), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), []))), G.end_alone(k, Spec.leaves(rs)))))
    case Con{Spec.Loop{+rs}, Con{+t2, +ts2}} Con{+it, +rest} _:
      +ftail = Fits.fits_tail(Spec.Loop{rs}, t2 <> ts2, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, rest, itemsEq)
      end_later(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), end_walk(t2 <> ts2, rest, 1n+dot, grammar, index, prefix, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), fin, ftail, restEq, Equal.trans(Nat, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), Spec.leaves(t2 <> ts2)))), fin, G.end_split(k, Spec.leaves(rs), Spec.leaves(t2 <> ts2)), finEq), {==}))

# ======== WHAT A PART OF A TREE PREDICTS ========

# A forest that reads something starts with the token at its position.
law first_token:
  for +input: +List<Nat>
  for +forest: +List<Spec.Tree>
  for +k: Nat
  for +t0: Nat
  for +w: +List<Nat>
  for +lv: {Spec.leaves(forest) == t0 <> w : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  {List.get(&2, Nat, input, k) == Some{t0} : Maybe<&2, Nat>}

def first_token(input, forest, k, t0, w, lv, sp):
  G.leaf_token(input, k, t0, w,
    Equal.trans(+List<Nat>, t0 <> w, Spec.leaves(forest), Lemma.slice(input, k, List.length(&2, Nat, t0 <> w)), Equal.sym(+List<Nat>, Spec.leaves(forest), t0 <> w, lv),
      Equal.trans(+List<Nat>, Spec.leaves(forest), Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(forest))), Lemma.slice(input, k, List.length(&2, Nat, t0 <> w)), sp,
        Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.slice(input, k, List.length(&2, Nat, v)), Spec.leaves(forest), t0 <> w, lv))))

# FIRST: a forest of the items that reads something.
law first_from:
  for w: +List<Nat>
  for next: Maybe<&2, Nat>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +forest: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +k: Nat
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +lv: {Spec.leaves(forest) == w : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for +nextEq: {List.get(&2, Nat, input, k) == next : Maybe<&2, Nat>}
  for +reads: {Bool.not(List.is_empty(&2, Nat, w)) == True{} : Bool}
  Spec.FirstOf(grammar, items, next)

def first_from(w, next, grammar, input, forest, items, k, fit, lv, sp, nextEq, reads):
  match w next:
    case Nil{} _:
      Empty.absurd(Spec.FirstOf(grammar, items, next), Lemma.false_is_not_true(reads))
    case Con{+t0, +w2} None{}:
      Empty.absurd(Spec.FirstOf(grammar, items, None{}), Lemma.none_is_not_some_nat(t0, Equal.trans(Maybe<&2, Nat>, None{}, List.get(&2, Nat, input, k), Some{t0}, Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, input, k), None{}, nextEq), first_token(input, forest, k, t0, w2, lv, sp))))
    case Con{+t0, +w2} Some{+tok}:
      +same = Lemma.some_injective(t0, tok, Equal.trans(Maybe<&2, Nat>, Some{t0}, List.get(&2, Nat, input, k), Some{tok}, Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, input, k), Some{t0}, first_token(input, forest, k, t0, w2, lv, sp)), nextEq))
      (w2, (forest, (fit, Equal.trans(+List<Nat>, Spec.leaves(forest), t0 <> w2, tok <> w2, lv, Equal.cong(Nat, +List<Nat>, v => v <> w2, t0, tok, same)))))

# PREDICT: a forest of the items, at position k, whose sequence ends (in the root's steps)
# where the forest ends.
law predicts_from:
  for w: +List<Nat>
  for next: Maybe<&2, Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +forest: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +k: Nat
  for +i2: Nat
  for +K: Nat
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +lv: {Spec.leaves(forest) == w : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for +nextEq: {List.get(&2, Nat, input, k) == next : Maybe<&2, Nat>}
  for +endIn: {Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i2, K, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest)))), Spec.steps(root, 0n)) == True{} : Bool}
  Spec.Predicts(grammar, start, items, index, prefix, next)

def predicts_from(w, next, grammar, start, input, root, rootFit, rootSp, forest, items, index, prefix, k, i2, K, fit, lv, sp, nextEq, endIn):
  match w:
    case Nil{}:
      +len = List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix))
      +atK = Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))), Nat.add(k, 0n), k,
        Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, v)), Spec.leaves(forest), [], lv), Lemma.add_zero_right(k))
      +inK = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, len, i2, K, k), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefix, len, i2, K, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest)))), Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, len, i2, K, v), Spec.steps(root, 0n)), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))), Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))), k, atK)), endIn)
      (False{}, ((forest, (fit, lv)), (input, (root, (i2, (K, (k, (rootFit, (rootSp, (inK, nextEq))))))))))
    case Con{+t0, +w2}:
      (True{}, first_from(t0 <> w2, next, grammar, input, forest, items, k, fit, lv, sp, nextEq, {==}))

# ======== CLASHES ========

# Two different choices at a choice point that both predict the same next token.
def Clash(+grammar: +List<Spec.Production>, +start: Nat) -> Type:
  &point: Spec.ChoicePoint -> &first: Nat -> &second: Nat -> &next: Maybe<&2, Nat> ->
    {Nat.is_eq(first, second) == False{} : Bool} & Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next) & Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)

# Two forests are the same, or there is a clash.
def Same(+grammar: +List<Spec.Production>, +start: Nat, +f1: +List<Spec.Tree>, +f2: +List<Spec.Tree>) -> Type:
  Either<{f1 == f2 : +List<Spec.Tree>}, Clash(grammar, start)>

law decide:
  for b: Bool
  for +c1: Nat
  for +c2: Nat
  for +bEq: {Nat.is_eq(c1, c2) == b : Bool}
  Either<{c1 == c2 : Nat}, {Nat.is_eq(c1, c2) == False{} : Bool}>

def decide(b, c1, c2, bEq):
  match b:
    case True{}:
      Inl{Lemma.nat_eq_sound(c1, c2, bEq)}
    case False{}:
      Inr{bEq}

# ---- A choice, in the form choiceOf gives it ----

law nt_cp:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +q: Nat
  for +next: Maybe<&2, Nat>
  for e: {b == True{} : Bool}
  for p: Spec.Predicts(grammar, start, Spec.rhsOf(grammar, q), q, [], next)
  Spec.ChoicePredicts(grammar, start, Spec.nonterminalAlternate(b, grammar, q), next)

def nt_cp(b, grammar, start, q, next, e, p):
  match b:
    case True{}:
      p
    case False{}:
      Empty.absurd(Spec.ChoicePredicts(grammar, start, None{}, next), Lemma.false_is_not_true(e))

law alt_cp:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +alts: +List<+List<Spec.Item>>
  for +c: Nat
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +mayBeEmpty: Bool
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for e: {b == True{} : Bool}
  for pw: Spec.predictsWhen(mayBeEmpty, grammar, start, Spec.altOf(alts, c), index, List.append(&2, Nat, prefix, [dot, c]), next)
  Spec.ChoicePredicts(grammar, start, Spec.bracketAlternate(b, alts, c, index, prefix, dot, mayBeEmpty, leave, rest), next)

def alt_cp(b, grammar, start, alts, c, index, prefix, dot, mayBeEmpty, leave, rest, next, e, pw):
  match b:
    case True{}:
      pw
    case False{}:
      Empty.absurd(Spec.ChoicePredicts(grammar, start, Spec.leaveChoice(Bool.and(Nat.is_eq(c, List.length(&2, +List<Spec.Item>, alts)), leave), rest, index, prefix), next), Lemma.false_is_not_true(e))

law leave_pick_cp:
  for l: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +next: Maybe<&2, Nat>
  for e: {l == True{} : Bool}
  for p: Spec.Predicts(grammar, start, rest, index, prefix, next)
  Spec.ChoicePredicts(grammar, start, Spec.leaveChoice(l, rest, index, prefix), next)

def leave_pick_cp(l, grammar, start, rest, index, prefix, next, e, p):
  match l:
    case True{}:
      p
    case False{}:
      Empty.absurd(Spec.ChoicePredicts(grammar, start, None{}, next), Lemma.false_is_not_true(e))

law leave_cp:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +mayBeEmpty: Bool
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for e: {b == False{} : Bool}
  for +leaveT: {leave == True{} : Bool}
  for p: Spec.Predicts(grammar, start, rest, index, prefix, next)
  Spec.ChoicePredicts(grammar, start, Spec.bracketAlternate(b, alts, List.length(&2, +List<Spec.Item>, alts), index, prefix, dot, mayBeEmpty, leave, rest), next)

def leave_cp(b, grammar, start, alts, index, prefix, dot, mayBeEmpty, leave, rest, next, e, leaveT, p):
  match b:
    case False{}:
      +n = List.length(&2, +List<Spec.Item>, alts)
      leave_pick_cp(Bool.and(Nat.is_eq(n, n), leave), grammar, start, rest, index, prefix, next, Lemma.and_true_intro(Nat.is_eq(n, n), leave, Lemma.nat_eq_refl(n), leaveT), p)
    case True{}:
      Empty.absurd(Spec.ChoicePredicts(grammar, start, Some{Spec.Choice{Spec.altOf(alts, List.length(&2, +List<Spec.Item>, alts)), index, List.append(&2, Nat, prefix, [dot, List.length(&2, +List<Spec.Item>, alts)]), mayBeEmpty}}, next), Lemma.true_is_not_false(e))

# The same choice, at the bracket of the sequence named by the prefix.
law bracket_cp:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +index: Nat
  for +p: +List<Nat>
  for +dot: Nat
  for +c: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)) == rest : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(Some{Spec.Brack{kind, alts}}, False{}, c, index, p, dot, rest), next)
  Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.BracketAt{index, p, dot}, c), next)

def bracket_cp(grammar, start, index, p, dot, c, kind, alts, rest, next, itAt, restAt, cp):
  +seq = Spec.sequenceAt(grammar, index, p)
  +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(seq, dot), Some{Spec.Brack{kind, alts}}, itAt)
  +restS = Equal.sym(+List<Spec.Item>, Spec.itemsFrom(1n+dot, seq), rest, restAt)
  %itS : Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(_, False{}, c, index, p, dot, Spec.itemsFrom(1n+dot, seq)), next)
  %restS : Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(Some{Spec.Brack{kind, alts}}, False{}, c, index, p, dot, _), next)
  cp

# After a round of < >.
law after_cp:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +index: Nat
  for +p: +List<Nat>
  for +dot: Nat
  for +c: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)) == rest : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(Some{Spec.Brack{kind, alts}}, True{}, c, index, p, dot, rest), next)
  Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.AfterRoundAt{index, p, dot}, c), next)

def after_cp(grammar, start, index, p, dot, c, kind, alts, rest, next, itAt, restAt, cp):
  +seq = Spec.sequenceAt(grammar, index, p)
  +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(seq, dot), Some{Spec.Brack{kind, alts}}, itAt)
  +restS = Equal.sym(+List<Spec.Item>, Spec.itemsFrom(1n+dot, seq), rest, restAt)
  %itS : Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(_, True{}, c, index, p, dot, Spec.itemsFrom(1n+dot, seq)), next)
  %restS : Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(Some{Spec.Brack{kind, alts}}, True{}, c, index, p, dot, _), next)
  cp

# ======== FACTS FOR THE COMPARISON ========

law consumes_child:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for e: {Spec.consumes(Spec.Pick{a, ch}) == True{} : Bool}
  {Bool.not(List.is_empty(&2, Nat, Spec.leaves(ch))) == True{} : Bool}

def consumes_child(a, ch, e):
  Equal.trans(Bool, Bool.not(List.is_empty(&2, Nat, Spec.leaves(ch))), Bool.not(List.is_empty(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), []))), True{},
    Equal.cong(+List<Nat>, Bool, v => Bool.not(List.is_empty(&2, Nat, v)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch)))), e)

law closure_consume:
  for rs: +List<Spec.Tree>
  for e: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  {Spec.allConsume(rs) == True{} : Bool}

def closure_consume(rs, e):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rr}:
      Lemma.or_false_right(Spec.allConsume(r <> rr), e)

law optional_consume:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for e: {Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]) == True{} : Bool}
  {Bool.not(List.is_empty(&2, Nat, Spec.leaves(ch))) == True{} : Bool}

def optional_consume(a, ch, e):
  +p = {Spec.Pick{a, ch} : Spec.Tree}
  consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(p), True{}, Lemma.or_false_right(Bool.and(Spec.consumes(p), True{}), e)))

law positive_rest:
  for +r: Spec.Tree
  for rr: +List<Spec.Tree>
  for e: {Spec.roundsOk(Spec.Positive{}, r <> rr) == True{} : Bool}
  {Spec.allConsume(rr) == True{} : Bool}

def positive_rest(r, rr, e):
  match rr:
    case Nil{}:
      {==}
    case Con{+r2, +rr2}:
      Lemma.and_true_right_side(Spec.consumes(r), Spec.allConsume(r2 <> rr2), Lemma.or_false_right(Spec.allConsume(r <> (r2 <> rr2)), e))

law lt_ne:
  for a: Nat
  for n: Nat
  for h: {Nat.is_lt(a, n) == True{} : Bool}
  {Nat.is_eq(a, n) == False{} : Bool}

def lt_ne(a, n, h):
  match a n:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, Lemma.lt_zero_false(a, h))
    case 0n 1n+m:
      {==}
    case 1n+b 1n+m:
      lt_ne(b, m, h)

law all_in_cons:
  for xs: +List<Spec.Bsr>
  for +x: Spec.Bsr
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(xs, set) == True{} : Bool}
  {Spec.allIn(xs, x <> set) == True{} : Bool}

def all_in_cons(xs, x, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(y, x <> set), Spec.allIn(rest, x <> set),
        R.bsr_member_cons(y, x, set, Lemma.and_true_left(Spec.bsrMember(y, set), Spec.allIn(rest, set), h)),
        all_in_cons(rest, x, set, Lemma.and_true_right_side(Spec.bsrMember(y, set), Spec.allIn(rest, set), h)))

law all_in_refl:
  for xs: +List<Spec.Bsr>
  {Spec.allIn(xs, xs) == True{} : Bool}

def all_in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Spec.bsrMember(x, x <> rest), Spec.allIn(rest, x <> rest), R.bsr_member_head(x, rest), all_in_cons(rest, x, rest, all_in_refl(rest)))

# The sequence of an alternative of the bracket at the dot.
law seq_child:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  {Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])) == Spec.altOf(alts, a) : +List<Spec.Item>}

def seq_child(grammar, index, prefix, dot, a, kind, alts, even, itAt):
  Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])), Spec.bracketAlternative(Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), a), Spec.altOf(alts, a),
    L.sequence_snoc(prefix, dot, a, Spec.rhsOf(grammar, index), even),
    Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Spec.bracketAlternative(v, a), Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{kind, alts}}, itAt))

# PREDICT for a part of a tree, from the end step of its sequence in some walk inside the
# tree. The walk may name the prefix differently (prefixW: a loop's rounds add the dot and
# the alternative one at a time).
law predicts_in:
  for next: Maybe<&2, Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +forest: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +prefixW: +List<Nat>
  for +k: Nat
  for +i2: Nat
  for +fin: Nat
  for +ws: +List<Spec.Bsr>
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +sp: G.Spells(forest, input, k)
  for +nextEq: {List.get(&2, Nat, input, k) == next : Maybe<&2, Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +pe: {prefixW == prefix : +List<Nat>}
  for ends: EndAt(grammar, index, prefixW, i2, fin, ws)
  for +inW: {Spec.allIn(ws, Spec.steps(root, 0n)) == True{} : Bool}
  Spec.Predicts(grammar, start, items, index, prefix, next)

def predicts_in(next, grammar, start, input, root, rootFit, rootSp, forest, items, index, prefix, prefixW, k, i2, fin, ws, fit, sp, nextEq, finEq, pe, ends, inW):
  match ends:
    case (K0, m):
      +K = {K0 : Nat}
      +inRoot = G.ebnf_all_in_member(ws, Spec.steps(root, 0n), Spec.at(index, prefixW, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefixW)), i2, K, fin), inW, m)
      +moved = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i2, K, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest)))), Spec.steps(root, 0n)),
        Spec.bsrMember(Spec.at(index, prefixW, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefixW)), i2, K, fin), Spec.steps(root, 0n)), True{},
        Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i2, K, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest)))), Spec.steps(root, 0n)),
          Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i2, K, fin), Spec.steps(root, 0n)),
          Spec.bsrMember(Spec.at(index, prefixW, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefixW)), i2, K, fin), Spec.steps(root, 0n)),
          Equal.cong(Nat, Bool, w => Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i2, K, w), Spec.steps(root, 0n)), Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))), fin, finEq),
          Equal.cong(+List<Nat>, Bool, v => Spec.bsrMember(Spec.at(index, v, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, v)), i2, K, fin), Spec.steps(root, 0n)), prefix, prefixW, Equal.sym(+List<Nat>, prefixW, prefix, pe))),
        inRoot)
      predicts_from(Spec.leaves(forest), next, grammar, start, input, root, rootFit, rootSp, forest, items, index, prefix, k, i2, K, fit, {==}, sp, nextEq, moved)

# ======== COMBINING COMPARISONS ========

law then_same:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -t1: +List<Spec.Tree>
  for -t2: +List<Spec.Tree>
  for -F1: +List<Spec.Tree>
  for -F2: +List<Spec.Tree>
  for r: Same(grammar, start, t1, t2)
  for mk: {t1 == t2 : +List<Spec.Tree>} -> {F1 == F2 : +List<Spec.Tree>}
  Same(grammar, start, F1, F2)

def then_same(grammar, start, t1, t2, F1, F2, r, mk):
  match r:
    case Inl{e}:
      Inl{mk(e)}
    case Inr{c}:
      Inr{c}

law both_same:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -c1: +List<Spec.Tree>
  for -c2: +List<Spec.Tree>
  for -t1: +List<Spec.Tree>
  for -t2: +List<Spec.Tree>
  for -F1: +List<Spec.Tree>
  for -F2: +List<Spec.Tree>
  for r: Same(grammar, start, c1, c2)
  for next: {c1 == c2 : +List<Spec.Tree>} -> Same(grammar, start, t1, t2)
  for mk: {c1 == c2 : +List<Spec.Tree>} -> {t1 == t2 : +List<Spec.Tree>} -> {F1 == F2 : +List<Spec.Tree>}
  Same(grammar, start, F1, F2)

def both_same(grammar, start, c1, c2, t1, t2, F1, F2, r, next, mk):
  match r:
    case Inl{e0}:
      +e = {e0 : {c1 == c2 : +List<Spec.Tree>}}
      then_same(grammar, start, t1, t2, F1, F2, next(e), mk(e))
    case Inr{c}:
      Inr{c}

# ======== THE COMPARISON ========

# How the rounds of a loop must consume: all of them, except the first round of < >.
def roundsFine(kind: Spec.Bracket, after: Bool, +rounds: +List<Spec.Tree>) -> Bool:
  match kind after:
    case Spec.Positive{} False{}:
      Spec.roundsOk(Spec.Positive{}, rounds)
    case _ _:
      Spec.allConsume(rounds)

# What the comparison knows of the two forests. In a sequence: both fit the items from the
# dot, spell the input from k, and walk inside their root's steps. In the rounds of a loop
# (the bracket at the dot): both are rounds of its body from k, consume as they must, end
# at E1 and E2, and leaving the loop there predicts the token there.
def CmpReady(rounds: Bool, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root1: Spec.Tree, +root2: Spec.Tree, +f1: +List<Spec.Tree>, +f2: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i1: Nat, +i2: Nat, +k: Nat, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +restO: +List<Spec.Item>, +after: Bool, +E1: Nat, +E2: Nat) -> Type:
  match rounds:
    case False{}:
      {Spec.fits(f1, grammar, items) == True{} : Bool} & {Spec.fits(f2, grammar, items) == True{} : Bool} & G.Spells(f1, input, k) & G.Spells(f2, input, k) &
        {Spec.allIn(Spec.walk(f1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool} & {Spec.allIn(Spec.walk(f2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool} &
        {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == items : +List<Spec.Item>} & {L.evenLength(prefix) == True{} : Bool}
    case True{}:
      {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>} &
        {Gll.isLoop(kind) == True{} : Bool} & {L.evenLength(prefix) == True{} : Bool} &
        {Spec.fits(f1, grammar, Spec.times(List.length(&2, Spec.Tree, f1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.fits(f2, grammar, Spec.times(List.length(&2, Spec.Tree, f2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} &
        {roundsFine(kind, after, f1) == True{} : Bool} & {roundsFine(kind, after, f2) == True{} : Bool} &
        G.Spells(f1, input, k) & G.Spells(f2, input, k) &
        {Spec.allIn(Spec.walk(f1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool} & {Spec.allIn(Spec.walk(f2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool} &
        {Nat.add(k, List.length(&2, Nat, Spec.leaves(f1))) == E1 : Nat} & {Nat.add(k, List.length(&2, Nat, Spec.leaves(f2))) == E2 : Nat} &
        Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1)) & Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))

def CmpIH(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root1: Spec.Tree, +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}, +root2: Spec.Tree, +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}, +f1: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @f2: +List<Spec.Tree> -> @items: +List<Spec.Item> -> @index: Nat -> @prefix: +List<Nat> -> @dot: Nat -> @i1: Nat -> @i2: Nat -> @k: Nat -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @restO: +List<Spec.Item> -> @after: Bool -> @E1: Nat -> @E2: Nat ->
    CmpReady(rounds, grammar, start, input, root1, root2, f1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2) -> Same(grammar, start, f1, f2)

# Two tokens: the same token, then the rest.
law leaf_leaf:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ts1: +List<Spec.Tree>
  for +a2: Nat
  for +ts2: +List<Spec.Tree>
  for +term: Nat
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Leaf{a1} <> ts1, grammar, Spec.Sym{Spec.Terminal{term}} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Leaf{a2} <> ts2, grammar, Spec.Sym{Spec.Terminal{term}} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Leaf{a1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Leaf{a2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Leaf{a1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Leaf{a2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Sym{Spec.Terminal{term}} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2)

def leaf_leaf(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ts1, a2, ts2, term, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihTs):
  +tok1 = G.leaf_token(input, k, a1, Spec.leaves(ts1), sp1)
  +tok2 = G.leaf_token(input, k, a2, Spec.leaves(ts2), sp2)
  +ae = Lemma.some_injective(a1, a2, Equal.trans(Maybe<&2, Nat>, Some{a1}, List.get(&2, Nat, input, k), Some{a2}, Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, input, k), Some{a1}, tok1), tok2))
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Sym{Spec.Terminal{term}}, restI, itemsEq)
  then_same(grammar, start, ts1, ts2, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2,
    ihTs(False{}, ts2, restI, index, prefix, 1n+dot, i1, i2, 1n+k, kind, alts, restO, after, E1, E2, (Fits.fits_tail(Spec.Leaf{a1}, ts1, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit1), (Fits.fits_tail(Spec.Leaf{a2}, ts2, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit2), (G.leaf_rest(input, k, a1, Spec.leaves(ts1), sp1), (G.leaf_rest(input, k, a2, Spec.leaves(ts2), sp2), (all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, 1n+k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, 1n+k), Spec.steps(root1, 0n), in1), (all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, 1n+k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, 1n+k), Spec.steps(root2, 0n), in2), (itT, even)))))))),
    tse => Equal.trans(+List<Spec.Tree>, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts1, Spec.Leaf{a2} <> ts2, Equal.cong(Nat, +List<Spec.Tree>, v => Spec.Leaf{v} <> ts1, a1, a2, ae), Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Leaf{a2} <> v, ts1, ts2, tse)))


# Two skips (of [ ] or of an empty item): the rest.
law skip_skip:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +it: Spec.Item
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Skip{} <> ts1, grammar, it <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Skip{} <> ts2, grammar, it <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Skip{} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Skip{} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == it <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2)

def skip_skip(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, it, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, fT1, fT2, ihTs):
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
  then_same(grammar, start, ts1, ts2, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2,
    ihTs(False{}, ts2, restI, index, prefix, 1n+dot, i1, i2, k, kind, alts, restO, after, E1, E2, (fT1, (fT2, (sp1, (sp2, (all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, k), Spec.steps(root1, 0n), in1), (all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, k), Spec.steps(root2, 0n), in2), (itT, even)))))))),
    tse => Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Skip{} <> v, ts1, ts2, tse))

# ---- Shared steps ----

law make_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -F1: +List<Spec.Tree>
  for -F2: +List<Spec.Tree>
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  Same(grammar, start, F1, F2)

def make_clash(grammar, start, F1, F2, point, first, second, next, neq, cp1, cp2):
  Inr{(point, (first, (second, (next, (neq, (cp1, cp2))))))}

# After equal first trees: the rest of both sequences, from the same position.
law seq_tail:
  for +c1: +List<Spec.Tree>
  for +c2: +List<Spec.Tree>
  for +ce: {c1 == c2 : +List<Spec.Tree>}
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +restI: +List<Spec.Item>
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for +spT1: G.Spells(ts1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(c1))))
  for +spT2: G.Spells(ts2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(c2))))
  for +inT1: {Spec.allIn(Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(c1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inT2: {Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(c2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itT: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, ts1, ts2)

def seq_tail(c1, c2, ce, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(c1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(c2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), c2, c1, Equal.sym(+List<Spec.Tree>, c1, c2, ce))
  +lt2 = List.length(&2, Nat, Spec.leaves(ts2))
  +spT2b = Equal.trans(+List<Nat>, Spec.leaves(ts2), Lemma.slice(input, e2, lt2), Lemma.slice(input, e1, lt2), spT2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lt2), e2, e1, eE))
  +inT2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inT2)
  ihTs(False{}, ts2, restI, index, prefix, 1n+dot, i1, i2, e1, kind, alts, restO, after, E1, E2, (fT1, (fT2, (spT1, (spT2b, (inT1, (inT2b, (itT, even))))))))

law node_eq:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +qe: {q1 == q2 : Nat}
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Node{q1, ch1} <> ts1 == Spec.Node{q2, ch2} <> ts2 : +List<Spec.Tree>}

def node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, che, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2, Equal.cong(Nat, +List<Spec.Tree>, v => Spec.Node{v, ch1} <> ts1, q1, q2, qe),
    Equal.trans(+List<Spec.Tree>, Spec.Node{q2, ch1} <> ts1, Spec.Node{q2, ch2} <> ts1, Spec.Node{q2, ch2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Node{q2, v} <> ts1, ch1, ch2, che),
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Node{q2, ch2} <> v, ts1, ts2, tse)))

law pick_eq:
  for +a1: Nat
  for +a2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +ae: {a1 == a2 : Nat}
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Pick{a1, ch1} <> ts1 == Spec.Pick{a2, ch2} <> ts2 : +List<Spec.Tree>}

def pick_eq(a1, a2, ch1, ch2, ts1, ts2, ae, che, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2, Equal.cong(Nat, +List<Spec.Tree>, v => Spec.Pick{v, ch1} <> ts1, a1, a2, ae),
    Equal.trans(+List<Spec.Tree>, Spec.Pick{a2, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts1, Spec.Pick{a2, ch2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Pick{a2, v} <> ts1, ch1, ch2, che),
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Pick{a2, ch2} <> v, ts1, ts2, tse)))

law loop_eq:
  for +rs1: +List<Spec.Tree>
  for +rs2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +rse: {rs1 == rs2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Loop{rs1} <> ts1 == Spec.Loop{rs2} <> ts2 : +List<Spec.Tree>}

def loop_eq(rs1, rs2, ts1, ts2, rse, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts1, Spec.Loop{rs2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Loop{v} <> ts1, rs1, rs2, rse),
    Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Loop{rs2} <> v, ts1, ts2, tse))

law node_same:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +fC1: {Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, q1, [], 0n, k, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +restI: +List<Spec.Item>
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for +spT1: G.Spells(ts1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spT2: G.Spells(ts2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inT1: {Spec.allIn(Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inT2: {Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itT: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2)

def node_same(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, q2, qe, ch1, ch2, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs):
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, q1, [], 0n, k, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.steps(root2, 0n)), True{}, Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, v, [], 0n, k, k), Spec.steps(root2, 0n)), q1, q2, qe), inC2)
  both_same(grammar, start, ch1, ch2, ts1, ts2, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2,
    ihCh(False{}, ch2, Spec.rhsOf(grammar, q1), q1, [], 0n, k, k, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, ({==}, {==})))))))),
    che => seq_tail(ch1, ch2, che, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs),
    che => tse => node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, che, tse))

# Two nodes: the same alternate, else a clash.
law node_node:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +q1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +q2: Nat
  for +ch2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +x: Nat
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Node{q1, ch1} <> ts1, grammar, Spec.Sym{Spec.Nonterminal{x}} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Node{q2, ch2} <> ts2, grammar, Spec.Sym{Spec.Nonterminal{x}} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Node{q1, ch1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Node{q2, ch2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Node{q1, ch1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Node{q2, ch2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Sym{Spec.Nonterminal{x}} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2)

def node_node(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, ch1, ts1, q2, ch2, ts2, x, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs):
  +h1 = Bool.and(Spec.lhsIs(grammar, q1, x), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)))
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(ts1, grammar, restI), fit1)
  +lhs1 = Lemma.and_true_left(Spec.lhsIs(grammar, q1, x), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q1, x), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
  +fT1 = Lemma.and_true_right_side(h1, Spec.fits(ts1, grammar, restI), fit1)
  +lc1 = Spec.leaves(ch1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lc1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch1, False{}, q1, [], 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inC1 = all_in_left(Spec.walk(ch1, False{}, q1, [], 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(ch1, False{}, q1, [], 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +h2 = Bool.and(Spec.lhsIs(grammar, q2, x), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)))
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(ts2, grammar, restI), fit2)
  +lhs2 = Lemma.and_true_left(Spec.lhsIs(grammar, q2, x), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q2, x), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
  +fT2 = Lemma.and_true_right_side(h2, Spec.fits(ts2, grammar, restI), fit2)
  +lc2 = Spec.leaves(ch2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lc2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inC2 = all_in_left(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Sym{Spec.Nonterminal{x}}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  cp1 = nt_cp(Spec.lhsIs(grammar, q1, x), grammar, start, q1, next, lhs1,
    predicts_in(next, grammar, start, input, root1, rootFit1, rootSp1, ch1, Spec.rhsOf(grammar, q1), q1, [], [], k, k, e1, Spec.walk(ch1, False{}, q1, [], 0n, k, k), fC1, spC1, {==}, {==}, {==},
      end_walk(ch1, Spec.rhsOf(grammar, q1), 0n, grammar, q1, [], k, k, e1, fC1, {==}, {==}, {==}), inC1))
  cp2 = nt_cp(Spec.lhsIs(grammar, q2, x), grammar, start, q2, next, lhs2,
    predicts_in(next, grammar, start, input, root2, rootFit2, rootSp2, ch2, Spec.rhsOf(grammar, q2), q2, [], [], k, k, e2, Spec.walk(ch2, False{}, q2, [], 0n, k, k), fC2, spC2, {==}, {==}, {==},
      end_walk(ch2, Spec.rhsOf(grammar, q2), 0n, grammar, q2, [], k, k, e2, fC2, {==}, {==}, {==}), inC2))
  L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), decide(Nat.is_eq(q1, q2), q1, q2, {==}),
    qe => node_same(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, q2, qe, ch1, ch2, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs),
    neq => make_clash(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2, Spec.NonterminalAt{x}, q1, q2, next, neq, cp1, cp2))

law pick_same:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +bk: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{bk, balts}} : Maybe<&2, Spec.Item>}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(balts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(balts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +restI: +List<Spec.Item>
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for +spT1: G.Spells(ts1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spT2: G.Spells(ts2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inT1: {Spec.allIn(Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inT2: {Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itT: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2)

def pick_same(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, bk, balts, a1, a2, ae, ch1, ch2, itAt, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs):
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(balts, a1)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(balts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, v]), 0n, k, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +cEq = seq_child(grammar, index, prefix, dot, a1, bk, balts, even, itAt)
  +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even)
  both_same(grammar, start, ch1, ch2, ts1, ts2, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2,
    ihCh(False{}, ch2, Spec.altOf(balts, a1), index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq, evenC)))))))),
    che => seq_tail(ch1, ch2, che, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs),
    che => tse => pick_eq(a1, a2, ch1, ch2, ts1, ts2, ae, che, tse))

# Two alternatives of Spec.Group{}: the same one, else a clash.
law group_group:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Pick{a1, ch1} <> ts1, grammar, Spec.Brack{Spec.Group{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Pick{a2, ch2} <> ts2, grammar, Spec.Brack{Spec.Group{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Group{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2)

def group_group(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs):
  +h1 = Bool.and(Spec.isAlt(balts, a1), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)))
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(ts1, grammar, restI), fit1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(balts, a1), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(balts, a1), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +fT1 = Lemma.and_true_right_side(h1, Spec.fits(ts1, grammar, restI), fit1)
  +lc1 = Spec.leaves(ch1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lc1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inC1 = all_in_left(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +h2 = Bool.and(Spec.isAlt(balts, a2), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)))
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(ts2, grammar, restI), fit2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(balts, a2), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(balts, a2), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +fT2 = Lemma.and_true_right_side(h2, Spec.fits(ts2, grammar, restI), fit2)
  +lc2 = Spec.leaves(ch2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lc2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inC2 = all_in_left(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Group{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Group{}, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  cp1 = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Group{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a1), grammar, start, balts, a1, index, prefix, dot, True{}, False{}, restI, next, isA1,
        predicts_in(next, grammar, start, input, root1, rootFit1, rootSp1, ch1, Spec.altOf(balts, a1), index, List.append(&2, Nat, prefix, [dot, a1]), List.append(&2, Nat, prefix, [dot, a1]), k, k, e1, Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), fC1, spC1, {==}, {==}, {==},
        end_walk(ch1, Spec.altOf(balts, a1), 0n, grammar, index, List.append(&2, Nat, prefix, [dot, a1]), k, k, e1, fC1, seq_child(grammar, index, prefix, dot, a1, Spec.Group{}, balts, even, itAt), {==}, {==}), inC1)))
  cp2 = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Group{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a2), grammar, start, balts, a2, index, prefix, dot, True{}, False{}, restI, next, isA2,
        predicts_in(next, grammar, start, input, root2, rootFit2, rootSp2, ch2, Spec.altOf(balts, a2), index, List.append(&2, Nat, prefix, [dot, a2]), List.append(&2, Nat, prefix, [dot, a2]), k, k, e2, Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), fC2, spC2, {==}, {==}, {==},
        end_walk(ch2, Spec.altOf(balts, a2), 0n, grammar, index, List.append(&2, Nat, prefix, [dot, a2]), k, k, e2, fC2, seq_child(grammar, index, prefix, dot, a2, Spec.Group{}, balts, even, itAt), {==}, {==}), inC2)))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => pick_same(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, Spec.Group{}, balts, a1, a2, ae, ch1, ch2, itAt, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# Two alternatives of Spec.Optional{}: the same one, else a clash.
law optional_optional:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Pick{a1, ch1} <> ts1, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Pick{a2, ch2} <> ts2, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Optional{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2)

def optional_optional(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs):
  +okR1 = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a1, ch1}])
  +h1 = Bool.and(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)))
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(ts1, grammar, restI), fit1)
  +h21 = Lemma.and_true_left(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +reads1 = optional_consume(a1, ch1, Lemma.and_true_left(okR1, Spec.isAlt(balts, a1), h21))
  +isA1 = Lemma.and_true_right_side(okR1, Spec.isAlt(balts, a1), h21)
  +fC1 = Lemma.and_true_right_side(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +fT1 = Lemma.and_true_right_side(h1, Spec.fits(ts1, grammar, restI), fit1)
  +lc1 = Spec.leaves(ch1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lc1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inC1 = all_in_left(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +okR2 = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a2, ch2}])
  +h2 = Bool.and(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)))
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(ts2, grammar, restI), fit2)
  +h22 = Lemma.and_true_left(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +reads2 = optional_consume(a2, ch2, Lemma.and_true_left(okR2, Spec.isAlt(balts, a2), h22))
  +isA2 = Lemma.and_true_right_side(okR2, Spec.isAlt(balts, a2), h22)
  +fC2 = Lemma.and_true_right_side(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +fT2 = Lemma.and_true_right_side(h2, Spec.fits(ts2, grammar, restI), fit2)
  +lc2 = Spec.leaves(ch2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lc2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inC2 = all_in_left(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  cp1 = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Optional{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a1), grammar, start, balts, a1, index, prefix, dot, False{}, True{}, restI, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(balts, a1), k, fC1, {==}, spC1, {==}, reads1)))
  cp2 = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Optional{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a2), grammar, start, balts, a2, index, prefix, dot, False{}, True{}, restI, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(balts, a2), k, fC2, {==}, spC2, {==}, reads2)))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => pick_same(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, Spec.Optional{}, balts, a1, a2, ae, ch1, ch2, itAt, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# [ ] taken by one tree and skipped by the other: a clash.
law optional_skip:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Pick{a1, ch1} <> ts1, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Skip{} <> ts2, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Skip{} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Optional{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2)

def optional_skip(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even):
  +okR1 = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a1, ch1}])
  +h1 = Bool.and(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)))
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(ts1, grammar, restI), fit1)
  +h21 = Lemma.and_true_left(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +reads1 = optional_consume(a1, ch1, Lemma.and_true_left(okR1, Spec.isAlt(balts, a1), h21))
  +isA1 = Lemma.and_true_right_side(okR1, Spec.isAlt(balts, a1), h21)
  +fC1 = Lemma.and_true_right_side(Bool.and(okR1, Spec.isAlt(balts, a1)), Spec.fits(ch1, grammar, Spec.altOf(balts, a1)), hOk1)
  +fT1 = Lemma.and_true_right_side(h1, Spec.fits(ts1, grammar, restI), fit1)
  +lc1 = Spec.leaves(ch1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lc1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inC1 = all_in_left(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(ch1, False{}, index, List.append(&2, Nat, prefix, [dot, a1]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  +n = List.length(&2, +List<Spec.Item>, balts)
  cpA = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Optional{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a1), grammar, start, balts, a1, index, prefix, dot, False{}, True{}, restI, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(balts, a1), k, fC1, {==}, spC1, {==}, reads1)))
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, balts), Spec.Optional{}, balts, restI, next, itAt, itT,
      leave_cp(Spec.isAlt(balts, List.length(&2, +List<Spec.Item>, balts)), grammar, start, balts, index, prefix, dot, False{}, True{}, restI, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, balts)), {==},
        predicts_in(next, grammar, start, input, root2, rootFit2, rootSp2, ts2, restI, index, prefix, prefix, k, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts2))), Spec.walk(Spec.Skip{} <> ts2, False{}, index, prefix, dot, i2, k), fit2, sp2, {==}, {==}, {==},
          end_walk(Spec.Skip{} <> ts2, Spec.Brack{Spec.Optional{}, balts} <> restI, dot, grammar, index, prefix, i2, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts2))), fit2, itemsEq, {==}, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Skip{} <> ts2)), {==})), in2)))
  make_clash(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2, Spec.BracketAt{index, prefix, dot}, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)


# [ ] taken by one tree and skipped by the other: a clash.
law skip_optional:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +ts1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Skip{} <> ts1, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Pick{a2, ch2} <> ts2, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Skip{} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Optional{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2)

def skip_optional(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even):
  +okR2 = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a2, ch2}])
  +h2 = Bool.and(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)))
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(ts2, grammar, restI), fit2)
  +h22 = Lemma.and_true_left(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +reads2 = optional_consume(a2, ch2, Lemma.and_true_left(okR2, Spec.isAlt(balts, a2), h22))
  +isA2 = Lemma.and_true_right_side(okR2, Spec.isAlt(balts, a2), h22)
  +fC2 = Lemma.and_true_right_side(Bool.and(okR2, Spec.isAlt(balts, a2)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), hOk2)
  +fT2 = Lemma.and_true_right_side(h2, Spec.fits(ts2, grammar, restI), fit2)
  +lc2 = Spec.leaves(ch2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lc2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inC2 = all_in_left(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, a2]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  +n = List.length(&2, +List<Spec.Item>, balts)
  cpA = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Optional{}, balts, restI, next, itAt, itT,
      alt_cp(Spec.isAlt(balts, a2), grammar, start, balts, a2, index, prefix, dot, False{}, True{}, restI, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(balts, a2), k, fC2, {==}, spC2, {==}, reads2)))
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, balts), Spec.Optional{}, balts, restI, next, itAt, itT,
      leave_cp(Spec.isAlt(balts, List.length(&2, +List<Spec.Item>, balts)), grammar, start, balts, index, prefix, dot, False{}, True{}, restI, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, balts)), {==},
        predicts_in(next, grammar, start, input, root1, rootFit1, rootSp1, ts1, restI, index, prefix, prefix, k, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts1))), Spec.walk(Spec.Skip{} <> ts1, False{}, index, prefix, dot, i1, k), fit1, sp1, {==}, {==}, {==},
          end_walk(Spec.Skip{} <> ts1, Spec.Brack{Spec.Optional{}, balts} <> restI, dot, grammar, index, prefix, i1, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts1))), fit1, itemsEq, {==}, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Skip{} <> ts1)), {==})), in1)))
  make_clash(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2, Spec.BracketAt{index, prefix, dot}, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)

# Two loops: the same rounds, then the rest.
law closure_closure:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +rs1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +rs2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Loop{rs1} <> ts1, grammar, Spec.Brack{Spec.Closure{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Loop{rs2} <> ts2, grammar, Spec.Brack{Spec.Closure{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Loop{rs1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Loop{rs2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Loop{rs1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Loop{rs2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Closure{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihRs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, rs1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2)

def closure_closure(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, rs2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihRs, ihTs):
  +okR1 = Spec.roundsOk(Spec.Closure{}, rs1)
  +tm1 = Spec.times(List.length(&2, Spec.Tree, rs1), Spec.Brack{Spec.Group{}, balts})
  +hOk1 = Lemma.and_true_left(Bool.and(okR1, Spec.fits(rs1, grammar, tm1)), Spec.fits(ts1, grammar, restI), fit1)
  +fR1 = Lemma.and_true_right_side(okR1, Spec.fits(rs1, grammar, tm1), hOk1)
  +fT1 = Lemma.and_true_right_side(Bool.and(okR1, Spec.fits(rs1, grammar, tm1)), Spec.fits(ts1, grammar, restI), fit1)
  +lr1 = Spec.leaves(rs1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lr1))
  +spR1 = G.spells_first(input, k, lr1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lr1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inR1 = all_in_left(Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +fine1 = closure_consume(rs1, Lemma.and_true_left(okR1, Spec.fits(rs1, grammar, tm1), hOk1))
  LP1 = predicts_in(List.get(&2, Nat, input, e1), grammar, start, input, root1, rootFit1, rootSp1, ts1, restI, index, prefix, prefix, e1, i1, Nat.add(e1, List.length(&2, Nat, lt1)), Spec.walk(Spec.Loop{rs1} <> ts1, False{}, index, prefix, dot, i1, k), fT1, spT1, {==}, {==}, {==},
    end_walk(Spec.Loop{rs1} <> ts1, Spec.Brack{Spec.Closure{}, balts} <> restI, dot, grammar, index, prefix, i1, k, Nat.add(e1, List.length(&2, Nat, lt1)), fit1, itemsEq,
      Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lt1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr1, lt1))), G.end_split(k, lr1, lt1)),
      Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs1} <> ts1)), {==})), in1)
  +okR2 = Spec.roundsOk(Spec.Closure{}, rs2)
  +tm2 = Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})
  +hOk2 = Lemma.and_true_left(Bool.and(okR2, Spec.fits(rs2, grammar, tm2)), Spec.fits(ts2, grammar, restI), fit2)
  +fR2 = Lemma.and_true_right_side(okR2, Spec.fits(rs2, grammar, tm2), hOk2)
  +fT2 = Lemma.and_true_right_side(Bool.and(okR2, Spec.fits(rs2, grammar, tm2)), Spec.fits(ts2, grammar, restI), fit2)
  +lr2 = Spec.leaves(rs2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lr2))
  +spR2 = G.spells_first(input, k, lr2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lr2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inR2 = all_in_left(Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +fine2 = closure_consume(rs2, Lemma.and_true_left(okR2, Spec.fits(rs2, grammar, tm2), hOk2))
  LP2 = predicts_in(List.get(&2, Nat, input, e2), grammar, start, input, root2, rootFit2, rootSp2, ts2, restI, index, prefix, prefix, e2, i2, Nat.add(e2, List.length(&2, Nat, lt2)), Spec.walk(Spec.Loop{rs2} <> ts2, False{}, index, prefix, dot, i2, k), fT2, spT2, {==}, {==}, {==},
    end_walk(Spec.Loop{rs2} <> ts2, Spec.Brack{Spec.Closure{}, balts} <> restI, dot, grammar, index, prefix, i2, k, Nat.add(e2, List.length(&2, Nat, lt2)), fit2, itemsEq,
      Equal.sym(Nat, Nat.add(e2, List.length(&2, Nat, lt2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr2, lt2))), G.end_split(k, lr2, lt2)),
      Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs2} <> ts2)), {==})), in2)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Closure{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Closure{}, balts}, restI, itemsEq)
  both_same(grammar, start, rs1, rs2, ts1, ts2, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2,
    ihRs(True{}, rs2, [], index, prefix, dot, k, k, k, Spec.Closure{}, balts, restI, False{}, e1, e2, (itAt, (itT, ({==}, (even, (fR1, (fR2, (fine1, (fine2, (spR1, (spR2, (inR1, (inR2, ({==}, ({==}, (LP1, LP2)))))))))))))))),
    rse => seq_tail(rs1, rs2, rse, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs),
    rse => tse => loop_eq(rs1, rs2, ts1, ts2, rse, tse))


# Two loops: the same rounds, then the rest.
law positive_positive:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +rs1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +rs2: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +balts: +List<+List<Spec.Item>>
  for +restI: +List<Spec.Item>
  for +fit1: {Spec.fits(Spec.Loop{rs1} <> ts1, grammar, Spec.Brack{Spec.Positive{}, balts} <> restI) == True{} : Bool}
  for +fit2: {Spec.fits(Spec.Loop{rs2} <> ts2, grammar, Spec.Brack{Spec.Positive{}, balts} <> restI) == True{} : Bool}
  for +sp1: G.Spells(Spec.Loop{rs1} <> ts1, input, k)
  for +sp2: G.Spells(Spec.Loop{rs2} <> ts2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Loop{rs1} <> ts1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Loop{rs2} <> ts2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Positive{}, balts} <> restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for ihRs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, rs1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2)

def positive_positive(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, rs2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihRs, ihTs):
  +okR1 = Spec.roundsOk(Spec.Positive{}, rs1)
  +tm1 = Spec.times(List.length(&2, Spec.Tree, rs1), Spec.Brack{Spec.Group{}, balts})
  +hOk1 = Lemma.and_true_left(Bool.and(okR1, Spec.fits(rs1, grammar, tm1)), Spec.fits(ts1, grammar, restI), fit1)
  +fR1 = Lemma.and_true_right_side(okR1, Spec.fits(rs1, grammar, tm1), hOk1)
  +fT1 = Lemma.and_true_right_side(Bool.and(okR1, Spec.fits(rs1, grammar, tm1)), Spec.fits(ts1, grammar, restI), fit1)
  +lr1 = Spec.leaves(rs1)
  +lt1 = Spec.leaves(ts1)
  +e1 = Nat.add(k, List.length(&2, Nat, lr1))
  +spR1 = G.spells_first(input, k, lr1, lt1, sp1)
  +spT1 = G.spells_second(input, k, lr1, lt1, sp1)
  +inA1 = all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, e1), List.append(&2, Spec.Bsr, Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1)), Spec.steps(root1, 0n), in1)
  +inR1 = all_in_left(Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +inT1 = all_in_right(Spec.walk(rs1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, e1), Spec.steps(root1, 0n), inA1)
  +fine1 = Lemma.and_true_left(okR1, Spec.fits(rs1, grammar, tm1), hOk1)
  LP1 = predicts_in(List.get(&2, Nat, input, e1), grammar, start, input, root1, rootFit1, rootSp1, ts1, restI, index, prefix, prefix, e1, i1, Nat.add(e1, List.length(&2, Nat, lt1)), Spec.walk(Spec.Loop{rs1} <> ts1, False{}, index, prefix, dot, i1, k), fT1, spT1, {==}, {==}, {==},
    end_walk(Spec.Loop{rs1} <> ts1, Spec.Brack{Spec.Positive{}, balts} <> restI, dot, grammar, index, prefix, i1, k, Nat.add(e1, List.length(&2, Nat, lt1)), fit1, itemsEq,
      Equal.sym(Nat, Nat.add(e1, List.length(&2, Nat, lt1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr1, lt1))), G.end_split(k, lr1, lt1)),
      Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs1} <> ts1)), {==})), in1)
  +okR2 = Spec.roundsOk(Spec.Positive{}, rs2)
  +tm2 = Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})
  +hOk2 = Lemma.and_true_left(Bool.and(okR2, Spec.fits(rs2, grammar, tm2)), Spec.fits(ts2, grammar, restI), fit2)
  +fR2 = Lemma.and_true_right_side(okR2, Spec.fits(rs2, grammar, tm2), hOk2)
  +fT2 = Lemma.and_true_right_side(Bool.and(okR2, Spec.fits(rs2, grammar, tm2)), Spec.fits(ts2, grammar, restI), fit2)
  +lr2 = Spec.leaves(rs2)
  +lt2 = Spec.leaves(ts2)
  +e2 = Nat.add(k, List.length(&2, Nat, lr2))
  +spR2 = G.spells_first(input, k, lr2, lt2, sp2)
  +spT2 = G.spells_second(input, k, lr2, lt2, sp2)
  +inA2 = all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, e2), List.append(&2, Spec.Bsr, Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2)), Spec.steps(root2, 0n), in2)
  +inR2 = all_in_left(Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +inT2 = all_in_right(Spec.walk(rs2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n), inA2)
  +fine2 = Lemma.and_true_left(okR2, Spec.fits(rs2, grammar, tm2), hOk2)
  LP2 = predicts_in(List.get(&2, Nat, input, e2), grammar, start, input, root2, rootFit2, rootSp2, ts2, restI, index, prefix, prefix, e2, i2, Nat.add(e2, List.length(&2, Nat, lt2)), Spec.walk(Spec.Loop{rs2} <> ts2, False{}, index, prefix, dot, i2, k), fT2, spT2, {==}, {==}, {==},
    end_walk(Spec.Loop{rs2} <> ts2, Spec.Brack{Spec.Positive{}, balts} <> restI, dot, grammar, index, prefix, i2, k, Nat.add(e2, List.length(&2, Nat, lt2)), fit2, itemsEq,
      Equal.sym(Nat, Nat.add(e2, List.length(&2, Nat, lt2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr2, lt2))), G.end_split(k, lr2, lt2)),
      Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs2} <> ts2)), {==})), in2)
  +itAt = items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Positive{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Brack{Spec.Positive{}, balts}, restI, itemsEq)
  both_same(grammar, start, rs1, rs2, ts1, ts2, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2,
    ihRs(True{}, rs2, [], index, prefix, dot, k, k, k, Spec.Positive{}, balts, restI, False{}, e1, e2, (itAt, (itT, ({==}, (even, (fR1, (fR2, (fine1, (fine2, (spR1, (spR2, (inR1, (inR2, ({==}, ({==}, (LP1, LP2)))))))))))))))),
    rse => seq_tail(rs1, rs2, rse, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs),
    rse => tse => loop_eq(rs1, rs2, ts1, ts2, rse, tse))


# The rounds after two equal rounds.
law round_tail_closure_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, r1, r2)

def round_tail_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), ch2, ch1, Equal.sym(+List<Spec.Tree>, ch1, ch2, che))
  +lr2 = List.length(&2, Nat, Spec.leaves(r2))
  +spR2b = Equal.trans(+List<Nat>, Spec.leaves(r2), Lemma.slice(input, e2, lr2), Lemma.slice(input, e1, lr2), spR2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lr2), e2, e1, eE))
  +inRr2b = Equal.trans(Bool, Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inRr2)
  +finRr2b = Equal.trans(Nat, Nat.add(e1, lr2), Nat.add(e2, lr2), E2, Equal.cong(Nat, Nat, v => Nat.add(v, lr2), e1, e2, Equal.sym(Nat, e2, e1, eE)), finRr2)
  ihR(True{}, r2, [], index, prefix, dot, i1, i2, e1, Spec.Closure{}, alts, restO, True{}, E1, E2, (itAt, (restAt, ({==}, (even, (fRest1, (fRest2, (fineR1, (fineR2, (spR1, (spR2b, (inRr1, (inRr2b, (finRr1, (finRr2b, (LP1, LP2))))))))))))))))

# Two equal choices for a round: the round, then the rest of the rounds.
law round_same_closure_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(alts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +cEq1: {Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])) == Spec.altOf(alts, a1) : +List<Spec.Item>}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def round_same_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihCh, ihR):
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(alts, a1)), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(alts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, pc1, 0n, i2, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [v]), 0n, i2, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +asc = G.nat_append_assoc(prefix, [dot], [a1])
  +evenC = Equal.trans(Bool, L.evenLength(pc1), L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), pc1, List.append(&2, Nat, prefix, [dot, a1]), asc),
    Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even))
  both_same(grammar, start, ch1, ch2, r1, r2, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2,
    ihCh(False{}, ch2, Spec.altOf(alts, a1), index, pc1, 0n, i1, i2, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq1, evenC)))))))),
    che => round_tail_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR),
    che => tse => pick_eq(a1, a2, ch1, ch2, r1, r2, ae, che, tse))

# Two rounds: the same choice, else a clash.
law rounds_closure_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, False{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, False{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def rounds_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Closure{}, alts, even, itAt))
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Closure{}, alts, even, itAt))
  +next = List.get(&2, Nat, input, k)
  cp1 = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, {==}, consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  cp2 = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, {==}, consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => round_same_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1), Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2), spR1, spR2, inRr1, inRr2,
      Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrr1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc1, lrr1))), E1, G.end_split(k, lc1, lrr1), finR1),
      Equal.trans(Nat, Nat.add(e2, List.length(&2, Nat, lrr2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc2, lrr2))), E2, G.end_split(k, lc2, lrr2), finR2), LP1, LP2, ihCh, ihR),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# One tree leaves the loop, the other takes another round: a clash.
law stop1_closure_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, False{}, []) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, False{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells([], input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, [], Spec.Pick{a2, ch2} <> r2)

def stop1_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Closure{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E1, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR1)
  +next = List.get(&2, Nat, input, E1)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Closure{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP1))
  cpA = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E1, nk), consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  make_clash(grammar, start, [], Spec.Pick{a2, ch2} <> r2, Spec.BracketAt{index, prefix, dot}, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)


# One tree leaves the loop, the other takes another round: a clash.
law stop2_closure_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, False{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, False{}, []) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells([], input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, [])

def stop2_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Closure{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E2, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR2)
  +next = List.get(&2, Nat, input, E2)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Closure{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP2))
  cpA = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E2, nk), consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, [], Spec.BracketAt{index, prefix, dot}, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)


# The rounds after two equal rounds.
law round_tail_closure_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, r1, r2)

def round_tail_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), ch2, ch1, Equal.sym(+List<Spec.Tree>, ch1, ch2, che))
  +lr2 = List.length(&2, Nat, Spec.leaves(r2))
  +spR2b = Equal.trans(+List<Nat>, Spec.leaves(r2), Lemma.slice(input, e2, lr2), Lemma.slice(input, e1, lr2), spR2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lr2), e2, e1, eE))
  +inRr2b = Equal.trans(Bool, Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inRr2)
  +finRr2b = Equal.trans(Nat, Nat.add(e1, lr2), Nat.add(e2, lr2), E2, Equal.cong(Nat, Nat, v => Nat.add(v, lr2), e1, e2, Equal.sym(Nat, e2, e1, eE)), finRr2)
  ihR(True{}, r2, [], index, prefix, dot, i1, i2, e1, Spec.Closure{}, alts, restO, True{}, E1, E2, (itAt, (restAt, ({==}, (even, (fRest1, (fRest2, (fineR1, (fineR2, (spR1, (spR2b, (inRr1, (inRr2b, (finRr1, (finRr2b, (LP1, LP2))))))))))))))))

# Two equal choices for a round: the round, then the rest of the rounds.
law round_same_closure_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(alts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +cEq1: {Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])) == Spec.altOf(alts, a1) : +List<Spec.Item>}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def round_same_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihCh, ihR):
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(alts, a1)), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(alts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, pc1, 0n, i2, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [v]), 0n, i2, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +asc = G.nat_append_assoc(prefix, [dot], [a1])
  +evenC = Equal.trans(Bool, L.evenLength(pc1), L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), pc1, List.append(&2, Nat, prefix, [dot, a1]), asc),
    Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even))
  both_same(grammar, start, ch1, ch2, r1, r2, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2,
    ihCh(False{}, ch2, Spec.altOf(alts, a1), index, pc1, 0n, i1, i2, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq1, evenC)))))))),
    che => round_tail_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR),
    che => tse => pick_eq(a1, a2, ch1, ch2, r1, r2, ae, che, tse))

# Two rounds: the same choice, else a clash.
law rounds_closure_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, True{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, True{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def rounds_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Closure{}, alts, even, itAt))
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Closure{}, alts, even, itAt))
  +next = List.get(&2, Nat, input, k)
  cp1 = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, {==}, consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  cp2 = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, {==}, consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => round_same_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1), Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2), spR1, spR2, inRr1, inRr2,
      Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrr1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc1, lrr1))), E1, G.end_split(k, lc1, lrr1), finR1),
      Equal.trans(Nat, Nat.add(e2, List.length(&2, Nat, lrr2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc2, lrr2))), E2, G.end_split(k, lc2, lrr2), finR2), LP1, LP2, ihCh, ihR),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# One tree leaves the loop, the other takes another round: a clash.
law stop1_closure_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, True{}, []) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, True{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells([], input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, [], Spec.Pick{a2, ch2} <> r2)

def stop1_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Closure{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E1, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR1)
  +next = List.get(&2, Nat, input, E1)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Closure{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP1))
  cpA = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E1, nk), consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  make_clash(grammar, start, [], Spec.Pick{a2, ch2} <> r2, Spec.BracketAt{index, prefix, dot}, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)


# One tree leaves the loop, the other takes another round: a clash.
law stop2_closure_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Closure{}, True{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Closure{}, True{}, []) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells([], input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, [])

def stop2_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Closure{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E2, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR2)
  +next = List.get(&2, Nat, input, E2)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Closure{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP2))
  cpA = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Closure{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E2, nk), consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, [], Spec.BracketAt{index, prefix, dot}, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)


# The rounds after two equal rounds.
law round_tail_positive_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, r1, r2)

def round_tail_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), ch2, ch1, Equal.sym(+List<Spec.Tree>, ch1, ch2, che))
  +lr2 = List.length(&2, Nat, Spec.leaves(r2))
  +spR2b = Equal.trans(+List<Nat>, Spec.leaves(r2), Lemma.slice(input, e2, lr2), Lemma.slice(input, e1, lr2), spR2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lr2), e2, e1, eE))
  +inRr2b = Equal.trans(Bool, Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inRr2)
  +finRr2b = Equal.trans(Nat, Nat.add(e1, lr2), Nat.add(e2, lr2), E2, Equal.cong(Nat, Nat, v => Nat.add(v, lr2), e1, e2, Equal.sym(Nat, e2, e1, eE)), finRr2)
  ihR(True{}, r2, [], index, prefix, dot, i1, i2, e1, Spec.Positive{}, alts, restO, True{}, E1, E2, (itAt, (restAt, ({==}, (even, (fRest1, (fRest2, (fineR1, (fineR2, (spR1, (spR2b, (inRr1, (inRr2b, (finRr1, (finRr2b, (LP1, LP2))))))))))))))))

# Two equal choices for a round: the round, then the rest of the rounds.
law round_same_positive_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(alts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +cEq1: {Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])) == Spec.altOf(alts, a1) : +List<Spec.Item>}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def round_same_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihCh, ihR):
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(alts, a1)), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(alts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, pc1, 0n, i2, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [v]), 0n, i2, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +asc = G.nat_append_assoc(prefix, [dot], [a1])
  +evenC = Equal.trans(Bool, L.evenLength(pc1), L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), pc1, List.append(&2, Nat, prefix, [dot, a1]), asc),
    Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even))
  both_same(grammar, start, ch1, ch2, r1, r2, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2,
    ihCh(False{}, ch2, Spec.altOf(alts, a1), index, pc1, 0n, i1, i2, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq1, evenC)))))))),
    che => round_tail_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR),
    che => tse => pick_eq(a1, a2, ch1, ch2, r1, r2, ae, che, tse))

# Two rounds: the same choice, else a clash.
law rounds_positive_first:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Positive{}, False{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Positive{}, False{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def rounds_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Positive{}, alts, even, itAt))
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Positive{}, alts, even, itAt))
  +next = List.get(&2, Nat, input, k)
  cp1 = bracket_cp(grammar, start, index, prefix, dot, a1, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, True{}, False{}, restO, next, isA1,
        predicts_in(next, grammar, start, input, root1, rootFit1, rootSp1, ch1, Spec.altOf(alts, a1), index, pcN1, pc1, k, i1, e1, wC1, fC1, spC1, {==}, {==}, asc1,
          end_walk(ch1, Spec.altOf(alts, a1), 0n, grammar, index, pc1, i1, k, e1, fC1, cEq1, {==}, {==}), inC1)))
  cp2 = bracket_cp(grammar, start, index, prefix, dot, a2, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, True{}, False{}, restO, next, isA2,
        predicts_in(next, grammar, start, input, root2, rootFit2, rootSp2, ch2, Spec.altOf(alts, a2), index, pcN2, pc2, k, i2, e2, wC2, fC2, spC2, {==}, {==}, asc2,
          end_walk(ch2, Spec.altOf(alts, a2), 0n, grammar, index, pc2, i2, k, e2, fC2, cEq2, {==}, {==}), inC2)))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => round_same_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, positive_rest(Spec.Pick{a1, ch1}, r1, fine1), positive_rest(Spec.Pick{a2, ch2}, r2, fine2), spR1, spR2, inRr1, inRr2,
      Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrr1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc1, lrr1))), E1, G.end_split(k, lc1, lrr1), finR1),
      Equal.trans(Nat, Nat.add(e2, List.length(&2, Nat, lrr2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc2, lrr2))), E2, G.end_split(k, lc2, lrr2), finR2), LP1, LP2, ihCh, ihR),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# The rounds after two equal rounds.
law round_tail_positive_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, r1, r2)

def round_tail_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), ch2, ch1, Equal.sym(+List<Spec.Tree>, ch1, ch2, che))
  +lr2 = List.length(&2, Nat, Spec.leaves(r2))
  +spR2b = Equal.trans(+List<Nat>, Spec.leaves(r2), Lemma.slice(input, e2, lr2), Lemma.slice(input, e1, lr2), spR2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lr2), e2, e1, eE))
  +inRr2b = Equal.trans(Bool, Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inRr2)
  +finRr2b = Equal.trans(Nat, Nat.add(e1, lr2), Nat.add(e2, lr2), E2, Equal.cong(Nat, Nat, v => Nat.add(v, lr2), e1, e2, Equal.sym(Nat, e2, e1, eE)), finRr2)
  ihR(True{}, r2, [], index, prefix, dot, i1, i2, e1, Spec.Positive{}, alts, restO, True{}, E1, E2, (itAt, (restAt, ({==}, (even, (fRest1, (fRest2, (fineR1, (fineR2, (spR1, (spR2b, (inRr1, (inRr2b, (finRr1, (finRr2b, (LP1, LP2))))))))))))))))

# Two equal choices for a round: the round, then the rest of the rounds.
law round_same_positive_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(alts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +cEq1: {Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])) == Spec.altOf(alts, a1) : +List<Spec.Item>}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def round_same_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihCh, ihR):
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(alts, a1)), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(alts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, pc1, 0n, i2, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2]), 0n, i2, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [v]), 0n, i2, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +asc = G.nat_append_assoc(prefix, [dot], [a1])
  +evenC = Equal.trans(Bool, L.evenLength(pc1), L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), pc1, List.append(&2, Nat, prefix, [dot, a1]), asc),
    Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even))
  both_same(grammar, start, ch1, ch2, r1, r2, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2,
    ihCh(False{}, ch2, Spec.altOf(alts, a1), index, pc1, 0n, i1, i2, k, Spec.Group{}, [], [], False{}, 0n, 0n, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq1, evenC)))))))),
    che => round_tail_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR),
    che => tse => pick_eq(a1, a2, ch1, ch2, r1, r2, ae, che, tse))

# Two rounds: the same choice, else a clash.
law rounds_positive_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Positive{}, True{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Positive{}, True{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2)

def rounds_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Positive{}, alts, even, itAt))
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Positive{}, alts, even, itAt))
  +next = List.get(&2, Nat, input, k)
  cp1 = after_cp(grammar, start, index, prefix, dot, a1, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, {==}, consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  cp2 = after_cp(grammar, start, index, prefix, dot, a2, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, {==}, consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2), decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => round_same_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1), Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2), spR1, spR2, inRr1, inRr2,
      Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrr1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc1, lrr1))), E1, G.end_split(k, lc1, lrr1), finR1),
      Equal.trans(Nat, Nat.add(e2, List.length(&2, Nat, lrr2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc2, lrr2))), E2, G.end_split(k, lc2, lrr2), finR2), LP1, LP2, ihCh, ihR),
    neq => make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Pick{a2, ch2} <> r2, Spec.AfterRoundAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))


# One tree leaves the loop, the other takes another round: a clash.
law stop1_positive_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a2: Nat
  for +ch2: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(Spec.Pick{a2, ch2} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch2} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Positive{}, True{}, []) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Positive{}, True{}, Spec.Pick{a2, ch2} <> r2) == True{} : Bool}
  for +sp1: G.Spells([], input, k)
  for +sp2: G.Spells(Spec.Pick{a2, ch2} <> r2, input, k)
  for +in1: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch2} <> r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch2} <> r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, [], Spec.Pick{a2, ch2} <> r2)

def stop1_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h2 = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)))
  +tmR2 = Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})
  +hOk2 = Lemma.and_true_left(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fC2 = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), hOk2)
  +fRest2 = Lemma.and_true_right_side(h2, Spec.fits(r2, grammar, tmR2), fR2)
  +lc2 = Spec.leaves(ch2)
  +lrr2 = Spec.leaves(r2)
  +e2 = Nat.add(k, List.length(&2, Nat, lc2))
  +spC2 = G.spells_first(input, k, lc2, lrr2, sp2)
  +spR2 = G.spells_second(input, k, lc2, lrr2, sp2)
  +pc2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a2])
  +pcN2 = List.append(&2, Nat, prefix, [dot, a2])
  +asc2 = G.nat_append_assoc(prefix, [dot], [a2])
  +wC2 = Spec.walk(ch2, False{}, index, pc2, 0n, i2, k)
  +wR2 = Spec.walk(r2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, e2)
  +inC2 = all_in_left(wC2, wR2, Spec.steps(root2, 0n), in2)
  +inRr2 = all_in_right(wC2, wR2, Spec.steps(root2, 0n), in2)
  +cEq2 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc2), Spec.sequenceAt(grammar, index, pcN2), Spec.altOf(alts, a2),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc2, pcN2, asc2), seq_child(grammar, index, prefix, dot, a2, Spec.Positive{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E1, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR1)
  +next = List.get(&2, Nat, input, E1)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = after_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Positive{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP1))
  cpA = after_cp(grammar, start, index, prefix, dot, a2, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a2), grammar, start, alts, a2, index, prefix, dot, False{}, True{}, restO, next, isA2,
        first_from(lc2, next, grammar, input, ch2, Spec.altOf(alts, a2), k, fC2, {==}, spC2, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E1, nk), consumes_child(a2, ch2, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch2}), Spec.allConsume(r2), fine2)))))
  make_clash(grammar, start, [], Spec.Pick{a2, ch2} <> r2, Spec.AfterRoundAt{index, prefix, dot}, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)


# One tree leaves the loop, the other takes another round: a clash.
law stop2_positive_later:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(Spec.Pick{a1, ch1} <> r1, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a1, ch1} <> r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(Spec.Positive{}, True{}, Spec.Pick{a1, ch1} <> r1) == True{} : Bool}
  for +fine2: {roundsFine(Spec.Positive{}, True{}, []) == True{} : Bool}
  for +sp1: G.Spells(Spec.Pick{a1, ch1} <> r1, input, k)
  for +sp2: G.Spells([], input, k)
  for +in1: {Spec.allIn(Spec.walk(Spec.Pick{a1, ch1} <> r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a1, ch1} <> r1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, [])

def stop2_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2):
  +h1 = Bool.and(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)))
  +tmR1 = Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})
  +hOk1 = Lemma.and_true_left(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +isA1 = Lemma.and_true_left(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fC1 = Lemma.and_true_right_side(Spec.isAlt(alts, a1), Spec.fits(ch1, grammar, Spec.altOf(alts, a1)), hOk1)
  +fRest1 = Lemma.and_true_right_side(h1, Spec.fits(r1, grammar, tmR1), fR1)
  +lc1 = Spec.leaves(ch1)
  +lrr1 = Spec.leaves(r1)
  +e1 = Nat.add(k, List.length(&2, Nat, lc1))
  +spC1 = G.spells_first(input, k, lc1, lrr1, sp1)
  +spR1 = G.spells_second(input, k, lc1, lrr1, sp1)
  +pc1 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a1])
  +pcN1 = List.append(&2, Nat, prefix, [dot, a1])
  +asc1 = G.nat_append_assoc(prefix, [dot], [a1])
  +wC1 = Spec.walk(ch1, False{}, index, pc1, 0n, i1, k)
  +wR1 = Spec.walk(r1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, e1)
  +inC1 = all_in_left(wC1, wR1, Spec.steps(root1, 0n), in1)
  +inRr1 = all_in_right(wC1, wR1, Spec.steps(root1, 0n), in1)
  +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc1), Spec.sequenceAt(grammar, index, pcN1), Spec.altOf(alts, a1),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc1, pcN1, asc1), seq_child(grammar, index, prefix, dot, a1, Spec.Positive{}, alts, even, itAt))
  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E2, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR2)
  +next = List.get(&2, Nat, input, E2)
  +n = List.length(&2, +List<Spec.Item>, alts)
  cpL = after_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), Spec.Positive{}, alts, restO, next, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP2))
  cpA = after_cp(grammar, start, index, prefix, dot, a1, Spec.Positive{}, alts, restO, next, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a1), grammar, start, alts, a1, index, prefix, dot, False{}, True{}, restO, next, isA1,
        first_from(lc1, next, grammar, input, ch1, Spec.altOf(alts, a1), k, fC1, {==}, spC1, Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E2, nk), consumes_child(a1, ch1, Lemma.and_true_left(Spec.consumes(Spec.Pick{a1, ch1}), Spec.allConsume(r1), fine1)))))
  make_clash(grammar, start, Spec.Pick{a1, ch1} <> r1, [], Spec.AfterRoundAt{index, prefix, dot}, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)

law leaf_disp:
  for items: +List<Spec.Item>
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ts1: +List<Spec.Tree>
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, Spec.Leaf{a1} <> ts1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Leaf{a1} <> ts1, f2)

def leaf_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ts1, ready, ihTs):
  match items f2:
    case Nil{} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          leaf_leaf(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ts1, a2, ts2, term, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihTs)
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))

law node_disp:
  for items: +List<Spec.Item>
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +q1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, Spec.Node{q1, ch1} <> ts1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Node{q1, ch1} <> ts1, f2)

def node_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, ch1, ts1, ready, ihCh, ihTs):
  match items f2:
    case Nil{} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          node_node(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, ch1, ts1, q2, ch2, ts2, x, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))

law pick_disp:
  for items: +List<Spec.Item>
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, Spec.Pick{a1, ch1} <> ts1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, f2)

def pick_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, ready, ihCh, ihTs):
  match items f2:
    case Nil{} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          group_group(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          optional_optional(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          optional_skip(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))

law skip_disp:
  for items: +List<Spec.Item>
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +ts1: +List<Spec.Tree>
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, Spec.Skip{} <> ts1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Skip{} <> ts1, f2)

def skip_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ready, ihTs):
  match items f2:
    case Nil{} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          skip_optional(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, a2, ch2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          +fitA = {fit1 : {Spec.fits(Spec.Skip{} <> ts1, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}
          +fitB = {fit2 : {Spec.fits(Spec.Skip{} <> ts2, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}
          skip_skip(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, Spec.Brack{Spec.Optional{}, balts}, restI, fitA, fitB, sp1, sp2, in1, in2, itemsEq, even, fitA, fitB, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Eps{}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Eps{}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Eps{}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Eps{}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          +fitA = {fit1 : {Spec.fits(Spec.Skip{} <> ts1, grammar, Spec.Eps{} <> restI) == True{} : Bool}}
          +fitB = {fit2 : {Spec.fits(Spec.Skip{} <> ts2, grammar, Spec.Eps{} <> restI) == True{} : Bool}}
          skip_skip(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ts2, Spec.Eps{}, restI, fitA, fitB, sp1, sp2, in1, in2, itemsEq, even, fitA, fitB, ihTs)
    case Con{Spec.Eps{}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit2))

law loop_disp:
  for items: +List<Spec.Item>
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for +rs1: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, Spec.Loop{rs1} <> ts1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihRs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, rs1)
  for ihTs: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ts1)
  Same(grammar, start, Spec.Loop{rs1} <> ts1, f2)

def loop_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, ready, ihRs, ihTs):
  match items f2:
    case Nil{} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Nil{} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          closure_closure(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, rs2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit2))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          positive_positive(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, rs2, ts2, balts, restI, fit1, fit2, sp1, sp2, in1, in2, itemsEq, even, ihRs, ihTs)
    case Con{Spec.Eps{}, +restI} Nil{}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, []), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Leaf{+a2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Leaf{a2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Node{+q2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Pick{+a2, +ch2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Pick{a2, ch2} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Skip{}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Skip{} <> ts2), Lemma.false_is_not_true(fit1))
    case Con{Spec.Eps{}, +restI} Con{Spec.Loop{+rs2}, +ts2}:
      match ready:
        case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts2), Lemma.false_is_not_true(fit1))

law rounds_nil_disp:
  for kind: Spec.Bracket
  for after: Bool
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for ready: CmpReady(True{}, grammar, start, input, root1, root2, [], f2, [], index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  Same(grammar, start, [], f2)

def rounds_nil_disp(kind, after, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2,  ready):
  match kind after f2:
    case Spec.Group{} _ _:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], f2), Lemma.false_is_not_true(isL))
    case Spec.Optional{} _ _:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], f2), Lemma.false_is_not_true(isL))
    case Spec.Closure{} False{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Inl{{==}}
    case Spec.Closure{} False{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop1_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Closure{} False{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Inl{{==}}
    case Spec.Closure{} True{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop1_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Closure{} True{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Inl{{==}}
    case Spec.Positive{} False{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Pick{a2, ch2} <> r2), Lemma.false_is_not_true(fine1))
    case Spec.Positive{} False{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Inl{{==}}
    case Spec.Positive{} True{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop1_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Positive{} True{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, [], Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))

law rounds_pick_disp:
  for kind: Spec.Bracket
  for after: Bool
  for f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
  for +a1: Nat
  for +ch1: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for ready: CmpReady(True{}, grammar, start, input, root1, root2, Spec.Pick{a1, ch1} <> r1, f2, [], index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  for ihCh: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ch1)
  for ihR: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, r1)
  Same(grammar, start, Spec.Pick{a1, ch1} <> r1, f2)

def rounds_pick_disp(kind, after, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, ready, ihCh, ihR):
  match kind after f2:
    case Spec.Group{} _ _:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, f2), Lemma.false_is_not_true(isL))
    case Spec.Optional{} _ _:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, f2), Lemma.false_is_not_true(isL))
    case Spec.Closure{} False{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop2_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Closure{} False{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          rounds_closure_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR)
    case Spec.Closure{} False{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} False{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop2_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Closure{} True{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          rounds_closure_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR)
    case Spec.Closure{} True{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Closure{} True{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, []), Lemma.false_is_not_true(fine2))
    case Spec.Positive{} False{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          rounds_positive_first(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR)
    case Spec.Positive{} False{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} False{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Nil{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          stop2_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2)
    case Spec.Positive{} True{} Con{Spec.Leaf{+a2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Leaf{a2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Node{+q2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Node{q2, ch2} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Pick{+a2, +ch2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          rounds_positive_later(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, a2, ch2, r2, itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2, ihCh, ihR)
    case Spec.Positive{} True{} Con{Spec.Skip{}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Skip{} <> r2), Lemma.false_is_not_true(fR2))
    case Spec.Positive{} True{} Con{Spec.Loop{+rs2}, +r2}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Pick{a1, ch1} <> r1, Spec.Loop{rs2} <> r2), Lemma.false_is_not_true(fR2))

law seq_nil:
  for f2: +List<Spec.Tree>
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for ready: CmpReady(False{}, grammar, start, input, root1, root2, [], f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  Same(grammar, start, [], f2)

def seq_nil(f2, items, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ready):
  match ready:
    case (fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even))))))):
      +none = fits_nil_items(items, grammar, fit1)
      +fit2b = Equal.trans(Bool, Spec.fits(f2, grammar, []), Spec.fits(f2, grammar, items), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), [], items, Equal.sym(+List<Spec.Item>, items, [], none)), fit2)
      Inl{Equal.sym(+List<Spec.Tree>, f2, [], L.fits_none(f2, grammar, fit2b))}

# Two forests that fit the same items from the same position, inside parse trees of the
# same input: the same forest, or a clash.
law compare:
  for f1: +List<Spec.Tree>
  for rounds: Bool
  for +f2: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
  for ready: CmpReady(rounds, grammar, start, input, root1, root2, f1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)
  Same(grammar, start, f1, f2)

def compare(f1, rounds, f2, items, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ready):
  match f1 rounds:
    case Nil{} False{}:
      seq_nil(f2, items, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ready)
    case Nil{} True{}:
      rounds_nil_disp(kind, after, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, ready)
    case Con{Spec.Leaf{+a1}, +ts1} False{}:
      leaf_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ts1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ts1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Node{+q1, +ch1}, +ts1} False{}:
      node_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, q1, ch1, ts1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ch1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)), (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ts1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Pick{+a1, +ch1}, +ts1} False{}:
      pick_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, a1, ch1, ts1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ch1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)), (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ts1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Skip{}, +ts1} False{}:
      skip_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, ts1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ts1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Loop{+rs1}, +ts1} False{}:
      loop_disp(items, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2, rs1, ts1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(rs1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)), (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ts1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Pick{+a1, +ch1}, +r1} True{}:
      rounds_pick_disp(kind, after, f2, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, index, prefix, dot, i1, i2, k, alts, restO, E1, E2, a1, ch1, r1, ready, (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(ch1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)), (ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(r1, ri, f2x, itx, grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd)))
    case Con{Spec.Leaf{a}, r1} True{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Leaf{a} <> r1, f2), Lemma.false_is_not_true(fR1))
    case Con{Spec.Node{q, ch}, r1} True{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Node{q, ch} <> r1, f2), Lemma.false_is_not_true(fR1))
    case Con{Spec.Skip{}, r1} True{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Skip{} <> r1, f2), Lemma.false_is_not_true(fR1))
    case Con{Spec.Loop{rs}, r1} True{}:
      match ready:
        case (itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2))))))))))))))):
          Empty.absurd(Same(grammar, start, Spec.Loop{rs} <> r1, f2), Lemma.false_is_not_true(fR1))

# ======== TWO PARSE TREES ========

law root_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -t1: Spec.Tree
  for -t2: Spec.Tree
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  Either<{t1 == t2 : Spec.Tree}, Clash(grammar, start)>

def root_clash(grammar, start, t1, t2, point, first, second, next, neq, cp1, cp2):
  Inr{(point, (first, (second, (next, (neq, (cp1, cp2))))))}

law root_then:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for r: Same(grammar, start, ch1, ch2)
  Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>

def root_then(grammar, start, q1, q2, qe, ch1, ch2, r):
  match r:
    case Inl{che}:
      Inl{Equal.trans(Spec.Tree, Spec.Node{q1, ch1}, Spec.Node{q2, ch1}, Spec.Node{q2, ch2}, Equal.cong(Nat, Spec.Tree, v => Spec.Node{v, ch1}, q1, q2, qe), Equal.cong(+List<Spec.Tree>, Spec.Tree, v => Spec.Node{q2, v}, ch1, ch2, che))}
    case Inr{c}:
      Inr{c}

law root_same:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +fit1: {Spec.fits([Spec.Node{q1, ch1}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([Spec.Node{q1, ch1}]) == input : +List<Nat>}
  for +fit2: {Spec.fits([Spec.Node{q2, ch2}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([Spec.Node{q2, ch2}]) == input : +List<Nat>}
  for +fC1: {Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}
  Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>

def root_same(grammar, start, input, q1, q2, qe, ch1, ch2, fit1, sp1, fit2, sp2, fC1, fC2):
  +root1 = {Spec.Node{q1, ch1} : Spec.Tree}
  +root2 = {Spec.Node{q2, ch2} : Spec.Tree}
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fC2)
  +in2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, q1, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, v, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), q1, q2, qe), all_in_refl(Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n)))
  root_then(grammar, start, q1, q2, qe, ch1, ch2,
    compare(ch1, False{}, ch2, Spec.rhsOf(grammar, q1), grammar, start, input, root1, fit1, sp1, root2, fit2, sp2, q1, [], 0n, 0n, 0n, 0n, Spec.Group{}, [], [], False{}, 0n, 0n,
      (fC1, (fC2b, (G.root_spells(input, q1, ch1, sp1), (G.root_spells(input, q2, ch2, sp2), (all_in_refl(Spec.walk(ch1, False{}, q1, [], 0n, 0n, 0n)), (in2, ({==}, {==})))))))))

# Two parse trees of the same input: the same tree, or a clash.
law trees_same:
  for tree1: Spec.Tree
  for tree2: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input : +List<Nat>}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([tree2]) == input : +List<Nat>}
  Either<{tree1 == tree2 : Spec.Tree}, Clash(grammar, start)>

def trees_same(tree1, tree2, grammar, start, input, fit1, sp1, fit2, sp2):
  match tree1 tree2:
    case Spec.Node{+q1, +ch1} Spec.Node{+q2, +ch2}:
      +h1 = Bool.and(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)))
      +h2 = Bool.and(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)))
      +hOk1 = Lemma.and_true_left(h1, True{}, fit1)
      +hOk2 = Lemma.and_true_left(h2, True{}, fit2)
      +lhs1 = Lemma.and_true_left(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
      +lhs2 = Lemma.and_true_left(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
      +fC1 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
      +fC2 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
      +next = List.get(&2, Nat, input, 0n)
      +w1 = Spec.walk(ch1, False{}, q1, [], 0n, 0n, 0n)
      +w2 = Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n)
      +n1 = List.length(&2, Nat, Spec.leaves(ch1))
      +n2 = List.length(&2, Nat, Spec.leaves(ch2))
      cp1 = nt_cp(Spec.lhsIs(grammar, q1, start), grammar, start, q1, next, lhs1,
        predicts_in(next, grammar, start, input, Spec.Node{q1, ch1}, fit1, sp1, ch1, Spec.rhsOf(grammar, q1), q1, [], [], 0n, 0n, n1, w1, fC1, G.root_spells(input, q1, ch1, sp1), {==}, {==}, {==},
          end_walk(ch1, Spec.rhsOf(grammar, q1), 0n, grammar, q1, [], 0n, 0n, n1, fC1, {==}, {==}, {==}), all_in_refl(w1)))
      cp2 = nt_cp(Spec.lhsIs(grammar, q2, start), grammar, start, q2, next, lhs2,
        predicts_in(next, grammar, start, input, Spec.Node{q2, ch2}, fit2, sp2, ch2, Spec.rhsOf(grammar, q2), q2, [], [], 0n, 0n, n2, w2, fC2, G.root_spells(input, q2, ch2, sp2), {==}, {==}, {==},
          end_walk(ch2, Spec.rhsOf(grammar, q2), 0n, grammar, q2, [], 0n, 0n, n2, fC2, {==}, {==}, {==}), all_in_refl(w2)))
      L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>, decide(Nat.is_eq(q1, q2), q1, q2, {==}),
        qe => root_same(grammar, start, input, q1, q2, qe, ch1, ch2, fit1, sp1, fit2, sp2, fC1, fC2),
        neq => root_clash(grammar, start, Spec.Node{q1, ch1}, Spec.Node{q2, ch2}, Spec.NonterminalAt{start}, q1, q2, next, neq, cp1, cp2))
    case Spec.Node{q1, ch1} Spec.Leaf{k}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Leaf{k} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Pick{a, ch}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Pick{a, ch} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Skip{}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Skip{} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Loop{rs}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Loop{rs} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Leaf{k} t2:
      Empty.absurd(Either<{Spec.Leaf{k} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Pick{a, ch} t2:
      Empty.absurd(Either<{Spec.Pick{a, ch} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Skip{} t2:
      Empty.absurd(Either<{Spec.Skip{} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Loop{rs} t2:
      Empty.absurd(Either<{Spec.Loop{rs} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))

# LL(1) rules out the clash.
law no_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -t1: Spec.Tree
  for -t2: Spec.Tree
  for r: Either<{t1 == t2 : Spec.Tree}, Clash(grammar, start)>
  for ll1: Spec.LL1(grammar, start)
  {t1 == t2 : Spec.Tree}

def no_clash(grammar, start, t1, t2, r, ll1):
  match r:
    case Inl{e}:
      e
    case Inr{c}:
      match c:
        case (point, (first, (second, (next, (neq, (cp1, cp2)))))):
          Empty.absurd({t1 == t2 : Spec.Tree}, ll1(point, first, second, next, neq, cp1, cp2))

# AN LL(1) GRAMMAR IS UNAMBIGUOUS.
law ll1_unambiguous:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for tree1: Spec.Tree
  for tree2: Spec.Tree
  for ll1: Spec.LL1(grammar, start)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input : +List<Nat>}
  for +sp2: {Spec.leaves([tree2]) == input : +List<Nat>}
  {tree1 == tree2 : Spec.Tree}

def ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, fit1, fit2, sp1, sp2):
  no_clash(grammar, start, tree1, tree2, trees_same(tree1, tree2, grammar, start, input, fit1, sp1, fit2, sp2), ll1)

# The law ll1_unambiguous.
def Laws.ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, fit1, fit2, sp1, sp2):
  ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, fit1, fit2, sp1, sp2)
