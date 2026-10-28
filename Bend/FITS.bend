import Base
import ./SPEC.bend as Spec
import ./LEMMAS.bend as Lemma

# Facts about SPEC.bend's `fits`, one tree and one item at a time (for the proofs).

# A forest fits a sequence when its first tree fits the first item and the rest fits
# the rest.
law fits_cons:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  {Spec.fits(t <> ts, grammar, it <> rest) == Bool.and(Spec.fits([t], grammar, [it]), Spec.fits(ts, grammar, rest)) : Bool}

def fits_cons(t, ts, grammar, it, rest):
  match t it:
    case Spec.Leaf{+kind} Spec.Sym{Spec.Terminal{+k}}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Nat.is_eq(kind, k), Bool.and(Nat.is_eq(kind, k), True{}), Equal.sym(Bool, Bool.and(Nat.is_eq(kind, k), True{}), Nat.is_eq(kind, k), Lemma.and_true_unit(Nat.is_eq(kind, k))))
    case Spec.Leaf{+kind} Spec.Sym{Spec.Nonterminal{+id}}:
      {==}
    case Spec.Leaf{+kind} Spec.Brack{Spec.Group{}, +alts}:
      {==}
    case Spec.Leaf{+kind} Spec.Brack{Spec.Optional{}, +alts}:
      {==}
    case Spec.Leaf{+kind} Spec.Brack{Spec.Closure{}, +alts}:
      {==}
    case Spec.Leaf{+kind} Spec.Brack{Spec.Positive{}, +alts}:
      {==}
    case Spec.Leaf{+kind} Spec.Eps{}:
      {==}
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Terminal{+k}}:
      {==}
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Bool.and(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}), Equal.sym(Bool, Bool.and(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}), Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Lemma.and_true_unit(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))))))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Group{}, +alts}:
      {==}
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      {==}
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      {==}
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      {==}
    case Spec.Node{+q, +ch} Spec.Eps{}:
      {==}
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Terminal{+k}}:
      {==}
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      {==}
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Bool.and(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}), Equal.sym(Bool, Bool.and(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}), Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Lemma.and_true_unit(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))))))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Bool.and(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}), Equal.sym(Bool, Bool.and(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}), Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Lemma.and_true_unit(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))))))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      {==}
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      {==}
    case Spec.Pick{+a, +ch} Spec.Eps{}:
      {==}
    case Spec.Skip{} Spec.Sym{Spec.Terminal{+k}}:
      {==}
    case Spec.Skip{} Spec.Sym{Spec.Nonterminal{+id}}:
      {==}
    case Spec.Skip{} Spec.Brack{Spec.Group{}, +alts}:
      {==}
    case Spec.Skip{} Spec.Brack{Spec.Optional{}, +alts}:
      {==}
    case Spec.Skip{} Spec.Brack{Spec.Closure{}, +alts}:
      {==}
    case Spec.Skip{} Spec.Brack{Spec.Positive{}, +alts}:
      {==}
    case Spec.Skip{} Spec.Eps{}:
      {==}
    case Spec.Loop{+rs} Spec.Sym{Spec.Terminal{+k}}:
      {==}
    case Spec.Loop{+rs} Spec.Sym{Spec.Nonterminal{+id}}:
      {==}
    case Spec.Loop{+rs} Spec.Brack{Spec.Group{}, +alts}:
      {==}
    case Spec.Loop{+rs} Spec.Brack{Spec.Optional{}, +alts}:
      {==}
    case Spec.Loop{+rs} Spec.Brack{Spec.Closure{}, +alts}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Bool.and(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}), Equal.sym(Bool, Bool.and(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}), Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Lemma.and_true_unit(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))))))
    case Spec.Loop{+rs} Spec.Brack{Spec.Positive{}, +alts}:
      Equal.cong(Bool, Bool, v => Bool.and(v, Spec.fits(ts, grammar, rest)), Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Bool.and(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}), Equal.sym(Bool, Bool.and(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}), Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Lemma.and_true_unit(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))))))
    case Spec.Loop{+rs} Spec.Eps{}:
      {==}

law fits_head:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.fits(t <> ts, grammar, it <> rest) == True{} : Bool}
  {Spec.fits([t], grammar, [it]) == True{} : Bool}

def fits_head(t, ts, grammar, it, rest, e):
  +tt = t
  +ii = it
  Lemma.and_true_left(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest), Equal.trans(Bool, Bool.and(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest)), Spec.fits(tt <> ts, grammar, ii <> rest), True{}, Equal.sym(Bool, Spec.fits(tt <> ts, grammar, ii <> rest), Bool.and(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest)), fits_cons(tt, ts, grammar, ii, rest)), e))

law fits_tail:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.fits(t <> ts, grammar, it <> rest) == True{} : Bool}
  {Spec.fits(ts, grammar, rest) == True{} : Bool}

def fits_tail(t, ts, grammar, it, rest, e):
  +tt = t
  +ii = it
  Lemma.and_true_right_side(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest), Equal.trans(Bool, Bool.and(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest)), Spec.fits(tt <> ts, grammar, ii <> rest), True{}, Equal.sym(Bool, Spec.fits(tt <> ts, grammar, ii <> rest), Bool.and(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest)), fits_cons(tt, ts, grammar, ii, rest)), e))

law fits_join:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.fits([t], grammar, [it]) == True{} : Bool}
  for et: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  {Spec.fits(t <> ts, grammar, it <> rest) == True{} : Bool}

def fits_join(t, ts, grammar, it, rest, e, et):
  +tt = t
  +ii = it
  Equal.trans(Bool, Spec.fits(tt <> ts, grammar, ii <> rest), Bool.and(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest)), True{}, fits_cons(tt, ts, grammar, ii, rest), Lemma.and_true_intro(Spec.fits([tt], grammar, [ii]), Spec.fits(ts, grammar, rest), e, et))

# A non-empty forest fits no empty sequence.
law fits_cons_nil:
  for t: Spec.Tree
  for -ts: +List<Spec.Tree>
  for -grammar: +List<Spec.Production>
  for e: {Spec.fits(t <> ts, grammar, []) == True{} : Bool}
  Empty

def fits_cons_nil(t, ts, grammar, e):
  match t:
    case Spec.Leaf{k}:
      Lemma.false_is_not_true(e)
    case Spec.Node{q, ch}:
      Lemma.false_is_not_true(e)
    case Spec.Pick{a, ch}:
      Lemma.false_is_not_true(e)
    case Spec.Skip{}:
      Lemma.false_is_not_true(e)
    case Spec.Loop{rs}:
      Lemma.false_is_not_true(e)

# A forest fits as many items as it has trees.
law fits_count:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for items: +List<Spec.Item>
  for e: {Spec.fits(forest, grammar, items) == True{} : Bool}
  {List.length(&2, Spec.Tree, forest) == List.length(&2, Spec.Item, items) : Nat}

def fits_count(forest, grammar, items, e):
  match forest items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{it, rest}:
      Empty.absurd({0n == 1n+List.length(&2, Spec.Item, rest) : Nat}, Lemma.false_is_not_true(e))
    case Con{t, ts} Nil{}:
      Empty.absurd({1n+List.length(&2, Spec.Tree, ts) == 0n : Nat}, fits_cons_nil(t, ts, grammar, e))
    case Con{+t, +ts} Con{+it, +rest}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Tree, ts), List.length(&2, Spec.Item, rest), fits_count(ts, grammar, rest, fits_tail(t, ts, grammar, it, rest, e)))
