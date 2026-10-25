import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./LEMMAS.bend as Lemma

# Proofs of the rewriting laws in LAWS.bend.
#
# A forest fits a sequence of items one tree per item, so it splits and joins like the
# sequence: the head tree fits the head item and the rest fits the rest (fits_head,
# fits_tail, fits_join), and a forest for a concatenation of items is a concatenation
# of forests (fits_split, fits_append). Each law then rearranges the trees for the
# bracket it is about.

# ---- Heads and tails ----

law fits_head:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.fits(t <> ts, grammar, it <> rest) == True{} : Bool}
  {Spec.fits([t], grammar, [it]) == True{} : Bool}

def fits_head(t, ts, grammar, it, rest, e):
  match t it:
    case Spec.Leaf{+kind} Spec.Sym{Spec.Terminal{+k}}:
      Lemma.and_true_intro(Nat.is_eq(kind, k), True{}, Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), e), {==})
    case Spec.Leaf{+kind} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits([Spec.Leaf{kind}], grammar, [Spec.Sym{Spec.Nonterminal{id}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Leaf{kind}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Leaf{kind}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Leaf{kind}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Leaf{kind}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Sym{Spec.Terminal{k}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), e), {==})
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Sym{Spec.Terminal{k}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Sym{Spec.Nonterminal{id}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), e), {==})
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), e), {==})
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits([Spec.Skip{}], grammar, [Spec.Sym{Spec.Terminal{k}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits([Spec.Skip{}], grammar, [Spec.Sym{Spec.Nonterminal{id}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Skip{}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Optional{}, +alts}:
      {==}
    case Spec.Skip{} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Skip{}], grammar, [Spec.Brack{Spec.Closure{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Skip{}], grammar, [Spec.Brack{Spec.Positive{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits([Spec.Loop{rs}], grammar, [Spec.Sym{Spec.Terminal{k}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits([Spec.Loop{rs}], grammar, [Spec.Sym{Spec.Nonterminal{id}}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Loop{rs}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits([Spec.Loop{rs}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Closure{}, +alts}:
      Lemma.and_true_intro(Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), True{}, Lemma.and_true_left(Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), Spec.fits(ts, grammar, rest), e), {==})
    case Spec.Loop{+rs} Spec.Brack{Spec.Positive{}, +alts}:
      Lemma.and_true_intro(Bool.and(Bool.not(List.is_empty(&2, Spec.Tree, rs)), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}, Lemma.and_true_left(Bool.and(Bool.not(List.is_empty(&2, Spec.Tree, rs)), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), e), {==})

law fits_tail:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {Spec.fits(t <> ts, grammar, it <> rest) == True{} : Bool}
  {Spec.fits(ts, grammar, rest) == True{} : Bool}

def fits_tail(t, ts, grammar, it, rest, e):
  match t it:
    case Spec.Leaf{+kind} Spec.Sym{Spec.Terminal{+k}}:
      Lemma.and_true_right_side(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), e)
    case Spec.Leaf{+kind} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), e)
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), e)
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), e)
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Optional{}, +alts}:
      e
    case Spec.Skip{} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(ts, grammar, rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Closure{}, +alts}:
      Lemma.and_true_right_side(Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), Spec.fits(ts, grammar, rest), e)
    case Spec.Loop{+rs} Spec.Brack{Spec.Positive{}, +alts}:
      Lemma.and_true_right_side(Bool.and(Bool.not(List.is_empty(&2, Spec.Tree, rs)), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), e)

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
  match t it:
    case Spec.Leaf{+kind} Spec.Sym{Spec.Terminal{+k}}:
      Lemma.and_true_intro(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Nat.is_eq(kind, k), True{}, e), et)
    case Spec.Leaf{+kind} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Leaf{+kind} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, e), et)
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Node{+q, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Group{}, +alts}:
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, e), et)
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Optional{}, +alts}:
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, e), et)
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Pick{+a, +ch} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Optional{}, +alts}:
      et
    case Spec.Skip{} Spec.Brack{Spec.Closure{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Skip{} Spec.Brack{Spec.Positive{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Terminal{+k}}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Sym{Spec.Nonterminal{+id}}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Group{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Optional{}, +alts}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Spec.Loop{+rs} Spec.Brack{Spec.Closure{}, +alts}:
      Lemma.and_true_intro(Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), True{}, e), et)
    case Spec.Loop{+rs} Spec.Brack{Spec.Positive{}, +alts}:
      Lemma.and_true_intro(Bool.and(Bool.not(List.is_empty(&2, Spec.Tree, rs)), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), Lemma.and_true_left(Bool.and(Bool.not(List.is_empty(&2, Spec.Tree, rs)), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), True{}, e), et)

# ---- Leaves ----

law nat_append_assoc:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +zs: +List<Nat>
  {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : +List<Nat>}

def nat_append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(+List<Nat>, +List<Nat>, v => x <> v, List.append(&2, Nat, List.append(&2, Nat, rest, ys), zs), List.append(&2, Nat, rest, List.append(&2, Nat, ys, zs)), nat_append_assoc(rest, ys, zs))

law leaves_cons:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {Spec.leaves(t <> ts) == List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)) : +List<Nat>}

def leaves_cons(t, ts):
  match t:
    case Spec.Leaf{kind}:
      {==}
    case Spec.Node{q, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Pick{a, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Skip{}:
      {==}
    case Spec.Loop{+rs}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(rs), List.append(&2, Nat, Spec.leaves(rs), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(rs), []), Spec.leaves(rs), Lemma.append_nil_right(Spec.leaves(rs))))

law leaves_append:
  for f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  {Spec.leaves(List.append(&2, Spec.Tree, f1, f2)) == List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)) : +List<Nat>}

def leaves_append(f1, f2):
  match f1:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +lt = Spec.leaves([t])
      Equal.trans(+List<Nat>, Spec.leaves(t <> List.append(&2, Spec.Tree, ts, f2)), List.append(&2, Nat, lt, Spec.leaves(List.append(&2, Spec.Tree, ts, f2))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
        leaves_cons(t, List.append(&2, Spec.Tree, ts, f2)),
        Equal.trans(+List<Nat>, List.append(&2, Nat, lt, Spec.leaves(List.append(&2, Spec.Tree, ts, f2))), List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
          Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, lt, v), Spec.leaves(List.append(&2, Spec.Tree, ts, f2)), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2)), leaves_append(ts, f2)),
          Equal.trans(+List<Nat>, List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), List.append(&2, Nat, List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(f2)), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
            Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(f2)), List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), nat_append_assoc(lt, Spec.leaves(ts), Spec.leaves(f2))),
            Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(f2)), List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(t <> ts), Equal.sym(+List<Nat>, Spec.leaves(t <> ts), List.append(&2, Nat, lt, Spec.leaves(ts)), leaves_cons(t, ts))))))

# ---- Concatenations ----

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


# A forest for xs then a forest for ys is a forest for xs ++ ys.
law fits_append:
  for f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for xs: +List<Spec.Item>
  for +ys: +List<Spec.Item>
  for e1: {Spec.fits(f1, grammar, xs) == True{} : Bool}
  for +e2: {Spec.fits(f2, grammar, ys) == True{} : Bool}
  {Spec.fits(List.append(&2, Spec.Tree, f1, f2), grammar, List.append(&2, Spec.Item, xs, ys)) == True{} : Bool}

def fits_append(f1, f2, grammar, xs, ys, e1, e2):
  match f1 xs:
    case Nil{} Nil{}:
      e2
    case Nil{} Con{it, rest}:
      Empty.absurd({Spec.fits(f2, grammar, it <> List.append(&2, Spec.Item, rest, ys)) == True{} : Bool}, Lemma.false_is_not_true(e1))
    case Con{t, ts} Nil{}:
      Empty.absurd({Spec.fits(t <> List.append(&2, Spec.Tree, ts, f2), grammar, ys) == True{} : Bool}, fits_cons_nil(t, ts, grammar, e1))
    case Con{+t, +ts} Con{+it, +rest}:
      +both = e1
      fits_join(t, List.append(&2, Spec.Tree, ts, f2), grammar, it, List.append(&2, Spec.Item, rest, ys),
        fits_head(t, ts, grammar, it, rest, both),
        fits_append(ts, f2, grammar, rest, ys, fits_tail(t, ts, grammar, it, rest, both), e2))

def Split(+grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>, +xs: +List<Spec.Item>, +ys: +List<Spec.Item>) -> Type:
  &f1: +List<Spec.Tree> -> &f2: +List<Spec.Tree> -> {forest == List.append(&2, Spec.Tree, f1, f2) : +List<Spec.Tree>} & {Spec.fits(f1, grammar, xs) == True{} : Bool} & {Spec.fits(f2, grammar, ys) == True{} : Bool}

law split_cons:
  for +grammar: +List<Spec.Production>
  for +t: Spec.Tree
  for -ts: +List<Spec.Tree>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for -ys: +List<Spec.Item>
  for +head: {Spec.fits([t], grammar, [it]) == True{} : Bool}
  for later: Split(grammar, ts, rest, ys)
  Split(grammar, t <> ts, it <> rest, ys)

def split_cons(grammar, t, ts, it, rest, ys, head, later):
  match later:
    case (f10, (f2, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      (t <> f1, (f2, (Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => t <> v, ts, List.append(&2, Spec.Tree, f1, f2), eq), (fits_join(t, f1, grammar, it, rest, head, e1), e2))))

# A forest for xs ++ ys splits into a forest for xs and one for ys.
law fits_split:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for xs: +List<Spec.Item>
  for +ys: +List<Spec.Item>
  for e: {Spec.fits(forest, grammar, List.append(&2, Spec.Item, xs, ys)) == True{} : Bool}
  Split(grammar, forest, xs, ys)

def fits_split(forest, grammar, xs, ys, e):
  match forest xs:
    case _ Nil{}:
      ([], (forest, ({==}, ({==}, e))))
    case Nil{} Con{it, rest}:
      Empty.absurd(Split(grammar, [], it <> rest, ys), Lemma.false_is_not_true(e))
    case Con{+t, +ts} Con{+it, +rest}:
      +both = e
      split_cons(grammar, t, ts, it, rest, ys,
        fits_head(t, ts, grammar, it, List.append(&2, Spec.Item, rest, ys), both),
        fits_split(ts, grammar, rest, ys, fits_tail(t, ts, grammar, it, List.append(&2, Spec.Item, rest, ys), both)))

# ---- Moving a round in and out of a loop ----

law leaves_unloop:
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  {Spec.leaves(r <> Spec.Loop{rs} <> ts) == Spec.leaves(Spec.Loop{r <> rs} <> ts) : +List<Nat>}

def leaves_unloop(r, rs, ts):
  +lr = Spec.leaves([r])
  +lrs = Spec.leaves(rs)
  +lts = Spec.leaves(ts)
  Equal.trans(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), List.append(&2, Nat, Spec.leaves(r <> rs), lts),
    leaves_cons(r, Spec.Loop{rs} <> ts),
    Equal.trans(+List<Nat>, List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), List.append(&2, Nat, List.append(&2, Nat, lr, lrs), lts), List.append(&2, Nat, Spec.leaves(r <> rs), lts),
      Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lr, lrs), lts), List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), nat_append_assoc(lr, lrs, lts)),
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, lts), List.append(&2, Nat, lr, lrs), Spec.leaves(r <> rs), Equal.sym(+List<Nat>, Spec.leaves(r <> rs), List.append(&2, Nat, lr, lrs), leaves_cons(r, rs)))))

# A loop with a first round r is r next to a loop without it.
law unloop:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for rounds: {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for later: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for l: {Spec.leaves(Spec.Loop{r <> rs} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)

def unloop(grammar, alts, rest, w, r, rs, ts, rounds, later, l):
  +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
  +more = Spec.times(List.length(&2, Spec.Tree, rs), g)
  +both = rounds
  +fitsRest = Lemma.and_true_intro(Spec.fits(rs, grammar, more), Spec.fits(ts, grammar, rest), fits_tail(r, rs, grammar, g, more, both), later)
  (r <> Spec.Loop{rs} <> ts, (fits_join(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, fits_head(r, rs, grammar, g, more, both), fitsRest),
    Equal.trans(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{r <> rs} <> ts), w, leaves_unloop(r, rs, ts), l)))

# A round next to a loop is a loop with one more round.
def Reloop(+grammar: +List<Spec.Production>, +alts: +List<+List<Spec.Item>>, +rest: +List<Spec.Item>, +w: +List<Nat>) -> Type:
  &r: Spec.Tree -> &rs: +List<Spec.Tree> -> &ts: +List<Spec.Tree> ->
    {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.fits(ts, grammar, rest) == True{} : Bool} & {Spec.leaves(Spec.Loop{r <> rs} <> ts) == w : +List<Nat>}

law reloop:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for forest: +List<Spec.Tree>
  for f: {Spec.fits(forest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  Reloop(grammar, alts, rest, w)

def reloop(grammar, alts, rest, w, forest, f, l):
  match forest:
    case Nil{}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(f))
    case Con{+r, Nil{}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(fits_tail(r, [], grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Leaf{k}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(fits_tail(r, Spec.Leaf{k} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Node{+q, +ch}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(fits_tail(r, Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Pick{+a, +ch}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(fits_tail(r, Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Skip{}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(fits_tail(r, Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Loop{+rs}, +ts}}:
      +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +more = Spec.times(List.length(&2, Spec.Tree, rs), g)
      +both = f
      +tl = fits_tail(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, both)
      roundsOk = fits_join(r, rs, grammar, g, more, fits_head(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, both), Lemma.and_true_left(Spec.fits(rs, grammar, more), Spec.fits(ts, grammar, rest), tl))
      (r, (rs, (ts, (roundsOk, (Lemma.and_true_right_side(Spec.fits(rs, grammar, more), Spec.fits(ts, grammar, rest), tl),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{r <> rs} <> ts), Spec.leaves(r <> Spec.Loop{rs} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{r <> rs} <> ts), leaves_unloop(r, rs, ts)), l))))))

# ======== THE REWRITING LAWS ========

def Laws.empty_derives(grammar, w, d):
  match d:
    case (Nil{}, (f, l)):
      Equal.sym(+List<Nat>, [], w, l)
    case (Con{t, ts}, (f, l)):
      Empty.absurd({w == [] : +List<Nat>}, fits_cons_nil(t, ts, grammar, f))

def Laws.terminal_unfold(grammar, k, rest, w, d):
  match d:
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{+kind}, +ts}, (f, l)):
      +both = f
      kEq = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both))
      wEq = Equal.trans(+List<Nat>, w, kind <> Spec.leaves(ts), k <> Spec.leaves(ts), Equal.sym(+List<Nat>, kind <> Spec.leaves(ts), w, l), Equal.cong(Nat, +List<Nat>, x => x <> Spec.leaves(ts), kind, k, kEq))
      (Spec.leaves(ts), (wEq, (ts, (Lemma.and_true_right_side(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both), {==}))))
    case (Con{Spec.Node{q, ch}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a, ch}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{rs}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))

def Laws.nonterminal_unfold(grammar, a, rest, w, d):
  match d:
    case (Con{Spec.Node{+p, +ch}, +ts}, (f, l)):
      +h = Bool.and(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)), hOk)
      fch = Lemma.and_true_right_side(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)), hOk)
      fts = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both)
      (p, (lhsOk, (List.append(&2, Spec.Tree, ch, ts), (fits_append(ch, ts, grammar, Spec.rhsOf(grammar, p), rest, fch, fts),
        Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, ch, ts)), List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(ts)), w, leaves_append(ch, ts), l)))))
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))

def Laws.group_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Pick{+a, +ch}, +ts}, (f, l)):
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      fch = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      fts = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both)
      (a, (isA, (List.append(&2, Spec.Tree, ch, ts), (fits_append(ch, ts, grammar, Spec.altOf(alts, a), rest, fch, fts),
        Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, ch, ts)), List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(ts)), w, leaves_append(ch, ts), l)))))
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))

law nonterminal_join:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +p: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +forest: +List<Spec.Tree>
  for lhsOk: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  for sp: Split(grammar, forest, Spec.rhsOf(grammar, p), rest)
  Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)

def nonterminal_join(grammar, a, p, rest, w, forest, lhsOk, l, sp):
  match sp:
    case (f10, (f20, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      +f2 = {f20 : +List<Spec.Tree>}
      +lEq = Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), Spec.leaves(forest), w,
        Equal.cong(+List<Spec.Tree>, +List<Nat>, x => Spec.leaves(x), List.append(&2, Spec.Tree, f1, f2), forest, Equal.sym(+List<Spec.Tree>, forest, List.append(&2, Spec.Tree, f1, f2), eq)), l)
      (Spec.Node{p, f1} <> f2, (Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, p, a), Spec.fits(f1, grammar, Spec.rhsOf(grammar, p))), Spec.fits(f2, grammar, rest), Lemma.and_true_intro(Spec.lhsIs(grammar, p, a), Spec.fits(f1, grammar, Spec.rhsOf(grammar, p)), lhsOk, e1), e2),
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), w, Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), leaves_append(f1, f2)), lEq)))

def Laws.nonterminal_fold(grammar, a, p, rest, w, lhsOk, d):
  match d:
    case (forest0, (f, l)):
      +forest = {forest0 : +List<Spec.Tree>}
      nonterminal_join(grammar, a, p, rest, w, forest, lhsOk, l, fits_split(forest, grammar, Spec.rhsOf(grammar, p), rest, f))

law group_join:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +forest: +List<Spec.Tree>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  for sp: Split(grammar, forest, Spec.altOf(alts, a), rest)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)

def group_join(grammar, alts, a, rest, w, forest, isA, l, sp):
  match sp:
    case (f10, (f20, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      +f2 = {f20 : +List<Spec.Tree>}
      +lEq = Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), Spec.leaves(forest), w,
        Equal.cong(+List<Spec.Tree>, +List<Nat>, x => Spec.leaves(x), List.append(&2, Spec.Tree, f1, f2), forest, Equal.sym(+List<Spec.Tree>, forest, List.append(&2, Spec.Tree, f1, f2), eq)), l)
      (Spec.Pick{a, f1} <> f2, (Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(f1, grammar, Spec.altOf(alts, a))), Spec.fits(f2, grammar, rest), Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(f1, grammar, Spec.altOf(alts, a)), isA, e1), e2),
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), w, Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), leaves_append(f1, f2)), lEq)))

def Laws.group_fold(grammar, alts, a, rest, w, isA, d):
  match d:
    case (forest0, (f, l)):
      +forest = {forest0 : +List<Spec.Tree>}
      group_join(grammar, alts, a, rest, w, forest, isA, l, fits_split(forest, grammar, Spec.altOf(alts, a), rest, f))

def Laws.optional_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Skip{}, ts}, (f, l)):
      Inl{(ts, (f, l))}
    case (Con{Spec.Pick{a, ch}, ts}, (f, l)):
      Inr{(Spec.Pick{a, ch} <> ts, (f, l))}
    case (Nil{}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))

law optional_take:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)

def optional_take(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Pick{a, ch}, ts}, (f, l)):
      (Spec.Pick{a, ch} <> ts, (f, l))
    case (Nil{}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))

def Laws.optional_fold(grammar, alts, rest, w, d):
  match d:
    case Inl{skip}:
      match skip:
        case (forest, (f, l)):
          (Spec.Skip{} <> forest, (f, l))
    case Inr{take}:
      optional_take(grammar, alts, rest, w, take)

def Laws.closure_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Loop{Nil{}}, ts}, (f, l)):
      Inl{(ts, (f, l))}
    case (Con{Spec.Loop{Con{+r, +rs}}, +ts}, (f, l)):
      +h = Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts}))
      +both = f
      Inr{unloop(grammar, alts, rest, w, r, rs, ts, Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both), Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both), l)}
    case (Nil{}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))

def Laws.positive_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Loop{Nil{}}, ts}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{Con{+r, +rs}}, +ts}, (f, l)):
      +h = Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts}))
      +both = f
      unloop(grammar, alts, rest, w, r, rs, ts, Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both), Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both), l)
    case (Nil{}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))

law closure_more:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for re: Reloop(grammar, alts, rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)

def closure_more(grammar, alts, rest, w, re):
  match re:
    case (r0, (rs0, (ts0, (rounds, (later, l))))):
      +r = {r0 : Spec.Tree}
      +rs = {rs0 : +List<Spec.Tree>}
      +ts = {ts0 : +List<Spec.Tree>}
      (Spec.Loop{r <> rs} <> ts, (Lemma.and_true_intro(Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})), Spec.fits(ts, grammar, rest), rounds, later), l))

law positive_more:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for re: Reloop(grammar, alts, rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

def positive_more(grammar, alts, rest, w, re):
  match re:
    case (r0, (rs0, (ts0, (rounds, (later, l))))):
      +r = {r0 : Spec.Tree}
      +rs = {rs0 : +List<Spec.Tree>}
      +ts = {ts0 : +List<Spec.Tree>}
      (Spec.Loop{r <> rs} <> ts, (Lemma.and_true_intro(Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})), Spec.fits(ts, grammar, rest), rounds, later), l))

def Laws.closure_fold(grammar, alts, rest, w, d):
  match d:
    case Inl{none}:
      match none:
        case (forest, (f, l)):
          (Spec.Loop{[]} <> forest, (f, l))
    case Inr{more}:
      match more:
        case (forest, (f, l)):
          closure_more(grammar, alts, rest, w, reloop(grammar, alts, rest, w, forest, f, l))

def Laws.positive_fold(grammar, alts, rest, w, d):
  match d:
    case (forest, (f, l)):
      positive_more(grammar, alts, rest, w, reloop(grammar, alts, rest, w, forest, f, l))
