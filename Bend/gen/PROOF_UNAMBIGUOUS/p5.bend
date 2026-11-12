
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
