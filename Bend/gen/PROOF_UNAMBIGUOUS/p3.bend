
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
