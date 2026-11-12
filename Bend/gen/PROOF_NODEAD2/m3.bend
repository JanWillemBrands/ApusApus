
# ======== TWO CHOICES AT A BRACKET THAT ADMIT THE TOKEN: A CONFLICT ========

# The checks at the bracket at item dot of the sequence at (index, R) are among the
# grammar's checks.
law local_conflict:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(R)) == Gll.seqAt(grammar, index, R) : +List<Spec.Item>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ne: {List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, R, dot)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def local_conflict(grammar, t, index, R, dot, kind, alts, seqEq, itEq, ne):
  +p = prefixOf(R)
  +S = Spec.sequenceAt(grammar, index, p)
  +itS = Equal.trans(Maybe<&2, Spec.Item>, Spec.itemAt(S, dot), Gll.nthItem(S, dot), Some{Spec.Brack{kind, alts}}, L.item_at_eq(S, dot),
    Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(S, dot), Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Some{Spec.Brack{kind, alts}}, Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), S, Gll.seqAt(grammar, index, R), seqEq), itEq))
  +back = L.reverse_twice(R, [])
  +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, L.localConflicts(Spec.itemAt(S, dot), grammar, t, index, Gll.reverseOnto(p, []), dot)), List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)), False{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, L.localConflicts(v, grammar, t, index, Gll.reverseOnto(p, []), dot)), Spec.itemAt(S, dot), Some{Spec.Brack{kind, alts}}, itS),
    Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)), List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, R, dot)), False{},
      Equal.cong(+List<Nat>, Bool, v => List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, v, dot)), Gll.reverseOnto(p, []), R, back), ne))
  L.nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
    L.prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), L.locate(p, Gll.nestFuel(), grammar, t, index, [], dot, ne2)))
