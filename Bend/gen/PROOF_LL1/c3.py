out = []
out.append('''
# ---- Brackets: the choices ----

# The sequence named by a prefix, when it has an item at the dot, is the engine's sequence at
# the reversed path.
law seq_path:
  for p: +List<Nat>
  for +R0: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +dot: Nat
  for +x: Spec.Item
  for e: {Spec.itemAt(Spec.sequenceIn(p, Gll.seqAt(grammar, index, R0)), dot) == Some{x} : Maybe<&2, Spec.Item>}
  {Spec.sequenceIn(p, Gll.seqAt(grammar, index, R0)) == Gll.seqAt(grammar, index, Gll.reverseOnto(p, R0)) : +List<Spec.Item>}

def seq_path(p, R0, grammar, index, dot, x, e):
  match p:
    case Nil{}:
      {==}
    case Con{m, Nil{}}:
      Empty.absurd({Spec.sequenceIn([m], Gll.seqAt(grammar, index, R0)) == Gll.seqAt(grammar, index, Gll.reverseOnto([m], R0)) : +List<Spec.Item>},
        Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{x}, e)))
    case Con{+m, Con{+a, +rest}}:
      +S = Gll.seqAt(grammar, index, R0)
      +alt = Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.bracketAlt(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, a <> (m <> R0)),
        alternative_eq(Spec.itemAt(S, m), a), Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Spec.itemAt(S, m), Gll.nthItem(S, m), item_at_eq(S, m)))
      +inner = Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Spec.sequenceIn(rest, v), Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, a <> (m <> R0)), alt)
      +e2 = Equal.trans(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), dot), Spec.itemAt(Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), dot), Some{x},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Spec.itemAt(v, dot), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)),
          Equal.sym(+List<Spec.Item>, Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), inner)), e)
      Equal.trans(+List<Spec.Item>, Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), Gll.seqAt(grammar, index, Gll.reverseOnto(rest, a <> (m <> R0))),
        inner, seq_path(rest, a <> (m <> R0), grammar, index, dot, x, e2))

# Alternate number c of a bracket, in the table's list of its alternates.
law alternates_in:
  for alts: +List<+List<Spec.Item>>
  for c2: Nat
  for +mayBeEmpty: Bool
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rpath: +List<Nat>
  for +a0: Nat
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for +e: {c == Nat.add(c2, a0) : Nat}
  for isA: {Nat.is_lt(c2, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +hs: {Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> rpath, Spec.altOf(alts, c2))) == True{} : Bool}
  HasAt(c, next, LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, rpath, a0))

def alternates_in(alts, c2, mayBeEmpty, grammar, t, index, rpath, a0, c, next, e, isA, hs):
  match alts c2:
    case Nil{} _:
      Empty.absurd(HasAt(c, next, []), Lemma.lt_zero_false(c2, isA))
    case Con{+alt, +rest} 0n:
      Inl{(e, Equal.trans(Bool, Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, a0 <> rpath, alt)), Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> rpath, alt)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, v <> rpath, alt)), a0, c, Equal.sym(Nat, c, a0, e)), hs))}
    case Con{+alt, +rest} 1n+(+d):
      Inr{alternates_in(rest, d, mayBeEmpty, grammar, t, index, rpath, 1n+a0, c, next, Equal.trans(Nat, c, 1n+Nat.add(d, a0), Nat.add(d, 1n+a0), e, Equal.sym(Nat, Nat.add(d, 1n+a0), 1n+Nat.add(d, a0), Lemma.add_succ_right(d, a0))), isA, hs)}

# An alternate that predicts the token: the token is in its table set.
law alt_set_has:
  for mayBeEmpty: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +c: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +next: Maybe<&2, Nat>
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for cp: Spec.predictsWhen(mayBeEmpty, grammar, start, Spec.altOf(alts, c), index, List.append(&2, Nat, p, [dot, c]), next)
  {Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> (dot <> R), Spec.altOf(alts, c))) == True{} : Bool}

def alt_set_has(mayBeEmpty, grammar, start, t, po, index, p, R, dot, c, kind, alts, next, rEq, itEq, cp):
  match mayBeEmpty:
    case True{}:
      +ctx = Gll.contextAfter(grammar, t, index, c <> (dot <> R))
      +rEq2 = Equal.trans(+List<Nat>, Gll.reverseOnto(R, [dot, c]), List.append(&2, Nat, Gll.reverseOnto(R, []), [dot, c]), List.append(&2, Nat, p, [dot, c]),
        G.rev_onto(R, [dot, c]), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [dot, c]), Gll.reverseOnto(R, []), p, rEq))
      Equal.trans(Bool, Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, R), dot), c), t), ctx)), Gll.lsHas(next, Gll.restOr(Gll.infoItems(Spec.altOf(alts, c), t), ctx)), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.bracketAlt(v, c), t), ctx)), Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Some{Spec.Brack{kind, alts}}, itEq),
        predicts_sound(grammar, start, t, po, Spec.altOf(alts, c), index, List.append(&2, Nat, p, [dot, c]), c <> (dot <> R), rEq2, next, cp))
    case False{}:
      first_of_sound(grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), Spec.altOf(alts, c), next, cp)

law leave_pick_has:
  for leave: Bool
  for +c: Nat
  for +n: Nat
  for +s: Gll.LSet
  for +next: Maybe<&2, Nat>
  for e: {leave == True{} : Bool}
  for +same: {c == n : Nat}
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{n, s}))

def leave_pick_has(leave, c, n, s, next, e, same, hs):
  match leave:
    case True{}:
      Inl{(same, hs)}
    case False{}:
      Empty.absurd(HasAt(c, next, []), Lemma.false_is_not_true(e))

# Leaving the bracket, when it predicts the token: the token is in the table set for leaving.
law leave_has:
  for l: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +c: Nat
  for +alts: +List<+List<Spec.Item>>
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +next: Maybe<&2, Nat>
  for +lEq: {Bool.and(Nat.is_eq(c, List.length(&2, +List<Spec.Item>, alts)), leave) == l : Bool}
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +restEq: {rest == Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)) : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.leaveChoice(l, rest, index, p), next)
  HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)}))

def leave_has(l, grammar, start, t, po, c, alts, leave, rest, index, p, R, dot, next, lEq, rEq, restEq, cp):
  match l:
    case True{}:
      +n = List.length(&2, +List<Spec.Item>, alts)
      +ctx = Gll.contextAfter(grammar, t, index, R)
      +hs0 = predicts_sound(grammar, start, t, po, rest, index, p, R, rEq, next, cp)
      +hs = Equal.trans(Bool, Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), t), ctx)), Gll.lsHas(next, Gll.restOr(Gll.infoItems(rest, t), ctx)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Gll.lsHas(next, Gll.restOr(Gll.infoItems(v, t), ctx)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), rest, Equal.sym(+List<Spec.Item>, rest, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restEq)), hs0)
      leave_pick_has(leave, c, n, Gll.predictAt(grammar, t, index, R, 1n+dot), next, Lemma.and_true_right_side(Nat.is_eq(c, n), leave, lEq),
        Lemma.nat_eq_sound(c, n, Lemma.and_true_left(Nat.is_eq(c, n), leave, lEq)), hs)
    case False{}:
      Empty.absurd(HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})), cp)

# A choice at a bracket that predicts the token: it is in the table's list of choices there.
law alt_choice:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +c: Nat
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +mayBeEmpty: Bool
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for +bEq: {Spec.isAlt(alts, c) == b : Bool}
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +restEq: {rest == Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)) : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.bracketAlternate(b, alts, c, index, p, dot, mayBeEmpty, leave, rest), next)
  HasAt(c, next, LL1.choicesWith(mayBeEmpty, leave, grammar, t, index, R, dot, alts))

def alt_choice(b, grammar, start, t, po, kind, alts, c, index, p, R, dot, mayBeEmpty, leave, rest, next, bEq, rEq, itEq, restEq, cp):
  match b:
    case True{}:
      +alternates = LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n)
      +leaving = LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})
      has_append_left(c, next, alternates, leaving,
        alternates_in(alts, c, mayBeEmpty, grammar, t, index, dot <> R, 0n, c, next, Equal.sym(Nat, Nat.add(c, 0n), c, Lemma.add_zero_right(c)), bEq,
          alt_set_has(mayBeEmpty, grammar, start, t, po, index, p, R, dot, c, kind, alts, next, rEq, itEq, cp)))
    case False{}:
      +alternates = LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n)
      +leaving = LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})
      has_append_right(c, next, alternates, leaving,
        leave_has(Bool.and(Nat.is_eq(c, List.length(&2, +List<Spec.Item>, alts)), leave), grammar, start, t, po, c, alts, leave, rest, index, p, R, dot, next, {==}, rEq, restEq, cp))
''')
open('partC3.bend', 'w').write('\n'.join(out))
