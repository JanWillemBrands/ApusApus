
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
