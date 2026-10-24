import Base
import ./GRAMMAR.bend as Grammar
import ./LAWS.bend as GrammarLaws

# HELPER LEMMAS
#
# Base has no lemmas that turn a Bool test into a proof, so we prove the few we need.

# The motive used to refute False == True: it sends False to Unit and True to Empty.
def TrueIsEmpty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False and True are different constructors, so an equality between them is impossible.
law false_is_not_true:
  for e: {False{} == True{} : Bool}
  Empty

# Rewriting True to False in the goal TrueIsEmpty(True) = Empty leaves TrueIsEmpty(False) = Unit.
def false_is_not_true(e):
  %e : TrueIsEmpty(_)
  Unit{}

# Nat.is_eq says True for equal numbers.
law nat_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def nat_eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

# Nat.is_eq says True only for equal numbers.
law nat_eq_sound:
  for a: Nat
  for b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def nat_eq_sound(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, false_is_not_true(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, false_is_not_true(e))
    case 1n+ap 1n+bp:
      %nat_eq_sound(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# A conjunction is True when both sides are True.
law and_true_intro:
  for x: Bool
  for -y: Bool
  for ex: {x == True{} : Bool}
  for ey: {y == True{} : Bool}
  {Bool.and(x, y) == True{} : Bool}

def and_true_intro(x, y, ex, ey):
  match x:
    case False{}:
      ex
    case True{}:
      ey

# A True conjunction has a True left side.
law and_true_left:
  for x: Bool
  for -y: Bool
  for e: {Bool.and(x, y) == True{} : Bool}
  {x == True{} : Bool}

def and_true_left(x, y, e):
  match x:
    case False{}:
      e
    case True{}:
      {==}

# A True conjunction has a True right side.
law and_true_right_side:
  for x: Bool
  for -y: Bool
  for e: {Bool.and(x, y) == True{} : Bool}
  {y == True{} : Bool}

def and_true_right_side(x, y, e):
  match x:
    case False{}:
      Empty.absurd({y == True{} : Bool}, false_is_not_true(e))
    case True{}:
      e

# STEP 1: a grammar that is one fixed sequence of terminals.

# Induction on the sequence: each terminal equals itself, and the rest accepts itself.
def GrammarLaws.sequence_accepts_itself(sequence):
  match sequence:
    case Nil{}:
      {==}
    case Con{+terminal, remainingSequence}:
      and_true_intro(
        Nat.is_eq(terminal, terminal),
        Grammar.sequenceAccepts(remainingSequence, remainingSequence),
        nat_eq_refl(terminal),
        GrammarLaws.sequence_accepts_itself(remainingSequence))

# Induction on both lists: unequal lengths contradict `accepted`; otherwise the heads
# are equal by nat_eq_sound, the tails by induction, so the lists are equal.
def GrammarLaws.sequence_accepts_only_itself(sequence, inputTokens, accepted):
  match sequence inputTokens:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{inputToken, remainingInput}:
      Empty.absurd({Nil{} == inputToken <> remainingInput : +List<Nat>}, false_is_not_true(accepted))
    case Con{terminal, remainingSequence} Nil{}:
      Empty.absurd({terminal <> remainingSequence == Nil{} : +List<Nat>}, false_is_not_true(accepted))
    case Con{+terminal, remainingSequence} Con{+inputToken, remainingInput}:
      # An equality proof is Data, so it may be copied: one copy for each side of the `and`.
      +bothAccepted = accepted
      headAccepted = and_true_left(
        Nat.is_eq(terminal, inputToken),
        Grammar.sequenceAccepts(remainingSequence, remainingInput),
        bothAccepted)
      tailAccepted = and_true_right_side(
        Nat.is_eq(terminal, inputToken),
        Grammar.sequenceAccepts(remainingSequence, remainingInput),
        bothAccepted)
      headEqual = nat_eq_sound(terminal, inputToken, headAccepted)
      tailEqual = GrammarLaws.sequence_accepts_only_itself(remainingSequence, remainingInput, tailAccepted)
      %tailEqual : {terminal <> remainingSequence == inputToken <> _ : +List<Nat>}
      %headEqual : {terminal <> remainingSequence == _ <> remainingSequence : +List<Nat>}
      {==}

# STEP 2: a grammar with alternatives.
#
# Helper lemmas for Maybe and Bool.or come first, then the two proofs.

# None and Some are different constructors.
def SomeIsEmpty(m: Maybe<&2, +List<Nat>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{value}:
      Empty

law none_is_not_some:
  for -value: +List<Nat>
  for e: {None{} == Some{value} : Maybe<&2, +List<Nat>>}
  Empty

def none_is_not_some(value, e):
  %e : SomeIsEmpty(_)
  Unit{}

# Equal sequences give equal Somes.
law some_of_equal:
  for -sequence: +List<Nat>
  for -inputTokens: +List<Nat>
  for e: {sequence == inputTokens : +List<Nat>}
  {Some{sequence} == Some{inputTokens} : Maybe<&2, +List<Nat>>}

def some_of_equal(sequence, inputTokens, e):
  %e : {Some{sequence} == Some{_} : Maybe<&2, +List<Nat>>}
  {==}

# The motive for chosen_accepts: the sequence inside a Some, run on the input.
def acceptsSome(m: Maybe<&2, +List<Nat>>, inputTokens: +List<Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{sequence}:
      Grammar.sequenceAccepts(sequence, inputTokens)

# If the chosen alternative is Some{input}, that alternative accepts the input.
law chosen_accepts:
  for sequence: +List<Nat>
  for +inputTokens: +List<Nat>
  for e: {Some{sequence} == Some{inputTokens} : Maybe<&2, +List<Nat>>}
  {Grammar.sequenceAccepts(sequence, inputTokens) == True{} : Bool}

def chosen_accepts(sequence, inputTokens, e):
  %Equal.sym(Maybe<&2, +List<Nat>>, Some{sequence}, Some{inputTokens}, e) : {acceptsSome(_, inputTokens) == True{} : Bool}
  GrammarLaws.sequence_accepts_itself(inputTokens)

# A disjunction is True when its left side is True.
law or_true_left_intro:
  for x: Bool
  for -y: Bool
  for ex: {x == True{} : Bool}
  {Bool.or(x, y) == True{} : Bool}

def or_true_left_intro(x, y, ex):
  match x:
    case False{}:
      Empty.absurd({y == True{} : Bool}, false_is_not_true(ex))
    case True{}:
      {==}

# A disjunction is True when its right side is True.
law or_true_right_intro:
  for x: Bool
  for -y: Bool
  for ey: {y == True{} : Bool}
  {Bool.or(x, y) == True{} : Bool}

def or_true_right_intro(x, y, ey):
  match x:
    case False{}:
      ey
    case True{}:
      {==}

# A True disjunction has a True left side or a True right side; the result says which.
law or_true_cases:
  for x: Bool
  for -y: Bool
  for e: {Bool.or(x, y) == True{} : Bool}
  Either<{x == True{} : Bool}, {y == True{} : Bool}>

def or_true_cases(x, y, e):
  match x:
    case False{}:
      Inr{e}
    case True{}:
      Inl{{==}}

# Induction on the alternatives and the index: index 0 picks the first alternative,
# index 1n+p is alternative p of the remaining ones.
def GrammarLaws.alternatives_accept_each(alternatives, index, inputTokens, chosen):
  match alternatives index:
    case Nil{} _:
      Empty.absurd({Grammar.alternativesAccept(Nil{}, inputTokens) == True{} : Bool}, none_is_not_some(inputTokens, chosen))
    case Con{+alternative, +remainingAlternatives} 0n:
      or_true_left_intro(
        Grammar.sequenceAccepts(alternative, inputTokens),
        Grammar.alternativesAccept(remainingAlternatives, inputTokens),
        chosen_accepts(alternative, inputTokens, chosen))
    case Con{+alternative, +remainingAlternatives} 1n+p:
      or_true_right_intro(
        Grammar.sequenceAccepts(alternative, inputTokens),
        Grammar.alternativesAccept(remainingAlternatives, inputTokens),
        GrammarLaws.alternatives_accept_each(remainingAlternatives, p, inputTokens, chosen))

# Alternative number k of the remaining alternatives is alternative number k+1 of the whole list.
law shift_found:
  for -alternative: +List<Nat>
  for -remainingAlternatives: +List<+List<Nat>>
  for -inputTokens: +List<Nat>
  for found: &index: Nat -> {List.get(&2, +List<Nat>, remainingAlternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}
  exs index: Nat
  {List.get(&2, +List<Nat>, alternative <> remainingAlternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}

def shift_found(alternative, remainingAlternatives, inputTokens, found):
  match found:
    case (index, proof):
      (1n+index, proof)

# Given which side of the `or` was True, produce the index of an accepting alternative.
law pick_alternative:
  for +alternative: +List<Nat>
  for -remainingAlternatives: +List<+List<Nat>>
  for +inputTokens: +List<Nat>
  for cases: Either<{Grammar.sequenceAccepts(alternative, inputTokens) == True{} : Bool}, {Grammar.alternativesAccept(remainingAlternatives, inputTokens) == True{} : Bool}>
  for searchRest: {Grammar.alternativesAccept(remainingAlternatives, inputTokens) == True{} : Bool} -> &index: Nat -> {List.get(&2, +List<Nat>, remainingAlternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}
  exs index: Nat
  {List.get(&2, +List<Nat>, alternative <> remainingAlternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}

def pick_alternative(alternative, remainingAlternatives, inputTokens, cases, searchRest):
  match cases:
    case Inl{acceptedHere}:
      (0n, some_of_equal(alternative, inputTokens, GrammarLaws.sequence_accepts_only_itself(alternative, inputTokens, acceptedHere)))
    case Inr{acceptedLater}:
      shift_found(alternative, remainingAlternatives, inputTokens, searchRest(acceptedLater))

# Induction on the alternatives: the `or` tells whether the first alternative accepted.
# If it did, the index is 0; if not, search the remaining alternatives and add one.
# The search of the rest is passed as a function, because it is needed only in the
# second case, and only there do we have the proof it needs.
def GrammarLaws.alternatives_accept_only_alternatives(alternatives, inputTokens, accepted):
  match alternatives:
    case Nil{}:
      (0n, Empty.absurd({List.get(&2, +List<Nat>, Nil{}, 0n) == Some{inputTokens} : Maybe<&2, +List<Nat>>}, false_is_not_true(accepted)))
    case Con{+alternative, +remainingAlternatives}:
      pick_alternative(
        alternative,
        remainingAlternatives,
        inputTokens,
        or_true_cases(
          Grammar.sequenceAccepts(alternative, inputTokens),
          Grammar.alternativesAccept(remainingAlternatives, inputTokens),
          accepted),
        laterAccepted => GrammarLaws.alternatives_accept_only_alternatives(remainingAlternatives, inputTokens, laterAccepted))
