import Base
import ./GRAMMAR.bend as Grammar
import ./LAWS.bend as GrammarLaws

# The grammar rejects an empty input.
def GrammarLaws.rejects_empty_input():
  {==}

# Every input containing at least two characters is rejected.
def GrammarLaws.rejects_multiple_characters(firstCharacter, secondCharacter, remainingCharacters):
  {==}

# A single-character input is accepted exactly when its character is 'a'.
def GrammarLaws.accepts_only_a(inputCharacter):
  {==}

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

# Nat.is_eq does not depend on the order of its arguments.
law nat_eq_symm:
  for a: Nat
  for b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def nat_eq_symm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat_eq_symm(ap, bp)

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

# True is the right identity of Bool.and.
law and_true_right:
  for b: Bool
  {Bool.and(b, True{}) == b : Bool}

def and_true_right(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# False absorbs Bool.and from the right.
law and_false_right:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def and_false_right(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

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
      Empty.absurd({Nil{} == inputToken <> remainingInput : List<Nat>}, false_is_not_true(accepted))
    case Con{terminal, remainingSequence} Nil{}:
      Empty.absurd({terminal <> remainingSequence == Nil{} : List<Nat>}, false_is_not_true(accepted))
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
      %tailEqual : {terminal <> remainingSequence == inputToken <> _ : List<Nat>}
      %headEqual : {terminal <> remainingSequence == _ <> remainingSequence : List<Nat>}
      {==}

# Case analysis on the input length. The one-token case differs only in the order of
# the Nat.is_eq arguments and a trailing `and True`; longer inputs end in `and False`.
def GrammarLaws.single_a_is_sequence_a(inputTokens):
  match inputTokens:
    case Nil{}:
      {==}
    case Con{+inputToken, Nil{}}:
      Equal.trans(
        Bool,
        Nat.is_eq(inputToken, 97n),
        Nat.is_eq(97n, inputToken),
        Bool.and(Nat.is_eq(97n, inputToken), True{}),
        nat_eq_symm(inputToken, 97n),
        Equal.sym(
          Bool,
          Bool.and(Nat.is_eq(97n, inputToken), True{}),
          Nat.is_eq(97n, inputToken),
          and_true_right(Nat.is_eq(97n, inputToken))))
    case Con{inputToken, Con{secondToken, remainingInput}}:
      Equal.sym(
        Bool,
        Bool.and(Nat.is_eq(97n, inputToken), False{}),
        False{},
        and_false_right(Nat.is_eq(97n, inputToken)))
