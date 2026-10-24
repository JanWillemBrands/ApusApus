import Base

# Terminals are token kinds, represented as natural numbers. For now each
# character is its own token kind, so 'a' is kind 97.
#
# Grammars and inputs are read many times, so they are copyable (`+List`).

# STEP 1: a grammar that accepts exactly one fixed sequence of terminals.

def sequenceAccepts(sequence: +List<Nat>, inputTokens: +List<Nat>) -> Bool:
  match sequence inputTokens:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{inputToken, remainingInput}:
      False{}
    case Con{terminal, remainingSequence} Nil{}:
      False{}
    case Con{terminal, remainingSequence} Con{inputToken, remainingInput}:
      Bool.and(Nat.is_eq(terminal, inputToken), sequenceAccepts(remainingSequence, remainingInput))

# STEP 2: a grammar with alternatives. Each alternative is a sequence, and the
# grammar accepts an input when at least one alternative accepts it.

def alternativesAccept(alternatives: +List<+List<Nat>>, +inputTokens: +List<Nat>) -> Bool:
  match alternatives:
    case Nil{}:
      False{}
    case Con{alternative, remainingAlternatives}:
      Bool.or(sequenceAccepts(alternative, inputTokens), alternativesAccept(remainingAlternatives, inputTokens))
