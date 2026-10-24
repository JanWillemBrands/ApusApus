import Base

# A grammar that accepts exactly one character: 'a'.
#
# For now, we represent characters using natural numbers.
# The number 97 represents the character 'a'.

def grammarAccepts(inputCharacters: List<Nat>) -> Bool:
  match inputCharacters:
    case []:
      False{}
    case [firstCharacter]:
      Nat.is_eq(firstCharacter, 97n)
    case firstCharacter <> secondCharacter <> remainingCharacters:
      False{}

# A grammar that accepts exactly one fixed sequence of terminals.
#
# Terminals are token kinds, represented as natural numbers. For now each
# character is its own token kind, so 'a' is kind 97.

def sequenceAccepts(sequence: List<Nat>, inputTokens: List<Nat>) -> Bool:
  match sequence inputTokens:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{inputToken, remainingInput}:
      False{}
    case Con{terminal, remainingSequence} Nil{}:
      False{}
    case Con{terminal, remainingSequence} Con{inputToken, remainingInput}:
      Bool.and(Nat.is_eq(terminal, inputToken), sequenceAccepts(remainingSequence, remainingInput))
