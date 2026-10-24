import Base
import ./GRAMMAR.bend as Grammar

# An empty input is not accepted by our grammar.
law rejects_empty_input:
  {Grammar.grammarAccepts([]) == False{} : Bool}

# Any input containing two or more characters is rejected.
law rejects_multiple_characters:
  for firstCharacter: Nat
  for secondCharacter: Nat
  for remainingCharacters: List<Nat>
  {Grammar.grammarAccepts(firstCharacter <> secondCharacter <> remainingCharacters) == False{} : Bool}

# For a single-character input, the grammar's decision agrees with whether that character is 'a'.
law accepts_only_a:
  for inputCharacter: Nat
  {Grammar.grammarAccepts([inputCharacter]) == Nat.is_eq(inputCharacter, 97n) : Bool}

# STEP 1: a grammar that is one fixed sequence of terminals.

# Completeness: a sequence accepts the input that is equal to it.
law sequence_accepts_itself:
  for sequence: List<Nat>
  {Grammar.sequenceAccepts(sequence, sequence) == True{} : Bool}

# Soundness: a sequence accepts no input other than itself.
law sequence_accepts_only_itself:
  for sequence: List<Nat>
  for inputTokens: List<Nat>
  for accepted: {Grammar.sequenceAccepts(sequence, inputTokens) == True{} : Bool}
  {sequence == inputTokens : List<Nat>}

# The single-'a' grammar of step 0 is the sequence grammar for the sequence [a].
law single_a_is_sequence_a:
  for inputTokens: List<Nat>
  {Grammar.grammarAccepts(inputTokens) == Grammar.sequenceAccepts([97n], inputTokens) : Bool}
