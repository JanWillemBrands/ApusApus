import Base
import ./GRAMMAR.bend as Grammar

# STEP 1: a grammar that is one fixed sequence of terminals.

# Completeness: a sequence accepts the input that is equal to it.
law sequence_accepts_itself:
  for sequence: +List<Nat>
  {Grammar.sequenceAccepts(sequence, sequence) == True{} : Bool}

# Soundness: a sequence accepts no input other than itself.
law sequence_accepts_only_itself:
  for sequence: +List<Nat>
  for inputTokens: +List<Nat>
  for accepted: {Grammar.sequenceAccepts(sequence, inputTokens) == True{} : Bool}
  {sequence == inputTokens : +List<Nat>}

# STEP 2: a grammar with alternatives.
#
# `List.get(&2, +List<Nat>, alternatives, index)` is alternative number `index`
# (counting from 0), or None when there are fewer alternatives.

# Completeness: if alternative number `index` is the input, the grammar accepts it.
law alternatives_accept_each:
  for alternatives: +List<+List<Nat>>
  for index: Nat
  for +inputTokens: +List<Nat>
  for chosen: {List.get(&2, +List<Nat>, alternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}
  {Grammar.alternativesAccept(alternatives, inputTokens) == True{} : Bool}

# Soundness: if the grammar accepts the input, some alternative number `index` is the input.
law alternatives_accept_only_alternatives:
  for alternatives: +List<+List<Nat>>
  for +inputTokens: +List<Nat>
  for accepted: {Grammar.alternativesAccept(alternatives, inputTokens) == True{} : Bool}
  exs index: Nat
  {List.get(&2, +List<Nat>, alternatives, index) == Some{inputTokens} : Maybe<&2, +List<Nat>>}
