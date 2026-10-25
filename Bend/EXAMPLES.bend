import Base
import ./TYPES.bend as Types
import ./GRAMMAR.bend as Grammar
import ./LAWS.bend as Spec
import ./PROOF.bend as Proof

# Balanced brackets in binary form, with ( = 1 and ) = 2:
#   S = L R | L X | S S ;  X = S R ;  L = "(" ;  R = ")"
# Nonterminals: S = 0, X = 1, L = 2, R = 3. Productions are numbered from 0.
def brackets() -> +List<Types.Production>:
  [ Types.Production{0n, [Types.Nonterminal{2n}, Types.Nonterminal{3n}]},
    Types.Production{0n, [Types.Nonterminal{2n}, Types.Nonterminal{1n}]},
    Types.Production{0n, [Types.Nonterminal{0n}, Types.Nonterminal{0n}]},
    Types.Production{1n, [Types.Nonterminal{0n}, Types.Nonterminal{3n}]},
    Types.Production{2n, [Types.Terminal{1n}]},
    Types.Production{3n, [Types.Terminal{2n}]} ]

# The parse tree of "()": production 0 (S = L R) over 4 (L = "(") and 5 (R = ")").
def bracketPair() -> +List<Types.Tree>:
  [Types.Node{0n, [Types.Node{4n, [Types.Leaf{1n}]}, Types.Node{5n, [Types.Leaf{2n}]}]}]

# The checker verifies this value: "()" is derivable.
def bracketPairDerives() -> Spec.Derives(brackets(), [Types.Nonterminal{0n}], [1n, 2n]):
  (bracketPair(), ({==}, {==}))

# CYK on some inputs: (), (()), ()(()), ((), )(, and the empty input.
def main() -> List<Bool>:
  [ Grammar.recognize(brackets(), 0n, [1n, 2n]),
    Grammar.recognize(brackets(), 0n, [1n, 1n, 2n, 2n]),
    Grammar.recognize(brackets(), 0n, [1n, 2n, 1n, 1n, 2n, 2n]),
    Grammar.recognize(brackets(), 0n, [1n, 1n, 2n]),
    Grammar.recognize(brackets(), 0n, [2n, 1n]),
    Grammar.recognize(brackets(), 0n, []) ]

# BINARY SUBTREE SETS. The checker verifies each of these values by computation.

def bracketPairTree() -> Types.Tree:
  Types.Node{0n, [Types.Node{4n, [Types.Leaf{1n}]}, Types.Node{5n, [Types.Leaf{2n}]}]}

# The two readings of ()()() under S = S S.
def splitAfterFour() -> Types.Tree:
  Types.Node{2n, [Types.Node{2n, [bracketPairTree(), bracketPairTree()]}, bracketPairTree()]}

def splitAfterTwo() -> Types.Tree:
  Types.Node{2n, [bracketPairTree(), Types.Node{2n, [bracketPairTree(), bracketPairTree()]}]}

# (()) : S = L X, X = S R.
def nested() -> Types.Tree:
  Types.Node{1n, [Types.Node{4n, [Types.Leaf{1n}]}, Types.Node{3n, [bracketPairTree(), Types.Node{5n, [Types.Leaf{2n}]}]}]}

def bothReadingsA() -> {Spec.embedded(splitAfterFour(), Grammar.bsrSet(brackets(), [1n, 2n, 1n, 2n, 1n, 2n]), 0n) == True{} : Bool}:
  {==}

def bothReadingsB() -> {Spec.embedded(splitAfterTwo(), Grammar.bsrSet(brackets(), [1n, 2n, 1n, 2n, 1n, 2n]), 0n) == True{} : Bool}:
  {==}

def otherInputNot() -> {Spec.embedded(nested(), Grammar.bsrSet(brackets(), [1n, 2n, 1n, 2n]), 0n) == False{} : Bool}:
  {==}

def nestedYes() -> {Spec.embedded(nested(), Grammar.bsrSet(brackets(), [1n, 1n, 2n, 2n]), 0n) == True{} : Bool}:
  {==}
