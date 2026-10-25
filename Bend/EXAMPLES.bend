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

# Is every element of xs in the set? Two inclusions make an equality of sets.
def allIn(xs: +List<Types.Bsr>, +set: +List<Types.Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(Spec.bsrMember(x, set), allIn(rest, set))

def sameSet(+xs: +List<Types.Bsr>, +ys: +List<Types.Bsr>) -> Bool:
  Bool.and(allIn(xs, ys), allIn(ys, xs))

# ()()() has exactly two parse trees; the set is exactly the steps of the two.
def threePairs() -> +List<Types.Bsr>:
  Grammar.bsrSet(brackets(), 0n, [1n, 2n, 1n, 2n, 1n, 2n])

def bothReadings() -> {sameSet(threePairs(), List.append(&2, Types.Bsr, Spec.steps(splitAfterFour(), 0n), Spec.steps(splitAfterTwo(), 0n))) == True{} : Bool}:
  {==}

# One reading alone is not the whole set: each has a step the other lacks.
def oneReadingIsNotAll() -> {sameSet(threePairs(), Spec.steps(splitAfterFour(), 0n)) == False{} : Bool}:
  {==}

def nestedExactly() -> {sameSet(Grammar.bsrSet(brackets(), 0n, [1n, 1n, 2n, 2n]), Spec.steps(nested(), 0n)) == True{} : Bool}:
  {==}

# No parse tree, so no elements, though CYK finds L, R and S on parts of the input.
def unbalancedEmpty() -> {Grammar.bsrSet(brackets(), 0n, [1n, 1n, 2n]) == [] : +List<Types.Bsr>}:
  {==}

# NO DEAD WOOD. Production 6, D = L R, matches every "()" but D is never used.
def bracketsWithDead() -> +List<Types.Production>:
  List.append(&2, Types.Production, brackets(), [Types.Production{4n, [Types.Nonterminal{2n}, Types.Nonterminal{3n}]}])

def deadWoodPruned() -> {sameSet(Grammar.bsrSet(bracketsWithDead(), 0n, [1n, 1n, 2n, 2n]), Spec.steps(nested(), 0n)) == True{} : Bool}:
  {==}

# SLOTS. The specification also covers productions with three symbols and empty
# ones; here checked against a hand-written list, since CYK only builds binary form.

# S = "(" S ")" (production 0) | ε (production 1), with ( = 1 and ) = 2.
# The tree of "()": S = ( S ) with the inner S empty.
def parenTree() -> Types.Tree:
  Types.Node{0n, [Types.Leaf{1n}, Types.Node{1n, []}, Types.Leaf{2n}]}

# Its steps, by Scott's definition: the slot S ::= ( S · ) over 0..1 with pivot 1,
# the complete S ::= ( S ) · over 0..2 with pivot 1, and the empty S at 1. The slot
# S ::= ( · S ) has no element: a slot with one symbol and more to come is skipped.
def parenSteps() -> +List<Types.Bsr>:
  [Types.Bsr{Types.Slot{0n, 2n}, 0n, 1n, 1n}, Types.Bsr{Types.Slot{1n, 0n}, 1n, 1n, 1n}, Types.Bsr{Types.Slot{0n, 3n}, 0n, 1n, 2n}]

def parenStepsExactly() -> {sameSet(Spec.steps(parenTree(), 0n), parenSteps()) == True{} : Bool}:
  {==}
