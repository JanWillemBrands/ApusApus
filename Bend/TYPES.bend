import Base

# The data types that both the code (GRAMMAR.bend) and the specification
# (LAWS.bend) talk about. Together with LAWS.bend this is what a reviewer reads.

# Terminals are token kinds, represented as natural numbers. For now each
# character is its own token kind, so 'a' is kind 97.

type Symbol is Data:
  Terminal{kind: Nat}
  Nonterminal{id: Nat}

# One production `lhs = rhs`. A grammar is a list of productions; several
# productions with the same lhs are its alternatives.
type Production is Data:
  Production{lhs: Nat, rhs: +List<Symbol>}

# A parse tree. A leaf is a token. A node names the production it uses, by its
# index in the grammar. LAWS.bend says when a tree is correct.
type Tree is Data:
  Leaf{kind: Nat}
  Node{index: Nat, children: +List<Tree>}

# A grammar slot: production `index` with its first `dot` symbols recognized.
type Slot is Data:
  Slot{index: Nat, dot: Nat}

# A binary subtree (BSR element): the recognized symbols of the slot cover the
# input from position i up to position j, and the last of them starts at the
# pivot k. When dot is the length of the right side the whole production is
# covered; for an empty right side the element is Bsr{Slot{index, 0}, i, i, i}.
type Bsr is Data:
  Bsr{slot: Slot, i: Nat, k: Nat, j: Nat}

# Reading the grammar: what production `index` says.

# Is production `index` a production of nonterminal `id`?
def lhsIs(+grammar: +List<Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Production{lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+i:
      lhsIs(rest, i, id)

# The right side of production `index` (empty when there is no such production).
def rhsOf(+grammar: +List<Production>, index: Nat) -> +List<Symbol>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Production{lhs, rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+i:
      rhsOf(rest, i)
