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

# A binary subtree (BSR element): production `index` covers the input from position
# i up to position j, and its last symbol starts at the pivot k. For A = "t" the
# pivot is i; for A = B C, B covers i .. k and C covers k .. j.
type Bsr is Data:
  Bsr{index: Nat, i: Nat, k: Nat, j: Nat}
