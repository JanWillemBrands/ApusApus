import Base
import ./TYPES.bend as Types
import ./GRAMMAR.bend as Grammar

# STEP 4: recursive grammars.
#
# The specification works for any grammar, in any form. A parse tree is plain data;
# `fits` says when a forest is a correct parse of a sequence of symbols, and `leaves`
# reads the tokens off the forest.

# Is production `index` a production of nonterminal `id`?
def lhsIs(+grammar: +List<Types.Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Types.Production{lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+i:
      lhsIs(rest, i, id)

# The right side of production `index` (empty when there is no such production).
def rhsOf(+grammar: +List<Types.Production>, index: Nat) -> +List<Types.Symbol>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Types.Production{lhs, rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+i:
      rhsOf(rest, i)

# Does the forest fit the symbols, one tree per symbol? A leaf fits a terminal of
# its kind. A node fits a nonterminal when its production belongs to that
# nonterminal and its children fit the production's right side.
def fits(forest: +List<Types.Tree>, +grammar: +List<Types.Production>, symbols: +List<Types.Symbol>) -> Bool:
  match forest symbols:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{symbol, rest}:
      False{}
    case Con{tree, trees} Nil{}:
      False{}
    case Con{Types.Leaf{kind}, trees} Con{Types.Terminal{k}, rest}:
      Bool.and(Nat.is_eq(kind, k), fits(trees, grammar, rest))
    case Con{Types.Leaf{kind}, trees} Con{Types.Nonterminal{id}, rest}:
      False{}
    case Con{Types.Node{index, children}, trees} Con{Types.Terminal{k}, rest}:
      False{}
    case Con{Types.Node{+index, children}, trees} Con{Types.Nonterminal{id}, rest}:
      Bool.and(lhsIs(grammar, index, id), Bool.and(fits(children, grammar, rhsOf(grammar, index)), fits(trees, grammar, rest)))

# The tokens at the leaves of the forest, left to right.
def leaves(forest: +List<Types.Tree>) -> +List<Nat>:
  match forest:
    case Nil{}:
      []
    case Con{Types.Leaf{kind}, trees}:
      kind <> leaves(trees)
    case Con{Types.Node{index, children}, trees}:
      List.append(&2, Nat, leaves(children), leaves(trees))

# The symbols derive the input when some forest fits them and spells the input.
def Derives(+grammar: +List<Types.Production>, +symbols: +List<Types.Symbol>, +inputTokens: +List<Nat>) -> Type:
  &forest: +List<Types.Tree> -> {fits(forest, grammar, symbols) == True{} : Bool} & {leaves(forest) == inputTokens : +List<Nat>}

# SANITY LAWS: facts about the specification itself, independent of any recognizer.

# Nothing fits the empty sequence except the empty forest.
law only_empty_fits_nothing:
  for forest: +List<Types.Tree>
  for -grammar: +List<Types.Production>
  for fitting: {fits(forest, grammar, []) == True{} : Bool}
  {forest == [] : +List<Types.Tree>}

# A forest that fits one terminal spells exactly that terminal.
law terminal_spells_itself:
  for +forest: +List<Types.Tree>
  for -grammar: +List<Types.Production>
  for +kind: Nat
  for fitting: {fits(forest, grammar, [Types.Terminal{kind}]) == True{} : Bool}
  {leaves(forest) == [kind] : +List<Nat>}

# A grammar without productions derives nothing for a nonterminal.
law empty_grammar_derives_nothing:
  for forest: +List<Types.Tree>
  for -id: Nat
  for fitting: {fits(forest, [], [Types.Nonterminal{id}]) == True{} : Bool}
  Empty

# CYK.

# The form CYK needs: every production is A = "t" or A = B C.
def IsBinaryForm(grammar: +List<Types.Production>) -> Bool:
  match grammar:
    case Nil{}:
      True{}
    case Con{Types.Production{lhs, [Types.Terminal{kind}]}, rest}:
      IsBinaryForm(rest)
    case Con{Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, rest}:
      IsBinaryForm(rest)
    case Con{other, rest}:
      False{}

# Soundness, for every grammar: CYK only accepts input that has a parse tree.
law recognize_only_derivable:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for accepted: {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}
  Derives(grammar, [Types.Nonterminal{start}], inputTokens)

# Completeness, for grammars in binary form: CYK accepts every input that has a parse tree.
law recognize_every_derivable:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for binary: {IsBinaryForm(grammar) == True{} : Bool}
  for derivation: Derives(grammar, [Types.Nonterminal{start}], inputTokens)
  {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}

# BINARY SUBTREE SETS.

def bsrMember(+element: Types.Bsr, set: +List<Types.Bsr>) -> Bool:
  match element set:
    case _ Nil{}:
      False{}
    case Types.Bsr{+p, +i, +k, +j} Con{Types.Bsr{p2, i2, k2, j2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), bsrMember(Types.Bsr{p, i, k, j}, rest))

# A node with one child must have a leaf there: production `index` = "t" at position i.
def embeddedLeaf(+index: Nat, child: Types.Tree, +set: +List<Types.Bsr>, +i: Nat) -> Bool:
  match child:
    case Types.Leaf{kind}:
      bsrMember(Types.Bsr{index, i, i, 1n+i}, set)
    case Types.Node{index2, children2}:
      False{}

# Is every derivation step of the tree in the set, when the tree starts at
# position i? The positions come from the tree itself: a node with children t1 t2
# has its pivot after the leaves of t1. Trees of other shapes are not binary-form
# trees and are never embedded.
def embedded(tree: Types.Tree, +set: +List<Types.Bsr>, +i: Nat) -> Bool:
  match tree:
    case Types.Leaf{kind}:
      False{}
    case Types.Node{index, Nil{}}:
      False{}
    case Types.Node{index, Con{child, Nil{}}}:
      embeddedLeaf(index, child, set, i)
    case Types.Node{+index, Con{+first, Con{+second, Nil{}}}}:
      +k = Nat.add(i, List.length(&2, Nat, leaves([first])))
      +j = Nat.add(k, List.length(&2, Nat, leaves([second])))
      Bool.and(bsrMember(Types.Bsr{index, i, k, j}, set), Bool.and(embedded(first, set, i), embedded(second, set, k)))
    case Types.Node{index, Con{first, Con{second, Con{third, more}}}}:
      False{}

# Together the two laws say: among the trees that fit the grammar, the ones embedded
# in the BSR set are exactly the parse trees of the input. An oracle that selects
# trees from the set therefore chooses among all parse trees, and only those.

# Sound, for every grammar: a fitting tree of the input's length that is embedded
# in the set spells the input.
law bsr_only_parse_trees:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +tree: Types.Tree
  for fitting: {fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for long: {List.length(&2, Nat, leaves([tree])) == List.length(&2, Nat, inputTokens) : Nat}
  for inSet: {embedded(tree, Grammar.bsrSet(grammar, inputTokens), 0n) == True{} : Bool}
  {leaves([tree]) == inputTokens : +List<Nat>}

# Complete, for grammars in binary form: every parse tree of the input is embedded in the set.
law bsr_every_parse_tree:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +tree: Types.Tree
  for binary: {IsBinaryForm(grammar) == True{} : Bool}
  for fitting: {fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for spelled: {leaves([tree]) == inputTokens : +List<Nat>}
  {embedded(tree, Grammar.bsrSet(grammar, inputTokens), 0n) == True{} : Bool}
