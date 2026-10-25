import Base
import ./TYPES.bend as Types
import ./GRAMMAR.bend as Grammar

# The specification works for any grammar, in any form. A parse tree is plain data;
# `fits` says when a forest is a correct parse of a sequence of symbols, and `leaves`
# reads the tokens off the forest.

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
      Bool.and(Types.lhsIs(grammar, index, id), Bool.and(fits(children, grammar, Types.rhsOf(grammar, index)), fits(trees, grammar, rest)))

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

# BINARY SUBTREE SETS.

def bsrMember(+element: Types.Bsr, set: +List<Types.Bsr>) -> Bool:
  match element set:
    case _ Nil{}:
      False{}
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j} Con{Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest))

# The step for slot dot + 1 of production `index` (a node starting at i), when the
# child that completes the slot covers at .. end. A slot with one symbol and more to
# come has no element (Scott's binarisation), so it contributes nothing.
def keepStep(keep: Bool, +element: Types.Bsr) -> +List<Types.Bsr>:
  match keep:
    case False{}:
      []
    case True{}:
      [element]

def slotSteps(+index: Nat, +dot: Nat, +i: Nat, +at: Nat, +end: Nat, last: Bool) -> +List<Types.Bsr>:
  keepStep(Bool.or(Bool.not(Nat.is_eq(dot, 0n)), last), Types.Bsr{Types.Slot{index, 1n+dot}, i, at, end})

# The step of a node without children (an empty right side), and nothing otherwise.
def emptySteps(+index: Nat, +at: Nat, children: +List<Types.Tree>) -> +List<Types.Bsr>:
  match children:
    case Nil{}:
      [Types.Bsr{Types.Slot{index, 0n}, at, at, at}]
    case Con{c, cs}:
      []

# The derivation steps of a node's children, from child number dot + 1 on. The node
# uses production `index` and starts at i; the first of these children starts at `at`.
# Each child completes a slot, and a child node also brings its own steps.
def childSteps(forest: +List<Types.Tree>, +index: Nat, +dot: Nat, +i: Nat, +at: Nat) -> +List<Types.Bsr>:
  match forest:
    case Nil{}:
      []
    case Con{Types.Leaf{kind}, +rest}:
      List.append(&2, Types.Bsr, slotSteps(index, dot, i, at, 1n+at, List.is_empty(&2, Types.Tree, rest)), childSteps(rest, index, 1n+dot, i, 1n+at))
    case Con{Types.Node{+q, +children}, +rest}:
      +end = Nat.add(at, List.length(&2, Nat, leaves(children)))
      List.append(&2, Types.Bsr, slotSteps(index, dot, i, at, end, List.is_empty(&2, Types.Tree, rest)),
        List.append(&2, Types.Bsr, List.append(&2, Types.Bsr, emptySteps(q, at, children), childSteps(children, q, 0n, at, at)),
          childSteps(rest, index, 1n+dot, i, end)))

# All derivation steps of a tree that starts at position i. The positions come from
# the tree itself: each child starts where the leaves of the children before it end.
def steps(tree: Types.Tree, +i: Nat) -> +List<Types.Bsr>:
  match tree:
    case Types.Leaf{kind}:
      []
    case Types.Node{+index, +children}:
      List.append(&2, Types.Bsr, emptySteps(index, i, children), childSteps(children, index, 0n, i, i))

# EXACT BSR SETS: what every parser must produce, for any grammar. A set is the
# exact BSR set of an input when it holds exactly the steps of the parse trees of
# the input: every element is a step of some parse tree (no dead wood), and no step
# of a parse tree is missing. An oracle selecting from such a set therefore chooses
# among all parse trees, and only those. Order and duplicates do not matter, so all
# correct parsers produce the same set.

# No dead wood: every element is a step of some parse tree of the input.
def OnlyParseSteps(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Types.Bsr>) -> Type:
  @element: Types.Bsr -> {bsrMember(element, set) == True{} : Bool} ->
    &tree: Types.Tree -> {fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool} & {leaves([tree]) == inputTokens : +List<Nat>} & {bsrMember(element, steps(tree, 0n)) == True{} : Bool}

# Nothing missing: every step of every parse tree of the input is in the set.
def EveryParseStep(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Types.Bsr>) -> Type:
  @tree: Types.Tree -> @element: Types.Bsr ->
    {fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool} -> {leaves([tree]) == inputTokens : +List<Nat>} -> {bsrMember(element, steps(tree, 0n)) == True{} : Bool} ->
    {bsrMember(element, set) == True{} : Bool}

def IsExactBsr(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +set: +List<Types.Bsr>) -> Type:
  OnlyParseSteps(grammar, start, inputTokens, set) & EveryParseStep(grammar, start, inputTokens, set)

# ----------------------------------------------------------------------------------
# THE IMPLEMENTATIONS. Everything above is the specification and mentions no
# algorithm. Below, each parser claims to produce exact BSR sets, under its own
# conditions on the grammar. GLL will add gll_bsr_exact here.

# CYK, a stepping stone and a reference to test other parsers against.

# Binary form, which the CYK-based parser needs for completeness: every production is A = "t" or A = B C.
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

# No dead wood, for every grammar.
law cyk_only_parse_steps:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  OnlyParseSteps(grammar, start, inputTokens, Grammar.bsrSet(grammar, start, inputTokens))

# Nothing missing, for grammars in binary form.
law cyk_every_parse_step:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for binary: {IsBinaryForm(grammar) == True{} : Bool}
  EveryParseStep(grammar, start, inputTokens, Grammar.bsrSet(grammar, start, inputTokens))

# Both, for grammars in binary form.
law cyk_bsr_exact:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for binary: {IsBinaryForm(grammar) == True{} : Bool}
  IsExactBsr(grammar, start, inputTokens, Grammar.bsrSet(grammar, start, inputTokens))

# The CYK recognizer accepts when its BSR set is not empty. Its laws follow from the above.

# Soundness, for every grammar: it only accepts input that has a parse tree.
law cyk_recognize_only_derivable:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for accepted: {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}
  Derives(grammar, [Types.Nonterminal{start}], inputTokens)

# Completeness, for grammars in binary form: it accepts every input that has a parse tree.
law cyk_recognize_every_derivable:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for binary: {IsBinaryForm(grammar) == True{} : Bool}
  for derivation: Derives(grammar, [Types.Nonterminal{start}], inputTokens)
  {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}
