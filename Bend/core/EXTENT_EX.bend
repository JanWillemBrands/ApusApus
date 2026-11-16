import Base
import ./CORE.bend as Core
import ./EXTENT.bend as Extent

# THE SELECTING ORACLE ON EXAMPLES: @longest and @shortest.

def a() -> Core.Sym:
  Core.Terminal{1n}

# S = L R, L = a | a a, R = a | ε: on a a, L reads one or two tokens.
def split() -> +List<Core.Production>:
  [Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}, Core.Nonterminal{2n, Core.Anything{}}]},
   Core.Production{1n, [a()]}, Core.Production{1n, [a(), a()]},
   Core.Production{2n, [a()]}, Core.Production{2n, []}]

def short() -> Core.Tree:
  Core.Node{0n, [Core.Node{1n, [Core.Leaf{1n}]}, Core.Node{3n, [Core.Leaf{1n}]}]}

def long() -> Core.Tree:
  Core.Node{0n, [Core.Node{2n, [Core.Leaf{1n}, Core.Leaf{1n}]}, Core.Node{4n, []}]}

def kept(m: Maybe<&2, +List<Core.Bsr>>, +t: Core.Tree) -> Bool:
  match m:
    case Some{+set}:
      Core.allIn(Core.steps([t], 0n), set)
    case None{}:
      False{}

def longest() -> +List<Extent.ExtentMark>:
  [Extent.ItemExtent{0n, 1n, Extent.Longest{}}]

def shortest() -> +List<Extent.ExtentMark>:
  [Extent.ItemExtent{0n, 1n, Extent.Shortest{}}]

law longest_keeps:
  {kept(Extent.selectedSteps(20n, split(), [], [], longest(), 0n, [1n, 1n]), long()) == True{} : Bool}

def longest_keeps():
  {==}

law longest_drops:
  {kept(Extent.selectedSteps(20n, split(), [], [], longest(), 0n, [1n, 1n]), short()) == False{} : Bool}

def longest_drops():
  {==}

law shortest_keeps:
  {kept(Extent.selectedSteps(20n, split(), [], [], shortest(), 0n, [1n, 1n]), short()) == True{} : Bool}

def shortest_keeps():
  {==}

law shortest_drops:
  {kept(Extent.selectedSteps(20n, split(), [], [], shortest(), 0n, [1n, 1n]), long()) == False{} : Bool}

def shortest_drops():
  {==}

# A mark on the nonterminal L itself does the same.
law nonterminal_mark:
  {kept(Extent.selectedSteps(20n, split(), [], [], [Extent.NtExtent{1n, Extent.Longest{}}], 0n, [1n, 1n]), short()) == False{} : Bool}

def nonterminal_mark():
  {==}

# Without marks both readings stay.
law plain_keeps:
  {kept(Extent.selectedSteps(20n, split(), [], [], [], 0n, [1n, 1n]), short()) == True{} : Bool}

def plain_keeps():
  {==}
