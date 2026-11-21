import Base
import ./SYNTAX.bend as Spec
import ./CORE.bend as Core
import ./EBNF.bend as E

# EXAMPLES: the translation towards Swift. For each grammar and input, a core tree of the
# translation reads the input, and its steps, mapped to Swift's slots, are the expected steps
# of that reading, in Swift's slots.

def t(k: Nat) -> Spec.Item:
  Spec.Sym{Spec.Terminal{k}}

def agrees(+g: +List<Spec.Production>, +input: +List<Nat>, +core: Core.Tree, +want: +List<Spec.Bsr>) -> Bool:
  +tr = E.towardsSwift(g)
  +cg = E.coreOf(tr)
  Bool.and(Core.reads([core], cg, [Core.Nonterminal{0n, Core.Anything{}}], input, 0n),
    Spec.sameSet(E.stepsToSwift(E.originsIn(tr), Core.steps([core], 0n)), want))

# THE EXPECTED STEPS OF EACH READING, IN SWIFT'S SLOTS.

def stepsOf_optional_pick() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [1n, 0n, 1n]}, 1n, 1n, 2n}]

def stepsOf_optional_skip() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 1n}]

def stepsOf_closure_two() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 1n, 1n, 2n}]

def stepsOf_closure_none() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}]

def stepsOf_positive_empty() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 1n, 1n]}, 0n, 0n, 0n}]

def stepsOf_positive_two() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 0n, 0n, 1n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 1n, 2n}, Spec.Bsr{Spec.Slot{0n, [0n, 0n, 0n, 0n, 1n]}, 1n, 1n, 2n}]

def stepsOf_group_epsilon() -> +List<Spec.Bsr>:
  [Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [0n, 1n, 1n]}, 0n, 0n, 0n}, Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 0n, 1n}]

# S = a [ b ]. Core: 0 S = a H, 1 E = ε, 2 H = ε, 3 H = G!, 4 G = b; E = 1, G = 2, H = 3.
def optional() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Brack{Spec.Optional{}, [[t(2n)]]}]}]

law optional_pick:
  {agrees(optional(), [1n, 2n], Core.Node{0n, [Core.Leaf{1n}, Core.Node{3n, [Core.Node{4n, [Core.Leaf{2n}]}]}]}, stepsOf_optional_pick()) == True{} : Bool}

def optional_pick():
  {==}

law optional_skip:
  {agrees(optional(), [1n], Core.Node{0n, [Core.Leaf{1n}, Core.Node{2n, []}]}, stepsOf_optional_skip()) == True{} : Bool}

def optional_skip():
  {==}

# S = { ( c ) }. Core: 0 S = H, 1 E = ε, 2 H = ε, 3 H = H G!, 4 G = c; E = 1, G = 2, H = 3.
def closure() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[Spec.Brack{Spec.Group{}, [[t(3n)]]}]]}]}]

law closure_two:
  {agrees(closure(), [3n, 3n],
    Core.Node{0n, [Core.Node{3n, [Core.Node{3n, [Core.Node{2n, []}, Core.Node{4n, [Core.Leaf{3n}]}]}, Core.Node{4n, [Core.Leaf{3n}]}]}]},
    stepsOf_closure_two()) == True{} : Bool}

def closure_two():
  {==}

law closure_none:
  {agrees(closure(), [], Core.Node{0n, [Core.Node{2n, []}]}, stepsOf_closure_none()) == True{} : Bool}

def closure_none():
  {==}

# S = < ( d | ε ) >. Core: 0 S = H, 1 E = ε, 2 H = G⁰, 3 H = K, 4 K = G!, 5 K = K G!,
# 6 G = d, 7 G = E; E = 1, G = 2, H = 3, K = 4.
def positive() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Positive{}, [[Spec.Brack{Spec.Group{}, [[t(4n)], [Spec.Eps{}]]}]]}]}]

law positive_empty:
  {agrees(positive(), [], Core.Node{0n, [Core.Node{2n, [Core.Node{7n, [Core.Node{1n, []}]}]}]},
    stepsOf_positive_empty()) == True{} : Bool}

def positive_empty():
  {==}

law positive_two:
  {agrees(positive(), [4n, 4n],
    Core.Node{0n, [Core.Node{3n, [Core.Node{5n, [Core.Node{4n, [Core.Node{6n, [Core.Leaf{4n}]}]}, Core.Node{6n, [Core.Leaf{4n}]}]}]}]},
    stepsOf_positive_two()) == True{} : Bool}

def positive_two():
  {==}

# The rules for empty rounds hold on the core: an empty round of < > next to others is no
# tree (K's rounds must read something).
law positive_no_empty_round:
  {Core.reads([Core.Node{0n, [Core.Node{3n, [Core.Node{5n, [Core.Node{4n, [Core.Node{7n, [Core.Node{1n, []}]}]}, Core.Node{6n, [Core.Leaf{4n}]}]}]}]}],
    E.coreOf(E.towardsSwift(positive())), [Core.Nonterminal{0n, Core.Anything{}}], [4n], 0n) == False{} : Bool}

def positive_no_empty_round():
  {==}

# S = ( a | ε ) b. Core: 0 S = G b, 1 E = ε, 2 G = a, 3 G = E; E = 1, G = 2.
def group() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Group{}, [[t(1n)], [Spec.Eps{}]]}, t(2n)]}]

law group_epsilon:
  {agrees(group(), [2n], Core.Node{0n, [Core.Node{3n, [Core.Node{1n, []}]}, Core.Leaf{2n}]}, stepsOf_group_epsilon()) == True{} : Bool}

def group_epsilon():
  {==}

# Towards LL(1), S = { ( c ) } is right-recursive: 0 S = H, 1 E = ε, 2 H = ε, 3 H = G! H,
# 4 G = c. Its tree for c c chooses "another round" where each round starts.
law closure_towards_ll1:
  {Core.reads([Core.Node{0n, [Core.Node{3n, [Core.Node{4n, [Core.Leaf{3n}]}, Core.Node{3n, [Core.Node{4n, [Core.Leaf{3n}]}, Core.Node{2n, []}]}]}]}],
    E.coreOf(E.towardsLL1(closure())), [Core.Nonterminal{0n, Core.Anything{}}], [3n, 3n], 0n) == True{} : Bool}

def closure_towards_ll1():
  {==}
