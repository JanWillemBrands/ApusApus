import Base
import ./SPEC.bend as Spec
import ./PREFER.bend as Prefer
import ./EXACT.bend as Exact

def t(k: Nat) -> Spec.Item:
  Spec.Sym{Spec.Terminal{k}}

def n(id: Nat) -> Spec.Item:
  Spec.Sym{Spec.Nonterminal{id}}

def preferGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n)]}, Spec.Production{0n, [n(2n)]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}]

def cycleGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(0n)]}, Spec.Production{0n, [t(1n)]}]

def pairGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n)]}, Spec.Production{0n, [t(1n)]}, Spec.Production{1n, [n(0n)]}, Spec.Production{1n, [t(1n)]}]

# S ::= { ( @avoid A | B ) }, A ::= t, B ::= t : on t t, each round prefers B.
def loopGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[Spec.Brack{Spec.Group{}, [[n(1n)], [n(2n)]]}]]}]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}]

def loopMarks() -> +List<Spec.Mark>:
  [Spec.AltMark{0n, [0n, 0n, 0n], 0n, Spec.Avoided{}}]

def main() -> +List<Maybe<&2, +List<Spec.Bsr>>>:
  [Exact.exactSteps(2000n, preferGrammar(), 0n, [1n]),
   Prefer.preferSteps(2000n, preferGrammar(), [Spec.ProdMark{0n, Spec.Preferred{}}], 0n, [1n]),
   Prefer.preferSteps(2000n, cycleGrammar(), [Spec.ProdMark{0n, Spec.Preferred{}}], 0n, [1n]),
   Prefer.preferSteps(2000n, pairGrammar(), [Spec.ProdMark{0n, Spec.Preferred{}}, Spec.ProdMark{2n, Spec.Preferred{}}], 0n, [1n]),
   Exact.exactSteps(2000n, loopGrammar(), 0n, [1n, 1n]),
   Prefer.preferSteps(2000n, loopGrammar(), loopMarks(), 0n, [1n, 1n])]
