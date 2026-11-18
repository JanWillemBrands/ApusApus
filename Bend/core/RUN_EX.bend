import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./RUN.bend as Run

def t(+k: Nat) -> Core.Sym:
  Core.Terminal{k}

def n(+x: Nat) -> Core.Sym:
  Core.Nonterminal{x, Core.Anything{}}

# E = E + E | n (left recursive, ambiguous)
def expr() -> +List<Core.Production>:
  [Core.Production{0n, [n(0n), t(2n), n(0n)]}, Core.Production{0n, [t(1n)]}]

# S = A b, A = a | ε
def opt() -> +List<Core.Production>:
  [Core.Production{0n, [n(1n), t(2n)]}, Core.Production{1n, [t(1n)]}, Core.Production{1n, []}]

# A = A | a | ε (cyclic, nullable)
def cyc() -> +List<Core.Production>:
  [Core.Production{0n, [n(0n)]}, Core.Production{0n, [t(1n)]}, Core.Production{0n, []}]

law inv_expr:
  {Run.invAlong(200n, Gll.NoPred{}, expr(), [1n, 2n, 1n, 2n, 1n], Run.initial(Gll.NoPred{}, expr(), 0n, [1n, 2n, 1n, 2n, 1n])) == True{} : Bool}

def inv_expr():
  {==}

law inv_opt:
  {Bool.and(Run.invAlong(100n, Gll.NoPred{}, opt(), [2n], Run.initial(Gll.NoPred{}, opt(), 0n, [2n])), Run.invAlong(100n, Gll.NoPred{}, opt(), [1n, 2n], Run.initial(Gll.NoPred{}, opt(), 0n, [1n, 2n]))) == True{} : Bool}

def inv_opt():
  {==}

law inv_cyc:
  {Bool.and(Run.invAlong(100n, Gll.NoPred{}, cyc(), [], Run.initial(Gll.NoPred{}, cyc(), 0n, [])), Run.invAlong(100n, Gll.NoPred{}, cyc(), [1n], Run.initial(Gll.NoPred{}, cyc(), 0n, [1n]))) == True{} : Bool}

def inv_cyc():
  {==}
