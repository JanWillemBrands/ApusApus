import Base
import ./CORE.bend as Core
import ./TABLES.bend as T

# THE LL(1) CHECK ON EXAMPLES.

def t(+k: Nat) -> Core.Sym:
  Core.Terminal{k}

def n(+x: Nat) -> Core.Sym:
  Core.Nonterminal{x, Core.Anything{}}

# A = a | b: LL(1).
law two_tokens:
  {T.ll1ByTables(10n, [Core.Production{0n, [t(1n)]}, Core.Production{0n, [t(2n)]}], 0n) == True{} : Bool}

def two_tokens():
  {==}

# A = a | a: both predict a.
law same_token:
  {T.ll1ByTables(10n, [Core.Production{0n, [t(1n)]}, Core.Production{0n, [t(1n)]}], 0n) == False{} : Bool}

def same_token():
  {==}

# A = ε | ε: both predict the end.
law two_empty:
  {T.ll1ByTables(10n, [Core.Production{0n, []}, Core.Production{0n, []}], 0n) == False{} : Bool}

def two_empty():
  {==}

# S = A b, A = a | ε: A -> ε predicts b, from FOLLOW. LL(1).
law follow_apart:
  {T.ll1ByTables(10n, [Core.Production{0n, [n(1n), t(2n)]}, Core.Production{1n, [t(1n)]}, Core.Production{1n, []}], 0n) == True{} : Bool}

def follow_apart():
  {==}

# S = A a, A = a | ε: A -> ε predicts a too, from FOLLOW.
law follow_clash:
  {T.ll1ByTables(10n, [Core.Production{0n, [n(1n), t(1n)]}, Core.Production{1n, [t(1n)]}, Core.Production{1n, []}], 0n) == False{} : Bool}

def follow_clash():
  {==}

# LL(1) at one nonterminal: S = X b, X = a | a c. The grammar is not LL(1), X has the
# conflict, S has none.
def partly() -> +List<Core.Production>:
  [Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}, Core.Terminal{2n}]},
   Core.Production{1n, [Core.Terminal{1n}]},
   Core.Production{1n, [Core.Terminal{1n}, Core.Terminal{3n}]}]

law partly_s_ok:
  {T.ll1AtByTables(10n, partly(), 0n, 0n) == True{} : Bool}

def partly_s_ok():
  {==}

law partly_x_conflict:
  {T.ll1AtByTables(10n, partly(), 0n, 1n) == False{} : Bool}

def partly_x_conflict():
  {==}

law partly_not_ll1:
  {T.ll1ByTables(10n, partly(), 0n) == False{} : Bool}

def partly_not_ll1():
  {==}
