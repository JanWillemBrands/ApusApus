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
