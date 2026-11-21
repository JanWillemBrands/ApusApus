import Base
import ./CORE.bend as Core

# SETS OF NATURALS AND THE NONTERMINALS THAT CAN READ NOTHING, shared by the rule on
# preference cycles (PREFER.bend) and the LL(1) tables (TABLES.bend). The nullable set is
# grown (not trusted) and checked closed: closed under "a production whose items can all
# read nothing makes its nonterminal nullable".

def natIn(+x: Nat, xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(Nat.is_eq(x, y), natIn(x, rest))

def allNatIn(xs: +List<Nat>, +c: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(natIn(x, c), allNatIn(rest, c))

def joinNats(a: +List<Nat>, +b: +List<Nat>) -> +List<Nat>:
  match a:
    case Nil{}:
      b
    case Con{+x, rest}:
      x <> joinNats(rest, b)

def addIf(b: Bool, +x: Nat, +c: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      x <> c
    case False{}:
      c

# Can the item read nothing? Never a terminal, nor an occurrence that needs something.
def needNull(need: Core.Need, +x: Nat, +nulls: +List<Nat>) -> Bool:
  match need:
    case Core.Something{}:
      False{}
    case Core.Anything{}:
      natIn(x, nulls)
    case Core.Nothing{}:
      natIn(x, nulls)

def itemNull(s: Core.Sym, +nulls: +List<Nat>) -> Bool:
  match s:
    case Core.Terminal{k}:
      False{}
    case Core.Nonterminal{+x, +need}:
      needNull(need, x, nulls)

def allNull(items: +List<Core.Sym>, +nulls: +List<Nat>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{+s, rest}:
      Bool.and(itemNull(s, nulls), allNull(rest, nulls))

def nullsOnce(prods: +List<Core.Production>, +acc: +List<Nat>) -> +List<Nat>:
  match prods:
    case Nil{}:
      acc
    case Con{Core.Production{+lhs, +rhs}, rest}:
      nullsOnce(rest, addIf(Bool.and(allNull(rhs, acc), Bool.not(natIn(lhs, acc))), lhs, acc))

def growNulls(n: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>) -> +List<Nat>:
  match n:
    case 0n:
      nulls
    case 1n+(+p):
      growNulls(p, grammar, nullsOnce(grammar, nulls))

def nullsClosed(prods: +List<Core.Production>, +nulls: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(Bool.or(Bool.not(allNull(rhs, nulls)), natIn(lhs, nulls)), nullsClosed(rest, nulls))

