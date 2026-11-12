import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./EXACT.bend as Exact
import ./FIRST.bend as First
import ./LL1.bend as LL1
import ./PSUPPORT.bend as PS

def t(k: Nat) -> Spec.Item:
  Spec.Sym{Spec.Terminal{k}}

def n(id: Nat) -> Spec.Item:
  Spec.Sym{Spec.Nonterminal{id}}

def one(+item: Spec.Item) -> +List<+List<Spec.Item>>:
  [[item]]

def tablesOr(m: Maybe<&2, Gll.Tables>) -> Gll.Tables:
  match m:
    case Some{t}:
      t
    case None{}:
      Gll.Tables{[], [], []}

def setOr(m: Maybe<&2, +List<Spec.Bsr>>) -> +List<Spec.Bsr>:
  match m:
    case Some{s}:
      s
    case None{}:
      []

def isSome(m: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m:
    case Some{s}:
      True{}
    case None{}:
      False{}

type Row is Data:
  Row{ll1: Bool, answered: Bool, exactSame: Bool, ll: Nat, exact: Nat}

def row(+g: +List<Spec.Production>, +input: +List<Nat>) -> Row:
  +tb = tablesOr(First.tablesOf(Nat.add(Nat.mul(First.ntCount(g), 4n), 4n), g, 0n))
  +ll = PS.llSteps(4000n, g, 0n, input)
  +ex = setOr(Exact.exactSteps(4000n, g, 0n, input))
  Row{LL1.ll1ByTables(g, 0n, tb), isSome(ll), Spec.sameSet(setOr(ll), ex), List.length(&2, Spec.Bsr, setOr(ll)), List.length(&2, Spec.Bsr, ex)}

def deadGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[t(1n)], [Spec.Eps{}]]}, t(2n)]}]

def posGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Positive{}, [[t(1n)], [Spec.Eps{}]]}, t(2n)]}]

def loopGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Brack{Spec.Closure{}, one(t(2n))}, t(3n)]}]

# X ::= a (a b | a) (b c | c)
def choiceGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Brack{Spec.Group{}, [[t(1n), t(2n)], [t(1n)]]}, Spec.Brack{Spec.Group{}, [[t(2n), t(3n)], [t(3n)]]}]}]

# S ::= {A} a,  A ::= b b | ε
def nullGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Closure{}, one(n(1n))}, t(1n)]},
    Spec.Production{1n, [t(2n), t(2n)]},
    Spec.Production{1n, []} ]

# S ::= [A] b,  A ::= a | ε
def optGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Optional{}, one(n(1n))}, t(2n)]},
    Spec.Production{1n, [t(1n)]},
    Spec.Production{1n, []} ]

# X ::= {a | a a}
def splitGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[t(1n)], [t(1n), t(1n)]]}]}]

# E ::= E + a | a
def leftGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [n(0n), t(5n), t(1n)]},
    Spec.Production{0n, [t(1n)]} ]

# An LL(1) expression grammar: E ::= T { + T },  T ::= F { * F },  F ::= ( E ) | a.
# Tokens: a = 1, + = 5, * = 6, ( = 7, ) = 8.
def exprGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [n(1n), Spec.Brack{Spec.Closure{}, one(Spec.Brack{Spec.Group{}, [[t(5n), n(1n)]]})}]},
    Spec.Production{1n, [n(2n), Spec.Brack{Spec.Closure{}, one(Spec.Brack{Spec.Group{}, [[t(6n), n(2n)]]})}]},
    Spec.Production{2n, [t(7n), n(0n), t(8n)]},
    Spec.Production{2n, [t(1n)]} ]

# a * ( a + a ) + a
def exprInput() -> +List<Nat>:
  [1n, 6n, 7n, 1n, 5n, 1n, 8n, 5n, 1n]

def main() -> +List<Row>:
  [ row(loopGrammar(), [1n, 2n, 2n, 2n, 3n]),
    row(choiceGrammar(), [1n, 1n, 2n, 3n]),
    row(nullGrammar(), [2n, 2n, 1n]),
    row(optGrammar(), [2n]),
    row(splitGrammar(), [1n, 1n, 1n]),
    row(leftGrammar(), [1n, 5n, 1n, 5n, 1n]),
    row(exprGrammar(), exprInput()),
    row(deadGrammar(), [2n]),
    row(deadGrammar(), [1n, 1n, 2n]),
    row(posGrammar(), [2n]),
    row(posGrammar(), [1n, 1n, 2n]) ]
