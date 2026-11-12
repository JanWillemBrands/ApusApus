import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./EXACT.bend as Exact
import ./FIRST.bend as First

# PREDICTION ON EXAMPLES (scratch). For each grammar and input: the facts of the plain
# engine and of the predicting one, and whether the predicting checked parser answered
# with a set between the exact set and the plain one.

def t(k: Nat) -> Spec.Item:
  Spec.Sym{Spec.Terminal{k}}

def n(id: Nat) -> Spec.Item:
  Spec.Sym{Spec.Nonterminal{id}}

def one(+item: Spec.Item) -> +List<+List<Spec.Item>>:
  [[item]]

type Facts is Data:
  Facts{descs: Nat, clusters: Nat, returns: Nat, pops: Nat, steps: Nat}

type Report is Data:
  Report{plain: Facts, predicted: Facts, exact: Nat, ok: Bool}

def fuel() -> Nat:
  4000n

def factsOf(r: Gll.GRun) -> Facts:
  match r:
    case Gll.GDone{Gll.GState{seen, todo, cs, rs, ps, ys}}:
      Facts{List.length(&2, Gll.Desc, seen), List.length(&2, Gll.CKey, cs), List.length(&2, Gll.Ret, rs), List.length(&2, Gll.Pop, ps), List.length(&2, Spec.Bsr, ys)}
    case Gll.OutOfFuel{s}:
      Facts{0n, 0n, 0n, 0n, 0n}

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

def predOf(+g: +List<Spec.Production>) -> Gll.Pred:
  Gll.Predict{tablesOr(First.tablesOf(Nat.add(Nat.mul(First.ntCount(g), 4n), 4n), g, 0n))}

def report(+g: +List<Spec.Production>, +input: +List<Nat>) -> Report:
  +plain = Check.checkedSteps(fuel(), g, 0n, input)
  +pred = Check.predictedSteps(fuel(), g, 0n, input)
  +exact = setOr(Exact.exactSteps(fuel(), g, 0n, input))
  +ok = Bool.and(isSome(pred), Bool.and(Spec.allIn(exact, setOr(pred)), Spec.allIn(setOr(pred), setOr(plain))))
  Report{factsOf(Gll.parse(fuel(), g, 0n, input)), factsOf(Gll.parseWith(fuel(), predOf(g), g, 0n, input)), List.length(&2, Spec.Bsr, exact), ok}

# X ::= a {b} c
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

def main() -> +List<Report>:
  [ report(loopGrammar(), [1n, 2n, 2n, 2n, 3n]),
    report(choiceGrammar(), [1n, 1n, 2n, 3n]),
    report(nullGrammar(), [2n, 2n, 1n]),
    report(optGrammar(), [2n]),
    report(splitGrammar(), [1n, 1n, 1n]),
    report(leftGrammar(), [1n, 5n, 1n, 5n, 1n]),
    report(exprGrammar(), exprInput()) ]
