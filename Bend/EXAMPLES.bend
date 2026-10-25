import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PROOF.bend as Proof

# Examples. Each def below is checked by computation when this file is checked: a
# false one makes `bend EXAMPLES.bend` fail.

# EXAMPLES, from Scott and Johnstone's EBNF paper. Tokens: a = 1, b = 2, c = 3, d = 4.

def t(k: Nat) -> Spec.Item:
  Spec.Sym{Spec.Terminal{k}}

def n(id: Nat) -> Spec.Item:
  Spec.Sym{Spec.Nonterminal{id}}

def one(+item: Spec.Item) -> +List<+List<Spec.Item>>:
  [[item]]

# X ::= a {b} c on abbbc: one loop with three rounds.
def loopGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Brack{Spec.Closure{}, one(t(2n))}, t(3n)]}]

def loopTree() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{2n}]}, Spec.Pick{0n, [Spec.Leaf{2n}]}, Spec.Pick{0n, [Spec.Leaf{2n}]}]}, Spec.Leaf{3n}]}

def loopFits() -> {Spec.fits([loopTree()], loopGrammar(), [n(0n)]) == True{} : Bool}:
  {==}

def loopSpells() -> {Spec.leaves([loopTree()]) == [1n, 2n, 2n, 2n, 3n] : +List<Nat>}:
  {==}

# A pick where the closure wants a loop does not fit.
def loopNeedsLoop() -> {Spec.fits([Spec.Node{0n, [Spec.Leaf{1n}, Spec.Pick{0n, [Spec.Leaf{2n}]}, Spec.Leaf{3n}]}], loopGrammar(), [n(0n)]) == False{} : Bool}:
  {==}

# X ::= a (a b | a) (b c | c) on aabc: two trees, the ambiguity of the regular expression.
def choiceGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Brack{Spec.Group{}, [[t(1n), t(2n)], [t(1n)]]}, Spec.Brack{Spec.Group{}, [[t(2n), t(3n)], [t(3n)]]}]}]

def choiceA() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Pick{0n, [Spec.Leaf{1n}, Spec.Leaf{2n}]}, Spec.Pick{1n, [Spec.Leaf{3n}]}]}

def choiceB() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Pick{1n, [Spec.Leaf{1n}]}, Spec.Pick{0n, [Spec.Leaf{2n}, Spec.Leaf{3n}]}]}

def choiceAFits() -> {Spec.fits([choiceA()], choiceGrammar(), [n(0n)]) == True{} : Bool}:
  {==}

def choiceBFits() -> {Spec.fits([choiceB()], choiceGrammar(), [n(0n)]) == True{} : Bool}:
  {==}

def choiceASpells() -> {Spec.leaves([choiceA()]) == [1n, 1n, 2n, 3n] : +List<Nat>}:
  {==}

def choiceBSpells() -> {Spec.leaves([choiceB()]) == [1n, 1n, 2n, 3n] : +List<Nat>}:
  {==}

# S ::= {A} a,  A ::= b b | ε  on bba: infinitely many trees, from ε rounds of A.
def nullGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Closure{}, one(n(1n))}, t(1n)]},
    Spec.Production{1n, [t(2n), t(2n)]},
    Spec.Production{1n, []} ]

def emptyA() -> Spec.Tree:
  Spec.Pick{0n, [Spec.Node{2n, []}]}

def bbA() -> Spec.Tree:
  Spec.Pick{0n, [Spec.Node{1n, [Spec.Leaf{2n}, Spec.Leaf{2n}]}]}

def nullOne() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[bbA()]}, Spec.Leaf{1n}]}

def nullThree() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[emptyA(), bbA(), emptyA()]}, Spec.Leaf{1n}]}

def nullBothFit() -> {Bool.and(Spec.fits([nullOne()], nullGrammar(), [n(0n)]), Spec.fits([nullThree()], nullGrammar(), [n(0n)])) == True{} : Bool}:
  {==}

def nullOneSpells() -> {Spec.leaves([nullOne()]) == [2n, 2n, 1n] : +List<Nat>}:
  {==}

def nullThreeSpells() -> {Spec.leaves([nullThree()]) == [2n, 2n, 1n] : +List<Nat>}:
  {==}

# S ::= [A] b,  A ::= a | ε  on b: the optional skipped, or matched to an empty A.
def optGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Optional{}, one(n(1n))}, t(2n)]},
    Spec.Production{1n, [t(1n)]},
    Spec.Production{1n, []} ]

def optBothFit() -> {Bool.and(Spec.fits([Spec.Node{0n, [Spec.Skip{}, Spec.Leaf{2n}]}], optGrammar(), [n(0n)]), Spec.fits([Spec.Node{0n, [Spec.Pick{0n, [Spec.Node{2n, []}]}, Spec.Leaf{2n}]}], optGrammar(), [n(0n)])) == True{} : Bool}:
  {==}

# A positive closure needs at least one round.
def positiveNeedsRound() -> {Spec.fits([Spec.Loop{[]}], [], [Spec.Brack{Spec.Positive{}, one(t(1n))}]) == False{} : Bool}:
  {==}

# STEPS. X ::= a {b} c (production 0) on abc and abbc.
def abc() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{2n}]}]}, Spec.Leaf{3n}]}

def abbc() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{2n}]}, Spec.Pick{0n, [Spec.Leaf{2n}]}]}, Spec.Leaf{3n}]}

# a completes [1]; the loop over 1..2 completes [2]; inside it, round 1 runs b from
# the loop start 1 (slot [1, 0, 1]); c completes [3].
def abcSteps() -> {Spec.sameSet(Spec.steps(abc(), 0n), [
    Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n},
    Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 2n},
    Spec.Bsr{Spec.Slot{0n, [1n, 0n, 1n]}, 1n, 1n, 2n},
    Spec.Bsr{Spec.Slot{0n, [3n]}, 0n, 2n, 3n}]) == True{} : Bool}:
  {==}

# The second round chains on from the loop start: b over 2..3 from 1.
def abbcSteps() -> {Spec.sameSet(Spec.steps(abbc(), 0n), [
    Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n},
    Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 3n},
    Spec.Bsr{Spec.Slot{0n, [1n, 0n, 1n]}, 1n, 1n, 2n},
    Spec.Bsr{Spec.Slot{0n, [1n, 0n, 1n]}, 1n, 2n, 3n},
    Spec.Bsr{Spec.Slot{0n, [3n]}, 0n, 3n, 4n}]) == True{} : Bool}:
  {==}

# X ::= {a | a a} on aaa: three readings, and the Spec.steps tell all three apart.
def splitGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[t(1n)], [t(1n), t(1n)]]}]}]

def oneTwo() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{1n}]}, Spec.Pick{1n, [Spec.Leaf{1n}, Spec.Leaf{1n}]}]}]}

def twoOne() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[Spec.Pick{1n, [Spec.Leaf{1n}, Spec.Leaf{1n}]}, Spec.Pick{0n, [Spec.Leaf{1n}]}]}]}

def oneOneOne() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{1n}]}, Spec.Pick{0n, [Spec.Leaf{1n}]}, Spec.Pick{0n, [Spec.Leaf{1n}]}]}]}

def splitsAllFit() -> {Bool.and(Spec.fits([oneTwo()], splitGrammar(), [n(0n)]), Bool.and(Spec.fits([twoOne()], splitGrammar(), [n(0n)]), Spec.fits([oneOneOne()], splitGrammar(), [n(0n)]))) == True{} : Bool}:
  {==}

def splitsDiffer() -> {Bool.or(Spec.sameSet(Spec.steps(oneTwo(), 0n), Spec.steps(twoOne(), 0n)), Bool.or(Spec.sameSet(Spec.steps(oneTwo(), 0n), Spec.steps(oneOneOne(), 0n)), Spec.sameSet(Spec.steps(twoOne(), 0n), Spec.steps(oneOneOne(), 0n)))) == False{} : Bool}:
  {==}

# S ::= [A] b, A ::= a | ε on b: a skipped optional and an optional matched to an
# empty A share the step for [A] over 0..0, but the second also has A's own Spec.steps.
def optSkip() -> Spec.Tree:
  Spec.Node{0n, [Spec.Skip{}, Spec.Leaf{2n}]}

def optEmpty() -> Spec.Tree:
  Spec.Node{0n, [Spec.Pick{0n, [Spec.Node{2n, []}]}, Spec.Leaf{2n}]}

def optSkipSteps() -> {Spec.sameSet(Spec.steps(optSkip(), 0n), [
    Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n},
    Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 0n, 1n}]) == True{} : Bool}:
  {==}

def optEmptySteps() -> {Spec.sameSet(Spec.steps(optEmpty(), 0n), [
    Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 0n},
    Spec.Bsr{Spec.Slot{0n, [0n, 0n, 1n]}, 0n, 0n, 0n},
    Spec.Bsr{Spec.Slot{2n, [0n]}, 0n, 0n, 0n},
    Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 0n, 1n}]) == True{} : Bool}:
  {==}

# ---- The GLL engine on the examples ----

def fuel() -> Nat:
  4000n

def run(+g: +List<Spec.Production>, +input: +List<Nat>) -> Gll.GRun:
  Gll.parse(fuel(), g, 0n, input)

# Every step of the tree is among the parser's steps.
def covers(+g: +List<Spec.Production>, +input: +List<Nat>, +tree: Spec.Tree) -> Bool:
  Spec.allIn(Spec.steps(tree, 0n), Gll.yieldsOf(run(g, input)))

def accepts(+g: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  Gll.accepts(run(g, input), 0n, List.length(&2, Nat, input))

# X ::= a {b} c
def loopOk() -> {Bool.and(accepts(loopGrammar(), [1n, 2n, 2n, 2n, 3n]), covers(loopGrammar(), [1n, 2n, 2n, 2n, 3n], loopTree())) == True{} : Bool}:
  {==}

def loopRejects() -> {accepts(loopGrammar(), [1n, 2n, 2n]) == False{} : Bool}:
  {==}

def loopEmpty() -> {accepts(loopGrammar(), [1n, 3n]) == True{} : Bool}:
  {==}

# X ::= a (a b | a) (b c | c): both readings of aabc.
def choiceOk() -> {Bool.and(accepts(choiceGrammar(), [1n, 1n, 2n, 3n]), Bool.and(covers(choiceGrammar(), [1n, 1n, 2n, 3n], choiceA()), covers(choiceGrammar(), [1n, 1n, 2n, 3n], choiceB()))) == True{} : Bool}:
  {==}

# S ::= {A} a, A ::= b b | ε: two of the infinitely many trees of bba.
def nullOk() -> {Bool.and(accepts(nullGrammar(), [2n, 2n, 1n]), Bool.and(covers(nullGrammar(), [2n, 2n, 1n], nullOne()), covers(nullGrammar(), [2n, 2n, 1n], nullThree()))) == True{} : Bool}:
  {==}

# S ::= [A] b, A ::= a | ε: both readings of b.
def optOk() -> {Bool.and(accepts(optGrammar(), [2n]), Bool.and(covers(optGrammar(), [2n], optSkip()), covers(optGrammar(), [2n], optEmpty()))) == True{} : Bool}:
  {==}

# X ::= {a | a a}: all three readings of aaa.
def splitOk() -> {Bool.and(accepts(splitGrammar(), [1n, 1n, 1n]), Bool.and(covers(splitGrammar(), [1n, 1n, 1n], oneTwo()), Bool.and(covers(splitGrammar(), [1n, 1n, 1n], twoOne()), covers(splitGrammar(), [1n, 1n, 1n], oneOneOne())))) == True{} : Bool}:
  {==}

# Left recursion: E ::= E + a | a, with + = 5.
def leftGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [n(0n), t(5n), t(1n)]},
    Spec.Production{0n, [t(1n)]} ]

def leftTree() -> Spec.Tree:
  Spec.Node{0n, [Spec.Node{0n, [Spec.Node{1n, [Spec.Leaf{1n}]}, Spec.Leaf{5n}, Spec.Leaf{1n}]}, Spec.Leaf{5n}, Spec.Leaf{1n}]}

def leftFits() -> {Spec.fits([leftTree()], leftGrammar(), [n(0n)]) == True{} : Bool}:
  {==}

def leftOk() -> {Bool.and(accepts(leftGrammar(), [1n, 5n, 1n, 5n, 1n]), covers(leftGrammar(), [1n, 5n, 1n, 5n, 1n], leftTree())) == True{} : Bool}:
  {==}

def leftRejects() -> {accepts(leftGrammar(), [1n, 5n, 5n, 1n]) == False{} : Bool}:
  {==}

# ---- The closedness check ----

def stateOf(r: Gll.GRun) -> Gll.GState:
  match r:
    case Gll.GDone{s}:
      s
    case Gll.OutOfFuel{s}:
      s

def closedFor(+g: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  Check.closed(g, input, stateOf(run(g, input)))

# Drop the most recent step, or the most recent pop: the state is no longer closed.
def dropStep(s: Gll.GState) -> Gll.GState:
  match s:
    case Gll.GState{seen, todo, cs, rs, ps, Con{y, ys}}:
      Gll.GState{seen, todo, cs, rs, ps, ys}
    case Gll.GState{seen, todo, cs, rs, ps, Nil{}}:
      Gll.GState{seen, todo, cs, rs, ps, []}

def dropPop(s: Gll.GState) -> Gll.GState:
  match s:
    case Gll.GState{seen, todo, cs, rs, Con{p, ps}, ys}:
      Gll.GState{seen, todo, cs, rs, ps, ys}
    case Gll.GState{seen, todo, cs, rs, Nil{}, ys}:
      Gll.GState{seen, todo, cs, rs, [], ys}

def allClosed() -> {Bool.and(closedFor(loopGrammar(), [1n, 2n, 2n, 2n, 3n]),
    Bool.and(closedFor(choiceGrammar(), [1n, 1n, 2n, 3n]),
    Bool.and(closedFor(nullGrammar(), [2n, 2n, 1n]),
    Bool.and(closedFor(optGrammar(), [2n]),
    Bool.and(closedFor(splitGrammar(), [1n, 1n, 1n]),
    Bool.and(closedFor(leftGrammar(), [1n, 5n, 1n, 5n, 1n]),
             closedFor(loopGrammar(), [1n, 2n, 2n])))))))  == True{} : Bool}:
  {==}

def missingStep() -> {Check.closed(leftGrammar(), [1n, 5n, 1n, 5n, 1n], dropStep(stateOf(run(leftGrammar(), [1n, 5n, 1n, 5n, 1n])))) == False{} : Bool}:
  {==}

def missingPop() -> {Check.closed(nullGrammar(), [2n, 2n, 1n], dropPop(stateOf(run(nullGrammar(), [2n, 2n, 1n])))) == False{} : Bool}:
  {==}

def isSome(m: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      True{}

# The checked parser hands out its steps on every example.
def checkedEverywhere() -> {Bool.and(isSome(Check.checkedSteps(fuel(), loopGrammar(), 0n, [1n, 2n, 2n, 2n, 3n])),
    Bool.and(isSome(Check.checkedSteps(fuel(), nullGrammar(), 0n, [2n, 2n, 1n])),
    Bool.and(isSome(Check.checkedSteps(fuel(), splitGrammar(), 0n, [1n, 1n, 1n])),
             isSome(Check.checkedSteps(fuel(), leftGrammar(), 0n, [1n, 5n, 1n, 5n, 1n]))))) == True{} : Bool}:
  {==}
