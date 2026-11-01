import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./UNBEATEN.bend as Unb
import ./EXTENT.bend as Extent
import ./PROOF.bend as Proof
import ./LEMMAS.bend as Lemma
import ./FITS.bend as Fits

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

# S ::= {A} a,  A ::= b b | ε  on bba: one tree. Rounds where A derives ε could be
# removed, so a tree with them does not fit.
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

def nullOneFits() -> {Bool.and(Spec.fits([nullOne()], nullGrammar(), [n(0n)]), Bool.not(Spec.fits([nullThree()], nullGrammar(), [n(0n)]))) == True{} : Bool}:
  {==}

def nullOneSpells() -> {Spec.leaves([nullOne()]) == [2n, 2n, 1n] : +List<Nat>}:
  {==}

def nullThreeSpells() -> {Spec.leaves([nullThree()]) == [2n, 2n, 1n] : +List<Nat>}:
  {==}

# S ::= [A] b,  A ::= a | ε  on b: the optional skipped. Taking it for an empty A
# reads nothing, so that tree does not fit.
def optGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Optional{}, one(n(1n))}, t(2n)]},
    Spec.Production{1n, [t(1n)]},
    Spec.Production{1n, []} ]

def optSkipFits() -> {Bool.and(Spec.fits([Spec.Node{0n, [Spec.Skip{}, Spec.Leaf{2n}]}], optGrammar(), [n(0n)]), Bool.not(Spec.fits([Spec.Node{0n, [Spec.Pick{0n, [Spec.Node{2n, []}]}, Spec.Leaf{2n}]}], optGrammar(), [n(0n)]))) == True{} : Bool}:
  {==}

# A positive closure needs at least one round.
def positiveNeedsRound() -> {Spec.fits([Spec.Loop{[]}], [], [Spec.Brack{Spec.Positive{}, one(t(1n))}]) == False{} : Bool}:
  {==}

# ε is an item, matched by a skip: S ::= a ε b on ab.
def epsGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [t(1n), Spec.Eps{}, t(2n)]}]

def epsTree() -> Spec.Tree:
  Spec.Node{0n, [Spec.Leaf{1n}, Spec.Skip{}, Spec.Leaf{2n}]}

def epsFits() -> {Spec.fits([epsTree()], epsGrammar(), [n(0n)]) == True{} : Bool}:
  {==}

# It records a step of its own, from 1 to 1, like Swift Apus's EPS items.
def epsSteps() -> {Spec.sameSet(Spec.steps(epsTree(), 0n), [
    Spec.Bsr{Spec.Slot{0n, [1n]}, 0n, 0n, 1n},
    Spec.Bsr{Spec.Slot{0n, [2n]}, 0n, 1n, 1n},
    Spec.Bsr{Spec.Slot{0n, [3n]}, 0n, 1n, 2n}]) == True{} : Bool}:
  {==}

# S ::= < a | ε > on nothing: one empty round, the τ of ( τ ) { τ }; not two.
def posGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Positive{}, [[t(1n)], [Spec.Eps{}]]}]}]

def emptyRound() -> Spec.Tree:
  Spec.Pick{1n, [Spec.Skip{}]}

def posOne() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[emptyRound()]}]}

def posOneFits() -> {Bool.and(Spec.fits([posOne()], posGrammar(), [n(0n)]), Bool.not(Spec.fits([Spec.Node{0n, [Spec.Loop{[emptyRound(), emptyRound()]}]}], posGrammar(), [n(0n)]))) == True{} : Bool}:
  {==}

# S ::= { a | ε } on nothing: no rounds; an empty round does not fit.
def cloGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[t(1n)], [Spec.Eps{}]]}]}]

def cloNone() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[]}]}

def cloNoneFits() -> {Bool.and(Spec.fits([cloNone()], cloGrammar(), [n(0n)]), Bool.not(Spec.fits([Spec.Node{0n, [Spec.Loop{[emptyRound()]}]}], cloGrammar(), [n(0n)]))) == True{} : Bool}:
  {==}

# S ::= ( ε | A ), A ::= ε on nothing: a choice between empty alternatives stays: two trees.
def groupGrammar() -> +List<Spec.Production>:
  [ Spec.Production{0n, [Spec.Brack{Spec.Group{}, [[Spec.Eps{}], [n(1n)]]}]},
    Spec.Production{1n, [Spec.Eps{}]} ]

def groupEps() -> Spec.Tree:
  Spec.Node{0n, [Spec.Pick{0n, [Spec.Skip{}]}]}

def groupA() -> Spec.Tree:
  Spec.Node{0n, [Spec.Pick{1n, [Spec.Node{1n, [Spec.Skip{}]}]}]}

def groupBothFit() -> {Bool.and(Spec.fits([groupEps()], groupGrammar(), [n(0n)]), Spec.fits([groupA()], groupGrammar(), [n(0n)])) == True{} : Bool}:
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
# empty A share the step for [A] over 0..0, but the second also has A's own steps.
# Only the first is a parse tree.
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

# S ::= {A} a, A ::= b b | ε: the engine also builds the rounds where A derives ε.
def nullOk() -> {Bool.and(accepts(nullGrammar(), [2n, 2n, 1n]), Bool.and(covers(nullGrammar(), [2n, 2n, 1n], nullOne()), covers(nullGrammar(), [2n, 2n, 1n], nullThree()))) == True{} : Bool}:
  {==}

# S ::= [A] b, A ::= a | ε: the engine also takes the optional for an empty A.
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

# ---- The exact parser ----

def stepsOr(m: Maybe<&2, +List<Spec.Bsr>>) -> +List<Spec.Bsr>:
  match m:
    case Some{xs}:
      xs
    case None{}:
      []

def exact(+g: +List<Spec.Production>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  stepsOr(Exact.exactSteps(fuel(), g, 0n, input))

# The exact set is exactly the steps of the parse trees: for a+a+a the one dead step
# the engine made is gone; for the ambiguous examples it is the union of all readings.
def exactLeft() -> {Spec.sameSet(exact(leftGrammar(), [1n, 5n, 1n, 5n, 1n]), Spec.steps(leftTree(), 0n)) == True{} : Bool}:
  {==}

def exactLoop() -> {Spec.sameSet(exact(loopGrammar(), [1n, 2n, 2n, 2n, 3n]), Spec.steps(loopTree(), 0n)) == True{} : Bool}:
  {==}

def exactChoice() -> {Spec.sameSet(exact(choiceGrammar(), [1n, 1n, 2n, 3n]), List.append(&2, Spec.Bsr, Spec.steps(choiceA(), 0n), Spec.steps(choiceB(), 0n))) == True{} : Bool}:
  {==}

def exactSplit() -> {Spec.sameSet(exact(splitGrammar(), [1n, 1n, 1n]), List.append(&2, Spec.Bsr, Spec.steps(oneTwo(), 0n), List.append(&2, Spec.Bsr, Spec.steps(twoOne(), 0n), Spec.steps(oneOneOne(), 0n)))) == True{} : Bool}:
  {==}

# Rounds and optionals that read nothing are gone: one tree each.
def exactOpt() -> {Spec.sameSet(exact(optGrammar(), [2n]), Spec.steps(optSkip(), 0n)) == True{} : Bool}:
  {==}

def exactNull() -> {Spec.sameSet(exact(nullGrammar(), [2n, 2n, 1n]), Spec.steps(nullOne(), 0n)) == True{} : Bool}:
  {==}

def exactEps() -> {Spec.sameSet(exact(epsGrammar(), [1n, 2n]), Spec.steps(epsTree(), 0n)) == True{} : Bool}:
  {==}

def exactPos() -> {Spec.sameSet(exact(posGrammar(), []), Spec.steps(posOne(), 0n)) == True{} : Bool}:
  {==}

# On a, only the round that reads a: the empty round's own bracket step was dead wood.
def exactPosA() -> {Spec.sameSet(exact(posGrammar(), [1n]), Spec.steps(Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Leaf{1n}]}]}]}, 0n)) == True{} : Bool}:
  {==}

def exactClo() -> {Spec.sameSet(exact(cloGrammar(), []), Spec.steps(cloNone(), 0n)) == True{} : Bool}:
  {==}

# A choice between empty alternatives is kept: both trees.
def exactGroup() -> {Spec.sameSet(exact(groupGrammar(), []), List.append(&2, Spec.Bsr, Spec.steps(groupEps(), 0n), Spec.steps(groupA(), 0n))) == True{} : Bool}:
  {==}

# No parse tree, no steps.
def exactRejects() -> {exact(leftGrammar(), [1n, 5n, 5n, 1n]) == [] : +List<Spec.Bsr>}:
  {==}

# The witness check refuses a step that is in no parse tree.
def bogus() -> Spec.Bsr:
  Spec.Bsr{Spec.Slot{1n, [1n]}, 0n, 2n, 3n}

def witnessRefuses() -> {Exact.witnessed(leftGrammar(), 0n, [1n, 5n, 1n, 5n, 1n], bogus() <> Spec.steps(leftTree(), 0n), [leftTree()]) == False{} : Bool}:
  {==}

# ---- Preferences ----

# S ::= @prefer A | B, A ::= t, B ::= t, on t. Productions: 0 is S ::= A, 1 is S ::= B,
# 2 is A ::= t, 3 is B ::= t. Nonterminals: S = 0, A = 1, B = 2.
def preferGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n)]}, Spec.Production{0n, [n(2n)]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}]

def preferMarks() -> +List<Spec.Mark>:
  [Spec.ProdMark{0n, Spec.Preferred{}}]

def viaA() -> Spec.Tree:
  Spec.Node{0n, [Spec.Node{2n, [Spec.Leaf{1n}]}]}

def viaB() -> Spec.Tree:
  Spec.Node{1n, [Spec.Node{3n, [Spec.Leaf{1n}]}]}

# The tree through B is a parse tree, but beaten: S ::= A outranks it on t.
def viaBRejected(sel: Spec.UnbeatenTree(preferGrammar(), [], preferMarks(), 0n, [1n], viaB())) -> Empty:
  match sel:
    case (adm, (notBeaten, rest)):
      notBeaten((0n, ({==}, ([Spec.Node{2n, [Spec.Leaf{1n}]}], ({==}, ({==}, ({==}, (Unit{}, (Unit{}, (Unit{}, Unit{}))))))))))

def noRivalOfSAt(q2: Nat, cond: {Bool.and(Spec.lhsIs(preferGrammar(), q2, 0n), Spec.outranks(Spec.prodRank(preferMarks(), q2), Spec.prodRank(preferMarks(), 0n))) == True{} : Bool}) -> Empty:
  match q2:
    case 0n:
      Lemma.false_is_not_true(cond)
    case 1n+p:
      match p:
        case 0n:
          Lemma.false_is_not_true(cond)
        case 1n+p2:
          match p2:
            case 0n:
              Lemma.false_is_not_true(cond)
            case 1n+p3:
              match p3:
                case 0n:
                  Lemma.false_is_not_true(cond)
                case 1n+p4:
                  Lemma.false_is_not_true(cond)

# No production of S outranks the preferred S ::= A.
def noRivalOfS(rival: Spec.ProdRival(preferGrammar(), [], preferMarks(), 0n, 0n, [1n], [], [0n])) -> Empty:
  match rival:
    case (q2, (cond, der)):
      noRivalOfSAt(q2, cond)

# A has one production, so nothing outranks it.
def noRivalOfAAt(q2: Nat, cond: {Bool.and(Spec.lhsIs(preferGrammar(), q2, 1n), Spec.outranks(Spec.prodRank(preferMarks(), q2), Spec.prodRank(preferMarks(), 2n))) == True{} : Bool}) -> Empty:
  match q2:
    case 0n:
      Lemma.false_is_not_true(cond)
    case 1n+p:
      match p:
        case 0n:
          Lemma.false_is_not_true(cond)
        case 1n+p2:
          match p2:
            case 0n:
              Lemma.false_is_not_true(cond)
            case 1n+p3:
              match p3:
                case 0n:
                  Lemma.false_is_not_true(cond)
                case 1n+p4:
                  Lemma.false_is_not_true(cond)

def noRivalOfA(rival: Spec.ProdRival(preferGrammar(), [], preferMarks(), 1n, 2n, [1n], [], [1n, 0n])) -> Empty:
  match rival:
    case (q2, (cond, der)):
      noRivalOfAAt(q2, cond)

# The tree through A is unbeaten.
def viaASelected() -> Spec.UnbeatenTree(preferGrammar(), [], preferMarks(), 0n, [1n], viaA()):
  (({==}, ({==}, (Unit{}, ((Unit{}, (Unit{}, Unit{})), Unit{})))), (r => noRivalOfS(r), ((r => noRivalOfA(r), (Unit{}, Unit{})), Unit{})))

# A ::= @prefer A | t, on t. Productions: 0 is A ::= A, 1 is A ::= t; A = 0. Every tree
# ends in A -> t. The preferred A -> A derives t only by coming back to A over t, so it is
# no rival, and A -> t is unbeaten: the preference does not remove every tree.
def cycleGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(0n)]}, Spec.Production{0n, [t(1n)]}]

def cycleMarks() -> +List<Spec.Mark>:
  [Spec.ProdMark{0n, Spec.Preferred{}}]

# A forest for A ::= A over t has a node of A over t, so it revisits A.
def cycleRevisits(+q: Nat, +ch: +List<Spec.Tree>,
    fit: {Bool.and(Bool.and(Spec.lhsIs(cycleGrammar(), q, 0n), Spec.fits(ch, cycleGrammar(), Spec.rhsOf(cycleGrammar(), q))), True{}) == True{} : Bool},
    spell: {List.append(&2, Nat, Spec.leaves(ch), []) == [1n] : +List<Nat>},
    clean: {Spec.revisits(cycleGrammar(), [Spec.Node{q, ch}], [0n], [1n]) == False{} : Bool}) -> Empty:
  +g = cycleGrammar()
  +both = Lemma.and_true_left(Bool.and(Spec.lhsIs(g, q, 0n), Spec.fits(ch, g, Spec.rhsOf(g, q))), True{}, fit)
  +lhsOk = Lemma.and_true_left(Spec.lhsIs(g, q, 0n), Spec.fits(ch, g, Spec.rhsOf(g, q)), both)
  +leavesEq = Equal.trans(+List<Nat>, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), [1n], Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))), spell)
  +pathOk = Equal.cong(+List<Nat>, Bool, v => Spec.pathEq(v, [1n]), [1n], Spec.leaves(ch), Equal.sym(+List<Nat>, Spec.leaves(ch), [1n], leavesEq))
  +among = Spec.lhsAmong(g, q, [0n])
  +amongOk = Lemma.or_true_left_intro(Spec.lhsIs(g, q, 0n), False{}, lhsOk)
  +hit = Bool.and(among, Spec.pathEq(Spec.leaves(ch), [1n]))
  +hitOk = Lemma.and_true_intro(among, Spec.pathEq(Spec.leaves(ch), [1n]), amongOk, Equal.sym(Bool, True{}, Spec.pathEq(Spec.leaves(ch), [1n]), pathOk))
  +inner = Bool.or(hit, Spec.revisits(g, ch, [0n], [1n]))
  +whole = Lemma.or_true_left_intro(inner, False{}, Lemma.or_true_left_intro(hit, Spec.revisits(g, ch, [0n], [1n]), hitOk))
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, Bool.or(inner, False{}), False{}, Equal.sym(Bool, Bool.or(inner, False{}), True{}, whole), clean))

def cycleForest(forest: +List<Spec.Tree>,
    fit: {Spec.fits(forest, cycleGrammar(), [n(0n)]) == True{} : Bool},
    spell: {Spec.leaves(forest) == [1n] : +List<Nat>},
    clean: {Spec.revisits(cycleGrammar(), forest, [0n], [1n]) == False{} : Bool}) -> Empty:
  match forest:
    case Nil{}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Node{+q, +ch}, rest}:
      match rest:
        case Nil{}:
          cycleRevisits(q, ch, fit, spell, clean)
        case Con{r, rr}:
          Fits.fits_cons_nil(r, rr, cycleGrammar(), Lemma.and_true_right_side(Bool.and(Spec.lhsIs(cycleGrammar(), q, 0n), Spec.fits(ch, cycleGrammar(), Spec.rhsOf(cycleGrammar(), q))), Spec.fits(r <> rr, cycleGrammar(), []), fit))
    case Con{Spec.Leaf{k}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Pick{a, ch}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Skip{}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Loop{rs}, rest}:
      Lemma.false_is_not_true(fit)

def cycleNoRivalAt(q2: Nat,
    cond: {Bool.and(Spec.lhsIs(cycleGrammar(), q2, 0n), Spec.outranks(Spec.prodRank(cycleMarks(), q2), Spec.prodRank(cycleMarks(), 1n))) == True{} : Bool},
    der: Spec.DerivesOnce(cycleGrammar(), [], Spec.rhsOf(cycleGrammar(), q2), [], q2, [], [1n], [], [0n])) -> Empty:
  match q2:
    case 0n:
      match der:
        case (forest, (fit, (spell, (clean, rules)))):
          cycleForest(forest, fit, spell, clean)
    case 1n+p:
      match p:
        case 0n:
          Lemma.false_is_not_true(cond)
        case 1n+p2:
          Lemma.false_is_not_true(cond)

def cycleNoRival(rival: Spec.ProdRival(cycleGrammar(), [], cycleMarks(), 0n, 1n, [1n], [], [0n])) -> Empty:
  match rival:
    case (q2, (cond, der)):
      cycleNoRivalAt(q2, cond, der)

# So A -> t is unbeaten.
def cycleSelected() -> Spec.UnbeatenTree(cycleGrammar(), [], cycleMarks(), 0n, [1n], Spec.Node{1n, [Spec.Leaf{1n}]}):
  (({==}, ({==}, (Unit{}, (Unit{}, Unit{})))), (r => cycleNoRival(r), (Unit{}, Unit{})))

# X ::= @prefer Y | t, Y ::= @prefer X | t, on t: a cycle of two. Productions: 0 is
# X ::= Y, 1 is X ::= t, 2 is Y ::= X, 3 is Y ::= t; X = 0, Y = 1. The tree X -> t loses
# to Y -> t. In X -> Y -> t, the rival Y ::= X of Y -> t would come back to X, which is
# above it over the same tokens, so it does not count, and the tree is unbeaten.
def pairGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n)]}, Spec.Production{0n, [t(1n)]}, Spec.Production{1n, [n(0n)]}, Spec.Production{1n, [t(1n)]}]

def pairMarks() -> +List<Spec.Mark>:
  [Spec.ProdMark{0n, Spec.Preferred{}}, Spec.ProdMark{2n, Spec.Preferred{}}]

# X -> t is beaten: Y -> t is a rival, and does not come back to X.
def pairDirectRejected(sel: Spec.UnbeatenTree(pairGrammar(), [], pairMarks(), 0n, [1n], Spec.Node{1n, [Spec.Leaf{1n}]})) -> Empty:
  match sel:
    case (adm, (notBeaten, rest)):
      notBeaten((0n, ({==}, ([Spec.Node{3n, [Spec.Leaf{1n}]}], ({==}, ({==}, ({==}, (Unit{}, (Unit{}, (Unit{}, Unit{}))))))))))

# Nothing outranks X ::= Y, which is preferred.
def pairNoRivalOfXAt(q2: Nat, cond: {Bool.and(Spec.lhsIs(pairGrammar(), q2, 0n), Spec.outranks(Spec.prodRank(pairMarks(), q2), Spec.prodRank(pairMarks(), 0n))) == True{} : Bool}) -> Empty:
  match q2:
    case 0n:
      Lemma.false_is_not_true(cond)
    case 1n+p:
      match p:
        case 0n:
          Lemma.false_is_not_true(cond)
        case 1n+p2:
          match p2:
            case 0n:
              Lemma.false_is_not_true(cond)
            case 1n+p3:
              match p3:
                case 0n:
                  Lemma.false_is_not_true(cond)
                case 1n+p4:
                  Lemma.false_is_not_true(cond)

def pairNoRivalOfX(rival: Spec.ProdRival(pairGrammar(), [], pairMarks(), 0n, 0n, [1n], [], [0n])) -> Empty:
  match rival:
    case (q2, (cond, der)):
      pairNoRivalOfXAt(q2, cond)

# A forest for Y ::= X over t has a node of X over t, and X is above.
def pairRevisits(+q: Nat, +ch: +List<Spec.Tree>,
    fit: {Bool.and(Bool.and(Spec.lhsIs(pairGrammar(), q, 0n), Spec.fits(ch, pairGrammar(), Spec.rhsOf(pairGrammar(), q))), True{}) == True{} : Bool},
    spell: {List.append(&2, Nat, Spec.leaves(ch), []) == [1n] : +List<Nat>},
    clean: {Spec.revisits(pairGrammar(), [Spec.Node{q, ch}], [1n, 0n], [1n]) == False{} : Bool}) -> Empty:
  +g = pairGrammar()
  +both = Lemma.and_true_left(Bool.and(Spec.lhsIs(g, q, 0n), Spec.fits(ch, g, Spec.rhsOf(g, q))), True{}, fit)
  +lhsOk = Lemma.and_true_left(Spec.lhsIs(g, q, 0n), Spec.fits(ch, g, Spec.rhsOf(g, q)), both)
  +leavesEq = Equal.trans(+List<Nat>, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), [1n], Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))), spell)
  +pathOk = Equal.cong(+List<Nat>, Bool, v => Spec.pathEq(v, [1n]), [1n], Spec.leaves(ch), Equal.sym(+List<Nat>, Spec.leaves(ch), [1n], leavesEq))
  +among = Spec.lhsAmong(g, q, [1n, 0n])
  +amongOk = Lemma.or_true_right_intro(Spec.lhsIs(g, q, 1n), Bool.or(Spec.lhsIs(g, q, 0n), False{}), Lemma.or_true_left_intro(Spec.lhsIs(g, q, 0n), False{}, lhsOk))
  +hit = Bool.and(among, Spec.pathEq(Spec.leaves(ch), [1n]))
  +hitOk = Lemma.and_true_intro(among, Spec.pathEq(Spec.leaves(ch), [1n]), amongOk, Equal.sym(Bool, True{}, Spec.pathEq(Spec.leaves(ch), [1n]), pathOk))
  +inner = Bool.or(hit, Spec.revisits(g, ch, [1n, 0n], [1n]))
  +whole = Lemma.or_true_left_intro(inner, False{}, Lemma.or_true_left_intro(hit, Spec.revisits(g, ch, [1n, 0n], [1n]), hitOk))
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, Bool.or(inner, False{}), False{}, Equal.sym(Bool, Bool.or(inner, False{}), True{}, whole), clean))

def pairForest(forest: +List<Spec.Tree>,
    fit: {Spec.fits(forest, pairGrammar(), [n(0n)]) == True{} : Bool},
    spell: {Spec.leaves(forest) == [1n] : +List<Nat>},
    clean: {Spec.revisits(pairGrammar(), forest, [1n, 0n], [1n]) == False{} : Bool}) -> Empty:
  match forest:
    case Nil{}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Node{+q, +ch}, rest}:
      match rest:
        case Nil{}:
          pairRevisits(q, ch, fit, spell, clean)
        case Con{r, rr}:
          Fits.fits_cons_nil(r, rr, pairGrammar(), Lemma.and_true_right_side(Bool.and(Spec.lhsIs(pairGrammar(), q, 0n), Spec.fits(ch, pairGrammar(), Spec.rhsOf(pairGrammar(), q))), Spec.fits(r <> rr, pairGrammar(), []), fit))
    case Con{Spec.Leaf{k}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Pick{a, ch}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Skip{}, rest}:
      Lemma.false_is_not_true(fit)
    case Con{Spec.Loop{rs}, rest}:
      Lemma.false_is_not_true(fit)

# The only rival of Y -> t below X is Y ::= X, which comes back to X.
def pairNoRivalOfYAt(q2: Nat,
    cond: {Bool.and(Spec.lhsIs(pairGrammar(), q2, 1n), Spec.outranks(Spec.prodRank(pairMarks(), q2), Spec.prodRank(pairMarks(), 3n))) == True{} : Bool},
    der: Spec.DerivesOnce(pairGrammar(), [], Spec.rhsOf(pairGrammar(), q2), [], q2, [], [1n], [], [1n, 0n])) -> Empty:
  match q2:
    case 0n:
      Lemma.false_is_not_true(cond)
    case 1n+p:
      match p:
        case 0n:
          Lemma.false_is_not_true(cond)
        case 1n+p2:
          match p2:
            case 0n:
              match der:
                case (forest, (fit, (spell, (clean, rules)))):
                  pairForest(forest, fit, spell, clean)
            case 1n+p3:
              match p3:
                case 0n:
                  Lemma.false_is_not_true(cond)
                case 1n+p4:
                  Lemma.false_is_not_true(cond)

def pairNoRivalOfY(rival: Spec.ProdRival(pairGrammar(), [], pairMarks(), 1n, 3n, [1n], [], [1n, 0n])) -> Empty:
  match rival:
    case (q2, (cond, der)):
      pairNoRivalOfYAt(q2, cond, der)

# X -> Y -> t is unbeaten.
def pairSelected() -> Spec.UnbeatenTree(pairGrammar(), [], pairMarks(), 0n, [1n], Spec.Node{0n, [Spec.Node{3n, [Spec.Leaf{1n}]}]}):
  (({==}, ({==}, (Unit{}, ((Unit{}, (Unit{}, Unit{})), Unit{})))), (r => pairNoRivalOfX(r), ((r => pairNoRivalOfY(r), (Unit{}, Unit{})), Unit{})))

# ---- A loop round with more than one item ----

# S ::= { ( A A ) } b, A ::= a | ε. A loop is written { ( τ ) }, so each round is one
# group, and its link step says where the round starts and ends. On b the loop has no
# rounds: a round over nothing would be removable. On a b there is one round, read two
# ways (a ε, or ε a).
def roundGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[Spec.Brack{Spec.Group{}, [[n(1n), n(1n)]]}]]}, t(2n)]},
   Spec.Production{1n, [t(1n)]},
   Spec.Production{1n, [Spec.Eps{}]}]

def roundNone() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[]}, Spec.Leaf{2n}]}

def roundAE() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Pick{0n, [Spec.Node{1n, [Spec.Leaf{1n}]}, Spec.Node{2n, [Spec.Skip{}]}]}]}]}, Spec.Leaf{2n}]}

def roundEA() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[Spec.Pick{0n, [Spec.Pick{0n, [Spec.Node{2n, [Spec.Skip{}]}, Spec.Node{1n, [Spec.Leaf{1n}]}]}]}]}, Spec.Leaf{2n}]}

def exactRoundNone() -> {Spec.sameSet(exact(roundGrammar(), [2n]), Spec.steps(roundNone(), 0n)) == True{} : Bool}:
  {==}

def exactRoundTwo() -> {Spec.sameSet(exact(roundGrammar(), [1n, 2n]), List.append(&2, Spec.Bsr, Spec.steps(roundAE(), 0n), Spec.steps(roundEA(), 0n))) == True{} : Bool}:
  {==}

# ---- The preference oracle ----

# The oracle's set, or nothing when it refuses.
def prefer(+grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  Unb.unbeatenSteps(2000n, grammar, [], marks, 0n, input)

def preferOr(m: Maybe<&2, +List<Spec.Bsr>>) -> +List<Spec.Bsr>:
  match m:
    case Some{+xs}:
      xs
    case None{}:
      []

# Does the oracle's set embed the tree?
def embeds(+grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +tree: Spec.Tree) -> Bool:
  Spec.allIn(Spec.steps(tree, 0n), preferOr(prefer(grammar, marks, input)))

# S ::= @prefer A | B: the set embeds the tree through A, not the one through B.
def preferKeepsA() -> {embeds(preferGrammar(), preferMarks(), [1n], viaA()) == True{} : Bool}:
  {==}

def preferDropsB() -> {embeds(preferGrammar(), preferMarks(), [1n], viaB()) == False{} : Bool}:
  {==}

# A ::= @prefer A | t goes round a cycle, and so does X ::= @prefer Y | t, Y ::= @prefer X | t:
# the oracle refuses both, as Swift Apus refuses such a grammar.
def preferRefusesCycle() -> {prefer(cycleGrammar(), cycleMarks(), [1n]) == None{} : Maybe<&2, +List<Spec.Bsr>>}:
  {==}

def preferRefusesPair() -> {prefer(pairGrammar(), pairMarks(), [1n]) == None{} : Maybe<&2, +List<Spec.Bsr>>}:
  {==}

# S ::= { ( @avoid A | B ) }, A ::= t, B ::= t, on t t: every round takes B.
def avoidGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[Spec.Brack{Spec.Group{}, [[n(1n)], [n(2n)]]}]]}]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}]

def avoidMarks() -> +List<Spec.Mark>:
  [Spec.AltMark{0n, [0n, 0n, 0n], 0n, Spec.Avoided{}}]

def avoidRound(+a: Nat, +q: Nat) -> Spec.Tree:
  Spec.Pick{0n, [Spec.Pick{a, [Spec.Node{q, [Spec.Leaf{1n}]}]}]}

def avoidBB() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[avoidRound(1n, 2n), avoidRound(1n, 2n)]}]}

def avoidAB() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[avoidRound(0n, 1n), avoidRound(1n, 2n)]}]}

def avoidKeepsBB() -> {embeds(avoidGrammar(), avoidMarks(), [1n, 1n], avoidBB()) == True{} : Bool}:
  {==}

def avoidDropsAB() -> {embeds(avoidGrammar(), avoidMarks(), [1n, 1n], avoidAB()) == False{} : Bool}:
  {==}

# A loop written { τ } is refused: its rounds are not groups.
def rawLoopGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[n(1n)], [n(2n)]]}]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}]

def preferRefusesRawLoop() -> {prefer(rawLoopGrammar(), [Spec.AltMark{0n, [0n], 0n, Spec.Avoided{}}], [1n]) == None{} : Maybe<&2, +List<Spec.Bsr>>}:
  {==}

# ---- Phase 2 on top of phase 1 ----

# S ::= @prefer A | B, A ::= @left(P) P "+" P, P ::= n | n "+" n, B ::= n "+" n "+" n,
# with n = 1 and "+" = 2, on n + n + n. Productions: 0 is S ::= A, 1 is S ::= B, 2 is
# A ::= P + P, 3 and 4 are P's, 5 is B's; S = 0, A = 1, P = 2, B = 3. Every tree of A
# breaks @left(P), since P derives the last child's tokens. So A is no rival: a preferred
# alternative that can't take the place of B beats nothing, and the tree through B stays.
# Without the rules, A is preferred and B goes.
def joinGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n)]}, Spec.Production{0n, [n(3n)]},
   Spec.Production{1n, [n(2n), t(2n), n(2n)]},
   Spec.Production{2n, [t(1n)]}, Spec.Production{2n, [t(1n), t(2n), t(1n)]},
   Spec.Production{3n, [t(1n), t(2n), t(1n), t(2n), t(1n)]}]

def joinGuards() -> +List<Spec.GuardMark>:
  [Spec.ProdGuard{2n, Spec.LeftAssoc{[2n]}}]

def joinMarks() -> +List<Spec.Mark>:
  [Spec.ProdMark{0n, Spec.Preferred{}}]

def joinInput() -> +List<Nat>:
  [1n, 2n, 1n, 2n, 1n]

def joinViaB() -> Spec.Tree:
  Spec.Node{1n, [Spec.Node{5n, [Spec.Leaf{1n}, Spec.Leaf{2n}, Spec.Leaf{1n}, Spec.Leaf{2n}, Spec.Leaf{1n}]}]}

def joined(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  Unb.unbeatenSteps(2000n, grammar, gm, marks, 0n, input)

def joinKeepsB() -> {Spec.allIn(Spec.steps(joinViaB(), 0n), preferOr(joined(joinGrammar(), joinGuards(), joinMarks(), joinInput()))) == True{} : Bool}:
  {==}

def noRulesDropsB() -> {embeds(joinGrammar(), joinMarks(), joinInput(), joinViaB()) == False{} : Bool}:
  {==}

# ---- The guard oracle (phase 1) ----

# The oracle's set, or nothing when it refuses.
def guarded(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  Guard.guardSteps(2000n, grammar, gm, 0n, input)

# Does the oracle's set embed the tree?
def admits(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +tree: Spec.Tree) -> Bool:
  Spec.allIn(Spec.steps(tree, 0n), preferOr(guarded(grammar, gm, input)))

# E ::= E "+" E | a, with a = 1 and "+" = 2, on a + a + a.
def sumGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(0n), t(2n), n(0n)]}, Spec.Production{0n, [t(1n)]}]

def atom() -> Spec.Tree:
  Spec.Node{1n, [Spec.Leaf{1n}]}

def sum(+l: Spec.Tree, +r: Spec.Tree) -> Spec.Tree:
  Spec.Node{0n, [l, Spec.Leaf{2n}, r]}

def sumInput() -> +List<Nat>:
  [1n, 2n, 1n, 2n, 1n]

# @left: (a + a) + a stays, a + (a + a) goes.
def leftMarks() -> +List<Spec.GuardMark>:
  [Spec.ProdGuard{0n, Spec.LeftAssoc{[]}}]

def leftKeepsLeft() -> {admits(sumGrammar(), leftMarks(), sumInput(), sum(sum(atom(), atom()), atom())) == True{} : Bool}:
  {==}

def leftDropsRight() -> {admits(sumGrammar(), leftMarks(), sumInput(), sum(atom(), sum(atom(), atom()))) == False{} : Bool}:
  {==}

# @right: the other way round.
def rightMarks() -> +List<Spec.GuardMark>:
  [Spec.ProdGuard{0n, Spec.RightAssoc{[]}}]

def rightKeepsRight() -> {admits(sumGrammar(), rightMarks(), sumInput(), sum(atom(), sum(atom(), atom()))) == True{} : Bool}:
  {==}

def rightDropsLeft() -> {admits(sumGrammar(), rightMarks(), sumInput(), sum(sum(atom(), atom()), atom())) == False{} : Bool}:
  {==}

# S ::= A A, A ::= t | t, D ::= t t, with a lookahead on the first A ::= t, on t t.
def aheadGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n), n(1n)]}, Spec.Production{1n, [t(1n)]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n), t(1n)]}]

def aheadTree(+q1: Nat, +q2: Nat) -> Spec.Tree:
  Spec.Node{0n, [Spec.Node{q1, [Spec.Leaf{1n}]}, Spec.Node{q2, [Spec.Leaf{1n}]}]}

# NotAhead(D): the first A ::= t only where D does not follow, so only at the second t.
def notAheadMarks() -> +List<Spec.GuardMark>:
  [Spec.ProdGuard{1n, Spec.NotAhead{[2n]}}]

def notAheadKeeps() -> {admits(aheadGrammar(), notAheadMarks(), [1n, 1n], aheadTree(2n, 1n)) == True{} : Bool}:
  {==}

def notAheadDrops() -> {admits(aheadGrammar(), notAheadMarks(), [1n, 1n], aheadTree(1n, 2n)) == False{} : Bool}:
  {==}

# Ahead(D): the first A ::= t only where D follows, so only at the first t.
def aheadMarks() -> +List<Spec.GuardMark>:
  [Spec.ProdGuard{1n, Spec.Ahead{[2n]}}]

def aheadKeeps() -> {admits(aheadGrammar(), aheadMarks(), [1n, 1n], aheadTree(1n, 2n)) == True{} : Bool}:
  {==}

def aheadDrops() -> {admits(aheadGrammar(), aheadMarks(), [1n, 1n], aheadTree(2n, 1n)) == False{} : Bool}:
  {==}

# A rule on the alternative of a loop is refused.
def guardRefusesLoop() -> {guarded(avoidGrammar(), [Spec.AltGuard{0n, [0n], 0n, Spec.LeftAssoc{[]}}], [1n, 1n]) == None{} : Maybe<&2, +List<Spec.Bsr>>}:
  {==}

# Without rules both readings of a + a + a stay.
def noGuardKeepsBoth() -> {Bool.and(admits(sumGrammar(), [], sumInput(), sum(atom(), sum(atom(), atom()))), admits(sumGrammar(), [], sumInput(), sum(sum(atom(), atom()), atom()))) == True{} : Bool}:
  {==}

# ---- The extent oracle (phase 3) ----

def extented(+grammar: +List<Spec.Production>, +em: +List<Spec.ExtentMark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  Extent.extentSteps(2000n, grammar, em, 0n, input)

def picks(+grammar: +List<Spec.Production>, +em: +List<Spec.ExtentMark>, +input: +List<Nat>, +tree: Spec.Tree) -> Bool:
  Spec.allIn(Spec.steps(tree, 0n), preferOr(extented(grammar, em, input)))

# S ::= { ( a ) } B, B ::= ε | a, on a a: the loop reads both a's, or one.
def extLoopGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [Spec.Brack{Spec.Closure{}, [[Spec.Brack{Spec.Group{}, [[t(1n)]]}]]}, n(1n)]}, Spec.Production{1n, [Spec.Eps{}]}, Spec.Production{1n, [t(1n)]}]

def aRound() -> Spec.Tree:
  Spec.Pick{0n, [Spec.Pick{0n, [Spec.Leaf{1n}]}]}

def loopTwo() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[aRound(), aRound()]}, Spec.Node{1n, [Spec.Skip{}]}]}

def loopOne() -> Spec.Tree:
  Spec.Node{0n, [Spec.Loop{[aRound()]}, Spec.Node{2n, [Spec.Leaf{1n}]}]}

# @longest on the loop: it takes both a's.
def longestLoop() -> +List<Spec.ExtentMark>:
  [Spec.BrackExtent{0n, [0n], Spec.Longest{}}]

def longestKeepsTwo() -> {picks(extLoopGrammar(), longestLoop(), [1n, 1n], loopTwo()) == True{} : Bool}:
  {==}

def longestDropsOne() -> {picks(extLoopGrammar(), longestLoop(), [1n, 1n], loopOne()) == False{} : Bool}:
  {==}

# @shortest on the loop: it takes one.
def shortestLoop() -> +List<Spec.ExtentMark>:
  [Spec.BrackExtent{0n, [0n], Spec.Shortest{}}]

def shortestKeepsOne() -> {picks(extLoopGrammar(), shortestLoop(), [1n, 1n], loopOne()) == True{} : Bool}:
  {==}

def shortestDropsTwo() -> {picks(extLoopGrammar(), shortestLoop(), [1n, 1n], loopTwo()) == False{} : Bool}:
  {==}

# S ::= X Y, X ::= a | a a, Y ::= ε | a, with @longest X, on a a.
def ntGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n), n(2n)]}, Spec.Production{1n, [t(1n)]}, Spec.Production{1n, [t(1n), t(1n)]}, Spec.Production{2n, [Spec.Eps{}]}, Spec.Production{2n, [t(1n)]}]

def xLong() -> Spec.Tree:
  Spec.Node{0n, [Spec.Node{2n, [Spec.Leaf{1n}, Spec.Leaf{1n}]}, Spec.Node{3n, [Spec.Skip{}]}]}

def xShort() -> Spec.Tree:
  Spec.Node{0n, [Spec.Node{1n, [Spec.Leaf{1n}]}, Spec.Node{4n, [Spec.Leaf{1n}]}]}

def longestX() -> +List<Spec.ExtentMark>:
  [Spec.NtExtent{1n, Spec.Longest{}}]

def longestXKeeps() -> {picks(ntGrammar(), longestX(), [1n, 1n], xLong()) == True{} : Bool}:
  {==}

def longestXDrops() -> {picks(ntGrammar(), longestX(), [1n, 1n], xShort()) == False{} : Bool}:
  {==}

# Without marks both stay.
def noExtentKeepsBoth() -> {Bool.and(picks(ntGrammar(), [], [1n, 1n], xLong()), picks(ntGrammar(), [], [1n, 1n], xShort())) == True{} : Bool}:
  {==}

# Two marked items in one sequence are refused.
def extentRefusesTwo() -> {extented(ntGrammar(), [Spec.NtExtent{1n, Spec.Longest{}}, Spec.NtExtent{2n, Spec.Longest{}}], [1n, 1n]) == None{} : Maybe<&2, +List<Spec.Bsr>>}:
  {==}

# S ::= P X Q, P ::= ε | a, X ::= a | a a, Q ::= ε | a, with @longest X, on a a: of the
# three readings only P = ε, X = a a, Q = ε stays, and the oracle answers.
def pxqGrammar() -> +List<Spec.Production>:
  [Spec.Production{0n, [n(1n), n(2n), n(3n)]}, Spec.Production{1n, [Spec.Eps{}]}, Spec.Production{1n, [t(1n)]}, Spec.Production{2n, [t(1n)]}, Spec.Production{2n, [t(1n), t(1n)]}, Spec.Production{3n, [Spec.Eps{}]}, Spec.Production{3n, [t(1n)]}]

def pxq(+p: Spec.Tree, +x: Spec.Tree, +q: Spec.Tree) -> Spec.Tree:
  Spec.Node{0n, [p, x, q]}

def pxqMarks() -> +List<Spec.ExtentMark>:
  [Spec.NtExtent{2n, Spec.Longest{}}]

def isSomeSet(m: Maybe<&2, +List<Spec.Bsr>>) -> Bool:
  match m:
    case Some{xs}:
      True{}
    case None{}:
      False{}

def pxqAnswers() -> {isSomeSet(extented(pxqGrammar(), pxqMarks(), [1n, 1n])) == True{} : Bool}:
  {==}

def pxqKeepsLong() -> {picks(pxqGrammar(), pxqMarks(), [1n, 1n], pxq(Spec.Node{1n, [Spec.Skip{}]}, Spec.Node{4n, [Spec.Leaf{1n}, Spec.Leaf{1n}]}, Spec.Node{5n, [Spec.Skip{}]})) == True{} : Bool}:
  {==}

def pxqDropsLeft() -> {picks(pxqGrammar(), pxqMarks(), [1n, 1n], pxq(Spec.Node{2n, [Spec.Leaf{1n}]}, Spec.Node{3n, [Spec.Leaf{1n}]}, Spec.Node{5n, [Spec.Skip{}]})) == False{} : Bool}:
  {==}

def pxqDropsRight() -> {picks(pxqGrammar(), pxqMarks(), [1n, 1n], pxq(Spec.Node{1n, [Spec.Skip{}]}, Spec.Node{3n, [Spec.Leaf{1n}]}, Spec.Node{6n, [Spec.Leaf{1n}]})) == False{} : Bool}:
  {==}
