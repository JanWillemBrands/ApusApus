import Base
import ./CORE.bend as Core
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle

# THE ORACLE ON EXAMPLES: @left and @right (phase 1), @prefer and @avoid (phase 2).

def n() -> Core.Sym:
  Core.Terminal{1n}

def plus() -> Core.Sym:
  Core.Terminal{2n}

def e() -> Core.Sym:
  Core.Nonterminal{0n, Core.Anything{}}

# E = E + E | n
def expr() -> +List<Core.Production>:
  [Core.Production{0n, [e(), plus(), e()]}, Core.Production{0n, [n()]}]

def leaf() -> Core.Tree:
  Core.Node{1n, [Core.Leaf{1n}]}

def sum(+a: Core.Tree, +b: Core.Tree) -> Core.Tree:
  Core.Node{0n, [a, Core.Leaf{2n}, b]}

def kept(m: Maybe<&2, +List<Core.Bsr>>, +t: Core.Tree) -> Bool:
  match m:
    case Some{+set}:
      Core.allIn(Core.steps([t], 0n), set)
    case None{}:
      False{}

def input() -> +List<Nat>:
  [1n, 2n, 1n, 2n, 1n]

# Bare @left on E + E: n + n + n reads as (n + n) + n only.
law left_keeps_left:
  {kept(Oracle.oracleSteps(40n, expr(), [Guard.GuardMark{0n, Guard.LeftAssoc{[]}}], [], 0n, input()), sum(sum(leaf(), leaf()), leaf())) == True{} : Bool}

def left_keeps_left():
  {==}

law left_drops_right:
  {kept(Oracle.oracleSteps(40n, expr(), [Guard.GuardMark{0n, Guard.LeftAssoc{[]}}], [], 0n, input()), sum(leaf(), sum(leaf(), leaf()))) == False{} : Bool}

def left_drops_right():
  {==}

# Bare @right on E + E: n + (n + n) only.
law right_keeps_right:
  {kept(Oracle.oracleSteps(40n, expr(), [Guard.GuardMark{0n, Guard.RightAssoc{[]}}], [], 0n, input()), sum(leaf(), sum(leaf(), leaf()))) == True{} : Bool}

def right_keeps_right():
  {==}

law right_drops_left:
  {kept(Oracle.oracleSteps(40n, expr(), [Guard.GuardMark{0n, Guard.RightAssoc{[]}}], [], 0n, input()), sum(sum(leaf(), leaf()), leaf())) == False{} : Bool}

def right_drops_left():
  {==}

def answered(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case Some{set}:
      True{}
    case None{}:
      False{}

def a() -> Core.Sym:
  Core.Terminal{1n}

# X = @prefer a | Y, Y = a: on a, X -> a only.
def choice() -> +List<Core.Production>:
  [Core.Production{0n, [a()]}, Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}]}, Core.Production{1n, [a()]}]

def direct() -> Core.Tree:
  Core.Node{0n, [Core.Leaf{1n}]}

def via() -> Core.Tree:
  Core.Node{1n, [Core.Node{2n, [Core.Leaf{1n}]}]}

law prefer_keeps:
  {kept(Oracle.oracleSteps(20n, choice(), [], [Prefer.RankMark{0n, Prefer.Preferred{}}], 0n, [1n]), direct()) == True{} : Bool}

def prefer_keeps():
  {==}

law prefer_drops:
  {kept(Oracle.oracleSteps(20n, choice(), [], [Prefer.RankMark{0n, Prefer.Preferred{}}], 0n, [1n]), via()) == False{} : Bool}

def prefer_drops():
  {==}

# The same with X = a | @avoid Y.
law avoid_drops:
  {kept(Oracle.oracleSteps(20n, choice(), [], [Prefer.RankMark{1n, Prefer.Avoided{}}], 0n, [1n]), via()) == False{} : Bool}

def avoid_drops():
  {==}

law avoid_keeps:
  {kept(Oracle.oracleSteps(20n, choice(), [], [Prefer.RankMark{1n, Prefer.Avoided{}}], 0n, [1n]), direct()) == True{} : Bool}

def avoid_keeps():
  {==}

# Without marks both readings stay.
law plain_keeps:
  {kept(Oracle.oracleSteps(20n, choice(), [], [], 0n, [1n]), via()) == True{} : Bool}

def plain_keeps():
  {==}

# A = @prefer A | a: every tree ends in A -> a, which A -> A outranks over the same tokens,
# so no tree is chosen. The grammar is not well-formed: A -> A lies on a cycle that reads
# no input.
def cycle() -> +List<Core.Production>:
  [Core.Production{0n, [Core.Nonterminal{0n, Core.Anything{}}]}, Core.Production{0n, [a()]}]

def preferFirst() -> +List<Prefer.RankMark>:
  [Prefer.RankMark{0n, Prefer.Preferred{}}]

law cycle_keeps_nothing:
  {Bool.or(kept(Oracle.oracleSteps(20n, cycle(), [], preferFirst(), 0n, [1n]), Core.Node{1n, [Core.Leaf{1n}]}),
           kept(Oracle.oracleSteps(20n, cycle(), [], preferFirst(), 0n, [1n]), Core.Node{0n, [Core.Node{1n, [Core.Leaf{1n}]}]})) == False{} : Bool}

def cycle_keeps_nothing():
  {==}

law cycle_not_well_formed:
  {Prefer.noPreferenceCycle(cycle(), preferFirst()) == False{} : Bool}

def cycle_not_well_formed():
  {==}

# Without the mark, or with the mark on a: cyclic, but well-formed.
law cycle_unmarked_ok:
  {Bool.and(Prefer.noPreferenceCycle(cycle(), []), Prefer.noPreferenceCycle(cycle(), [Prefer.RankMark{1n, Prefer.Preferred{}}])) == True{} : Bool}

def cycle_unmarked_ok():
  {==}

law choice_ok:
  {Prefer.noPreferenceCycle(choice(), preferFirst()) == True{} : Bool}

def choice_ok():
  {==}

# A = @prefer B | a, B = A: the cycle goes through B.
law cycle_through_b:
  {Prefer.noPreferenceCycle([Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}]}, Core.Production{0n, [a()]}, Core.Production{1n, [Core.Nonterminal{0n, Core.Anything{}}]}], preferFirst()) == False{} : Bool}

def cycle_through_b():
  {==}

# A = @prefer N A | a, N = n | ε: N can read nothing, so A -> N A reaches A.
law cycle_through_null:
  {Prefer.noPreferenceCycle([Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}, Core.Nonterminal{0n, Core.Anything{}}]}, Core.Production{0n, [a()]},
     Core.Production{1n, [Core.Terminal{2n}]}, Core.Production{1n, []}], preferFirst()) == False{} : Bool}

def cycle_through_null():
  {==}

# A = @prefer x A | a: x must be read, so there is no cycle.
law token_breaks_cycle:
  {Prefer.noPreferenceCycle([Core.Production{0n, [Core.Terminal{2n}, Core.Nonterminal{0n, Core.Anything{}}]}, Core.Production{0n, [a()]}], preferFirst()) == True{} : Bool}

def token_breaks_cycle():
  {==}

# P = X c | a, X = @prefer Y | a, Y = P: X -> Y reaches P, but P -> X c must read c.
law suffix_breaks_cycle:
  {Prefer.noPreferenceCycle([Core.Production{0n, [Core.Nonterminal{1n, Core.Anything{}}, Core.Terminal{3n}]}, Core.Production{0n, [a()]},
     Core.Production{1n, [Core.Nonterminal{2n, Core.Anything{}}]}, Core.Production{1n, [a()]},
     Core.Production{2n, [Core.Nonterminal{0n, Core.Anything{}}]}], [Prefer.RankMark{2n, Prefer.Preferred{}}]) == True{} : Bool}

def suffix_breaks_cycle():
  {==}
