import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./GUARD.bend as Guard
import ./WITNESS.bend as Witness
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_DECIDE.bend as D

# PHASE 1'S VERDICT ON A STEP IS RIGHT. Yes when every rule the step decides answers Yes,
# No when one answers No. A Yes is right and a No is right (PROOF_DECIDE.bend), so a step
# answered Yes keeps its rules, and a step answered No does not.

# ======== ONE STEP ========

def only_yes(b: Bool, +t: Guard.Tri, -r: Type, +e: {Guard.only(b, t) == Guard.Yes{} : Guard.Tri}, k: {t == Guard.Yes{} : Guard.Tri} -> r) -> Guard.When(b, r):
  match b:
    case True{}:
      k(e)
    case False{}:
      Unit{}

def only_no(b: Bool, +t: Guard.Tri, -r: Type, +e: {Guard.only(b, t) == Guard.No{} : Guard.Tri}, h: Guard.When(b, r), k: {t == Guard.No{} : Guard.Tri} -> r -> Empty) -> Empty:
  match b:
    case True{}:
      k(e, h)
    case False{}:
      D.yes_not_no(e)

def rule_yes(g: Guard.Guard, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +e: {Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j) == Guard.Yes{} : Guard.Tri}) -> Guard.StepHolds(grammar, g, input, q, n, d, i, k, j):
  match g:
    case Guard.Ahead{+ids}:
      +ahead = Lemma.dropN(i, input)
      only_yes(Nat.is_eq(d, n), Guard.allAheadTri(ids, fuel, grammar, ahead), Guard.AllAhead(grammar, ids, ahead), e, y => D.all_ahead_yes(ids, fuel, grammar, ahead, y))
    case Guard.NotAhead{+ids}:
      +ahead = Lemma.dropN(i, input)
      only_yes(Nat.is_eq(d, n), Guard.noneAheadTri(ids, fuel, grammar, ahead), Guard.NoneAhead(grammar, ids, ahead), e, y => D.none_ahead_yes(ids, fuel, grammar, ahead, y))
    case Guard.LeftAssoc{+ids}:
      +w = Lemma.slice(input, k, Nat.sub(j, k))
      only_yes(Bool.and(Nat.is_eq(d, n), Bool.not(Nat.is_eq(d, 0n))), Guard.edgeTri(ids, fuel, grammar, q, w), Guard.EdgeOk(grammar, ids, q, w), e, y => D.edge_yes(ids, fuel, grammar, q, w, y))
    case Guard.RightAssoc{+ids}:
      +w = Lemma.slice(input, k, Nat.sub(j, k))
      only_yes(Nat.is_eq(d, 1n), Guard.edgeTri(ids, fuel, grammar, q, w), Guard.EdgeOk(grammar, ids, q, w), e, y => D.edge_yes(ids, fuel, grammar, q, w, y))

def rule_no(g: Guard.Guard, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +e: {Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri},
  h: Guard.StepHolds(grammar, g, input, q, n, d, i, k, j)) -> Empty:
  match g:
    case Guard.Ahead{+ids}:
      +ahead = Lemma.dropN(i, input)
      only_no(Nat.is_eq(d, n), Guard.allAheadTri(ids, fuel, grammar, ahead), Guard.AllAhead(grammar, ids, ahead), e, h, no => a => D.all_ahead_no(ids, fuel, grammar, ahead, no, a))
    case Guard.NotAhead{+ids}:
      +ahead = Lemma.dropN(i, input)
      only_no(Nat.is_eq(d, n), Guard.noneAheadTri(ids, fuel, grammar, ahead), Guard.NoneAhead(grammar, ids, ahead), e, h, no => a => D.none_ahead_no(ids, fuel, grammar, ahead, no, a))
    case Guard.LeftAssoc{+ids}:
      +w = Lemma.slice(input, k, Nat.sub(j, k))
      only_no(Bool.and(Nat.is_eq(d, n), Bool.not(Nat.is_eq(d, 0n))), Guard.edgeTri(ids, fuel, grammar, q, w), Guard.EdgeOk(grammar, ids, q, w), e, h, no => a => D.edge_no(ids, fuel, grammar, q, w, no, a))
    case Guard.RightAssoc{+ids}:
      +w = Lemma.slice(input, k, Nat.sub(j, k))
      only_no(Nat.is_eq(d, 1n), Guard.edgeTri(ids, fuel, grammar, q, w), Guard.EdgeOk(grammar, ids, q, w), e, h, no => a => D.edge_no(ids, fuel, grammar, q, w, no, a))

def rules_pair(+g: Guard.Guard, +rest: +List<Guard.Guard>, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  p: {Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j) == Guard.Yes{} : Guard.Tri} & {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.Yes{} : Guard.Tri},
  later: {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.Yes{} : Guard.Tri} -> Guard.StepRules(grammar, rest, input, q, n, d, i, k, j))
  -> Guard.StepRules(grammar, g <> rest, input, q, n, d, i, k, j):
  match p:
    case (a, b):
      (rule_yes(g, fuel, grammar, input, q, n, d, i, k, j, a), later(b))

law rules_yes:
  for gs: +List<Guard.Guard>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +e: {Guard.rulesAt(gs, fuel, grammar, input, q, n, d, i, k, j) == Guard.Yes{} : Guard.Tri}
  Guard.StepRules(grammar, gs, input, q, n, d, i, k, j)

def rules_yes(gs, fuel, grammar, input, q, n, d, i, k, j, e):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +rest}:
      rules_pair(g, rest, fuel, grammar, input, q, n, d, i, k, j, D.and_yes(Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j), Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j), e),
        later => rules_yes(rest, fuel, grammar, input, q, n, d, i, k, j, later))

def rules_side(+g: Guard.Guard, +rest: +List<Guard.Guard>, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  cases: Either<{Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri}, {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri}>,
  h1: Guard.StepHolds(grammar, g, input, q, n, d, i, k, j), hr: Guard.StepRules(grammar, rest, input, q, n, d, i, k, j),
  later: {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri} -> Guard.StepRules(grammar, rest, input, q, n, d, i, k, j) -> Empty) -> Empty:
  match cases:
    case Inl{e}:
      rule_no(g, fuel, grammar, input, q, n, d, i, k, j, e, h1)
    case Inr{e}:
      later(e, hr)

def rules_split(+g: Guard.Guard, +rest: +List<Guard.Guard>, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  cases: Either<{Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri}, {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri}>,
  h: Guard.StepRules(grammar, g <> rest, input, q, n, d, i, k, j),
  later: {Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri} -> Guard.StepRules(grammar, rest, input, q, n, d, i, k, j) -> Empty) -> Empty:
  match h:
    case (h1, hr):
      rules_side(g, rest, fuel, grammar, input, q, n, d, i, k, j, cases, h1, hr, later)

law rules_no:
  for gs: +List<Guard.Guard>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +e: {Guard.rulesAt(gs, fuel, grammar, input, q, n, d, i, k, j) == Guard.No{} : Guard.Tri}
  for h: Guard.StepRules(grammar, gs, input, q, n, d, i, k, j)
  Empty

def rules_no(gs, fuel, grammar, input, q, n, d, i, k, j, e, h):
  match gs:
    case Nil{}:
      D.yes_not_no(e)
    case Con{+g, +rest}:
      rules_split(g, rest, fuel, grammar, input, q, n, d, i, k, j, D.and_no_cases(Guard.ruleAt(g, fuel, grammar, input, q, n, d, i, k, j), Guard.rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j), e), h,
        later => hr => rules_no(rest, fuel, grammar, input, q, n, d, i, k, j, later, hr))

# A step answered Yes keeps its rules; a step that keeps its rules is not answered No.
law step_yes:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +marks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +e: {Guard.stepTri(fuel, grammar, marks, input, x) == Guard.Yes{} : Guard.Tri}
  Guard.StepOk(grammar, marks, input, x)

def step_yes(x, fuel, grammar, marks, input, e):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      rules_yes(Guard.guardsOf(marks, q), fuel, grammar, input, q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), d, i, k, j, e)

law step_no:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +marks: +List<Guard.GuardMark>
  for +input: +List<Nat>
  for +e: {Guard.stepTri(fuel, grammar, marks, input, x) == Guard.No{} : Guard.Tri}
  for h: Guard.StepOk(grammar, marks, input, x)
  Empty

def step_no(x, fuel, grammar, marks, input, e, h):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      rules_no(Guard.guardsOf(marks, q), fuel, grammar, input, q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), d, i, k, j, e, h)

law yes_of:
  for c: Guard.Tri
  for +h: {Guard.isYes(c) == True{} : Bool}
  {c == Guard.Yes{} : Guard.Tri}

def yes_of(c, h):
  match c:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(h))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(h))
