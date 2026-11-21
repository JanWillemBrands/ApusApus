import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./WITNESS.bend as Witness
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./RUN.bend as Run
import ./PROOF_RUN.bend as R
import ./PROOF_NEEDS.bend as N
import ./PROOF_ANSWER.bend as A
import ./PROOF_RIVAL_GROW.bend as RG
import ./PROOF_VERDICT.bend as V

# THE ORACLE ANSWERS. The exact parser answers with fuel 1 + twice the size of the
# descriptor universe (PROOF_ANSWER), its steps lie within bounds, and every verdict on a
# step within bounds is decided (PROOF_VERDICT). So no step of the exact set is Unknown,
# and the oracle hands out its set (`oracle_answers`).

# ======== THE EXACT SET LIES WITHIN BOUNDS ========

# What a parser hands out lies within bounds (nothing is trivially within bounds).
def mBounded(m: Maybe<&2, +List<Core.Bsr>>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match m:
    case Some{+ps}:
      Run.stepsBounded(ps, grammar, input)
    case None{}:
      True{}

def check_pick_b(b: Bool, +t: Gll.GState, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.stepsBounded(Check.stepsOf(t), grammar, input) == True{} : Bool})
  -> {mBounded(Check.checkPick(b, t), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def checked_b(r: Gll.GRun, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +er: {Gll.parseWith(fuel, Gll.NoPred{}, grammar, start, input) == r : Gll.GRun})
  -> {mBounded(Check.runChecked(r, grammar, start, input), grammar, input) == True{} : Bool}:
  match r:
    case Gll.GDone{+t}:
      check_pick_b(Bool.and(Check.closedWith(Gll.NoPred{}, grammar, input, t), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(t))), t, grammar, input,
        R.final_steps_bounded(fuel, Gll.NoPred{}, grammar, start, input, t, er))
    case Gll.OutOfFuel{+st}:
      {==}

def prune_pick_b(b: Bool, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.stepsBounded(ys, grammar, input) == True{} : Bool})
  -> {mBounded(Prune.prunePick(b, ys, ns), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      A.keep_bounded(ys, ns, grammar, input, h)
    case False{}:
      {==}

def prune_checked_b(m: Maybe<&2, +List<Prune.Seg>>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +h: {Run.stepsBounded(ys, grammar, input) == True{} : Bool})
  -> {mBounded(Prune.pruneChecked(m, grammar, start, List.length(&2, Nat, input), ys), grammar, input) == True{} : Bool}:
  match m:
    case Some{+ns}:
      prune_pick_b(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns), ys, ns, grammar, input, h)
    case None{}:
      {==}

def prune_b(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +h: {mBounded(m, grammar, input) == True{} : Bool})
  -> {mBounded(Prune.pruneSteps(m, fuel, grammar, start, input), grammar, input) == True{} : Bool}:
  match m:
    case Some{+ys}:
      prune_checked_b(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), grammar, start, input, ys, h)
    case None{}:
      {==}

def exact_pick_b(b: Bool, +ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.stepsBounded(ps, grammar, input) == True{} : Bool})
  -> {mBounded(Exact.exactPick(b, ps), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def exact_from_b(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +h: {mBounded(m, grammar, input) == True{} : Bool})
  -> {mBounded(Exact.exactFrom(m, fuel, grammar, start, input), grammar, input) == True{} : Bool}:
  match m:
    case Some{+ps}:
      exact_pick_b(Bool.and(Exact.allTreesOk(Witness.witnesses(fuel, grammar, start, input, ps), grammar, start, input), Exact.allCovered(ps, Witness.witnesses(fuel, grammar, start, input, ps))), ps, grammar, input, h)
    case None{}:
      {==}

# The exact parser's steps lie within bounds.
law exact_bounded:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {mBounded(Exact.exactSteps(fuel, grammar, start, input), grammar, input) == True{} : Bool}

def exact_bounded(fuel, grammar, start, input):
  exact_from_b(Prune.prunedSteps(fuel, grammar, start, input), fuel, grammar, start, input,
    prune_b(Check.checkedSteps(fuel, grammar, start, input), fuel, grammar, start, input,
      checked_b(Gll.parse(fuel, grammar, start, input), fuel, grammar, start, input, {==})))

# ======== NO STEP OF THE EXACT SET IS UNKNOWN ========

def unknown_false(t: Guard.Tri, +h: {RG.decidedTri(t) == True{} : Bool}) -> {Guard.isUnknown(t) == False{} : Bool}:
  match t:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      {==}
    case Guard.Unknown{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(h))

def or_false(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

# With fuel above the universe, no step within bounds is Unknown to the oracle.
law none_unknown:
  for ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool}
  {Oracle.anyUnknown(ys, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool}

def none_unknown(ys, fuel, grammar, gmarks, rmarks, start, input, hy, hf):
  match ys:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +B = {Run.stepBound(e, grammar, input) : Bool}
      +t1 = Guard.stepTri(fuel, grammar, gmarks, input, e)
      +t2 = Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, e)
      or_false(Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, e)), Oracle.anyUnknown(rest, fuel, grammar, gmarks, rmarks, start, input),
        unknown_false(Guard.andTri(t1, t2), V.and_dec(t1, t2, V.phase1_decides(fuel, grammar, gmarks, input, e, hf),
          V.phase2_decides(fuel, grammar, gmarks, input, rmarks, e, Lemma.and_true_left(B, Run.stepsBounded(rest, grammar, input), hy), hf))),
        none_unknown(rest, fuel, grammar, gmarks, rmarks, start, input, Lemma.and_true_right_side(B, Run.stepsBounded(rest, grammar, input), hy), hf))

# ======== THE ORACLE ANSWERS ========

def pick_some(b: Bool, +ex: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>,
  +eb: {b == False{} : Bool}) -> {R.isAnswer(Oracle.oraclePick(b, ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({R.isAnswer(None{}) == True{} : Bool}, Lemma.true_is_not_false(eb))
    case False{}:
      {==}

def oracle_from_a(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>,
  +hs: {N.isSteps(m) == True{} : Bool}, +hb: {mBounded(m, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), fuel) == True{} : Bool})
  -> {R.isAnswer(Oracle.oracleFrom(m, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}:
  match m:
    case Some{+ex}:
      pick_some(Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input), ex, fuel, grammar, gmarks, rmarks, start, input, none_unknown(ex, fuel, grammar, gmarks, rmarks, start, input, hb, hf))
    case None{}:
      Empty.absurd({R.isAnswer(None{}) == True{} : Bool}, Lemma.false_is_not_true(hs))

# THE ORACLE ANSWERS: with fuel 1 + twice the size of the descriptor universe, `oracleSteps`
# hands out its set, on every grammar, marks and input.
law oracle_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Oracle.oracleSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, start, input)) == True{} : Bool}

def oracle_answers(grammar, gmarks, rmarks, start, input):
  +F = {1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) : Nat}
  oracle_from_a(Exact.exactSteps(F, grammar, start, input), F, grammar, gmarks, rmarks, start, input,
    A.exact_parser_answers(grammar, start, input), exact_bounded(F, grammar, start, input), Lemma.le_add_right(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))))
