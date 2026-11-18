import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./RUN.bend as Run
import ./PROOF_RUN.bend as R
import ./PROOF_NEEDS.bend as N

# THE TWIN ANSWERS: with fuel 1 + the size of the descriptor universe (RUN.bend), each
# stage of the exact parser hands out a set. Built from the engine's laws (PROOF_RUN.bend)
# and the loops' laws on bounded input (PROOF_NEEDS.bend, ...).

def prune_after(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +F: Nat,
  +er: {Gll.parseWith(F, Gll.NoPred{}, grammar, start, input) == r : Gll.GRun},
  +hd: {R.isDone(r) == True{} : Bool},
  +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F) == True{} : Bool})
  -> {N.isSteps(Prune.pruneSteps(Check.runChecked(r, grammar, start, input), F, grammar, start, input)) == True{} : Bool}:
  match r:
    case Gll.GDone{+t}:
      %Equal.sym(Maybe<&2, +List<Core.Bsr>>, Check.runCheckedWith(Gll.NoPred{}, Gll.GDone{t}, grammar, start, input), Some{Check.stepsOf(t)}, R.checked_answers(F, Gll.NoPred{}, grammar, start, input, t, er)) : {N.isSteps(Prune.pruneSteps(_, F, grammar, start, input)) == True{} : Bool}
      N.pruned_answers(F, grammar, start, input, Check.stepsOf(t), R.final_steps_bounded(F, Gll.NoPred{}, grammar, start, input, t, er), hf)
    case Gll.OutOfFuel{+st}:
      Empty.absurd({N.isSteps(Prune.pruneSteps(Check.runChecked(Gll.OutOfFuel{st}, grammar, start, input), F, grammar, start, input)) == True{} : Bool}, Lemma.false_is_not_true(hd))

# THE PRUNED PARSER ANSWERS: with that fuel, `prunedSteps` hands out its steps.
law pruned_parser_answers:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {N.isSteps(Prune.prunedSteps(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), grammar, start, input)) == True{} : Bool}

def pruned_parser_answers(grammar, start, input):
  +F = {1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)) : Nat}
  prune_after(Gll.parseWith(F, Gll.NoPred{}, grammar, start, input), grammar, start, input, F, {==}, R.gll_finishes(Gll.NoPred{}, grammar, start, input), Lemma.le_refl(F))
