import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./RUN.bend as Run
import ./PROOF_RUN.bend as R
import ./PROOF_NEEDS.bend as N
import ./WITNESS.bend as W
import ./EXACT.bend as Exact
import ./PROOF_WITNESS.bend as WC
import ./PROOF_WSOUND.bend as WS
import ./PROOF_GROUND.bend as GD
import ./PROOF_FOUND.bend as FD
import ./PROOF_COUNT.bend as C
import ./TABLES.bend as T
import ./SETS.bend as Sets
import ./PREDICT.bend as P
import ./PROOF_GROW.bend as GW

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

# ======== THE ENGINE'S STEPS REST ON EARLIER STEPS ========

def todo_bound(+d: Gll.Desc, +rest: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  p: R.Inv6([], pred, grammar, input, Gll.GState{seen, d <> rest, cs, rs, ps, ys}))
  -> {Gll.descIn(d, seen) == True{} : Bool} & {Run.descBound(d, grammar, input) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      +hin = Lemma.and_true_left(Gll.descIn(d, seen), Run.subDescs(rest, seen), h7)
      (hin, R.bounded_at(seen, grammar, input, d, hin, h8))

def ground_next2(+d: Gll.Desc, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s0: Gll.GState, +t: Gll.GState,
  +inv: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool}, q: GD.GStep(grammar, input, s0, Gll.step(d, pred, grammar, input, s0)),
  later: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Run.groundOk(grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Run.groundOk(grammar, input, t) == True{} : Bool}) -> {Run.groundOk(grammar, input, t) == True{} : Bool}:
  match q:
    case (+g, w):
      later(inv, g)

def ground_next(+d: Gll.Desc, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s0: Gll.GState, +t: Gll.GState,
  p: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Run.grows(s0, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(d, pred, grammar, input, s0)), Run.meas(grammar, input, s0)) == True{} : Bool},
  q: GD.GStep(grammar, input, s0, Gll.step(d, pred, grammar, input, s0)),
  later: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Run.groundOk(grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Run.groundOk(grammar, input, t) == True{} : Bool}) -> {Run.groundOk(grammar, input, t) == True{} : Bool}:
  match p:
    case (+inv, (+g, m)):
      ground_next2(d, pred, grammar, input, s0, t, inv, q, later)

def ground_pair(+d: Gll.Desc, +rest: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +hg: {Run.groundOk(grammar, input, Gll.GState{seen, d <> rest, cs, rs, ps, ys}) == True{} : Bool},
  p: {Gll.descIn(d, seen) == True{} : Bool} & {Run.descBound(d, grammar, input) == True{} : Bool})
  -> GD.GStep(grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})):
  match p:
    case (+hin, hb):
      GD.ground_step(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, hg, hin, hb)

# A run that finishes ends in a state that rests on its steps.
law run_grounded:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for s: Gll.GState
  for +t: Gll.GState
  for +h: {Run.inv(pred, grammar, input, s) == True{} : Bool}
  for +hg: {Run.groundOk(grammar, input, s) == True{} : Bool}
  for +e: {Gll.run(fuel, pred, grammar, input, s) == Gll.GDone{t} : Gll.GRun}
  {Run.groundOk(grammar, input, t) == True{} : Bool}

def run_grounded(fuel, pred, grammar, input, s, t, h, hg, e):
  match fuel s:
    case 0n +st:
      Empty.absurd({Run.groundOk(grammar, input, t) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Gll.GRun, Bool, v => R.isDone(v), Gll.OutOfFuel{st}, Gll.GDone{t}, e)))
    case 1n+(+f) Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      +st = {Gll.GState{seen, [], cs, rs, ps, ys} : Gll.GState}
      %Equal.cong(Gll.GRun, Gll.GState, v => R.runState(v), Gll.GDone{st}, Gll.GDone{t}, e) : {Run.groundOk(grammar, input, _) == True{} : Bool}
      hg
    case 1n+(+f) Gll.GState{+seen, Con{+d, +rest}, +cs, +rs, +ps, +ys}:
      +s1 = {Gll.GState{seen, d <> rest, cs, rs, ps, ys} : Gll.GState}
      +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      ground_next(d, pred, grammar, input, s0, t, R.step_inv(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h),
        ground_pair(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, hg, todo_bound(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, R.inv_split([], pred, grammar, input, s1, h))),
        inv2 => g2 => run_grounded(f, pred, grammar, input, Gll.step(d, pred, grammar, input, s0), t, inv2, g2, e))

def inv_of(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  p: {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool})
  -> {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool}:
  match p:
    case (+h, root):
      h

# The engine's final state rests on its steps.
law final_ground:
  for +fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for +e: {Gll.parseWith(fuel, pred, grammar, start, input) == Gll.GDone{t} : Gll.GRun}
  {Run.groundOk(grammar, input, t) == True{} : Bool}

def final_ground(fuel, pred, grammar, start, input, t, e):
  run_grounded(fuel, pred, grammar, input, Run.initial(pred, grammar, start, input), t, inv_of(pred, grammar, start, input, R.initial_inv(pred, grammar, start, input)),
    GD.initial_ground(pred, grammar, start, input), e)

# ======== THE EXACT PARSER ANSWERS ========

def kb_pick(b: Bool, +e: Core.Bsr, +more: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +he: {Run.stepBound(e, grammar, input) == True{} : Bool}, +hm: {Run.stepsBounded(more, grammar, input) == True{} : Bool})
  -> {Run.stepsBounded(Prune.keepPick(b, e, more), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(Run.stepBound(e, grammar, input), Run.stepsBounded(more, grammar, input), he, hm)
    case False{}:
      hm

law keep_bounded:
  for ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}
  {Run.stepsBounded(Prune.keep(ys, ns), grammar, input) == True{} : Bool}

def keep_bounded(ys, ns, grammar, input, h):
  match ys:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +B = {Run.stepBound(e, grammar, input) : Bool}
      kb_pick(Prune.isKept(e, ns), e, Prune.keep(rest, ns), grammar, input, Lemma.and_true_left(B, Run.stepsBounded(rest, grammar, input), h),
        keep_bounded(rest, ns, grammar, input, Lemma.and_true_right_side(B, Run.stepsBounded(rest, grammar, input), h)))

# Every kept step has a witness.
law all_found:
  for todo: +List<Core.Bsr>
  for +F: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Core.Bsr>
  for +ns: +List<Prune.Seg>
  for +sub: {Core.allIn(todo, Prune.keep(ys, ns)) == True{} : Bool}
  for +ok: {Prune.allStepsOk(ys, grammar, ns) == True{} : Bool}
  for +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool}
  for +sj: {N.seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool}
  for +hy: {Run.stepsBounded(Prune.keep(ys, ns), grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), F) == True{} : Bool}
  {WS.allFound(todo, F, grammar, start, input, Prune.keep(ys, ns)) == True{} : Bool}

def all_found(todo, F, grammar, start, input, ys, ns, sub, ok, hg, sj, hy, hf):
  match todo:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +ps = Prune.keep(ys, ns)
      +Fx = W.fixpoint(F, ps, grammar, input, e, [])
      Lemma.and_true_intro(WC.isTrees(W.witnessFor(F, grammar, start, input, ps, e)), WS.allFound(rest, F, grammar, start, input, ps),
        FD.found_root(grammar, input, start, e, ys, ns, Fx, ok, WC.witness_closed(F, ps, grammar, input, e, hy, hf), hg, sj, Lemma.and_true_left(Core.member(e, ps), Core.allIn(rest, ps), sub)),
        all_found(rest, F, grammar, start, input, ys, ns, Lemma.and_true_right_side(Core.member(e, ps), Core.allIn(rest, ps), sub), ok, hg, sj, hy, hf))

def ex3(b: Bool, +F: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>,
  +eb: {b == True{} : Bool},
  +hc: {Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns) == True{} : Bool},
  +sj: {N.seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) == True{} : Bool},
  +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool},
  +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), F) == True{} : Bool})
  -> {N.isSteps(Exact.exactFrom(Prune.prunePick(b, ys, ns), F, grammar, start, input)) == True{} : Bool}:
  match b:
    case True{}:
      +ps = Prune.keep(ys, ns)
      +ok = Lemma.and_true_right_side(Prune.allSegsIn(Prune.rootSegs(grammar, start, List.length(&2, Nat, input)), ns), Prune.allStepsOk(ys, grammar, ns), hc)
      WS.exact_from_answers(F, grammar, start, input, ps,
        all_found(ps, F, grammar, start, input, ys, ns, C.step_refl(ps), ok, hg, sj, keep_bounded(ys, ns, grammar, input, hy), hf))
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(eb))

def ex2(m: Maybe<&2, +List<Prune.Seg>>, +F: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>,
  +hm: {N.closedPick(m, grammar, start, List.length(&2, Nat, input), ys) == True{} : Bool},
  +hg: {Run.stepsGrounded(ys, grammar, input) == True{} : Bool},
  +hy: {Run.stepsBounded(ys, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), F) == True{} : Bool})
  -> {N.isSteps(Exact.exactFrom(Prune.pruneChecked(m, grammar, start, List.length(&2, Nat, input), ys), F, grammar, start, input)) == True{} : Bool}:
  match m:
    case Some{+ns}:
      +NC = {Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns) : Bool}
      +SJ = {N.seenJust(ns, ys, grammar, Prune.rootSegs(grammar, start, List.length(&2, Nat, input))) : Bool}
      +hc = Lemma.and_true_left(NC, SJ, hm)
      ex3(NC, F, grammar, start, input, ys, ns, hc, hc, Lemma.and_true_right_side(NC, SJ, hm), hg, hy, hf)
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hm))

def ground_steps(t: Gll.GState, +grammar: +List<Core.Production>, +input: +List<Nat>, +h: {Run.groundOk(grammar, input, t) == True{} : Bool})
  -> {Run.stepsGrounded(Check.stepsOf(t), grammar, input) == True{} : Bool}:
  match t:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      Lemma.and_true_left(Run.stepsGrounded(ys, grammar, input), Bool.and(Run.descsGrounded(seen, ys), Bool.and(Run.retsGrounded(rs, grammar, ys), Run.popsGrounded(ps, grammar, ys))), h)

def ex1(r: Gll.GRun, +F: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  +er: {Gll.parseWith(F, Gll.NoPred{}, grammar, start, input) == r : Gll.GRun},
  +hd: {R.isDone(r) == True{} : Bool}, +hf1: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F) == True{} : Bool}, +hf2: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), F) == True{} : Bool})
  -> {N.isSteps(Exact.exactFrom(Prune.pruneSteps(Check.runChecked(r, grammar, start, input), F, grammar, start, input), F, grammar, start, input)) == True{} : Bool}:
  match r:
    case Gll.GDone{+t}:
      +ys = Check.stepsOf(t)
      %Equal.sym(Maybe<&2, +List<Core.Bsr>>, Check.runCheckedWith(Gll.NoPred{}, Gll.GDone{t}, grammar, start, input), Some{ys}, R.checked_answers(F, Gll.NoPred{}, grammar, start, input, t, er)) : {N.isSteps(Exact.exactFrom(Prune.pruneSteps(_, F, grammar, start, input), F, grammar, start, input)) == True{} : Bool}
      +hy = R.final_steps_bounded(F, Gll.NoPred{}, grammar, start, input, t, er)
      ex2(Prune.needsOf(F, grammar, start, List.length(&2, Nat, input), ys), F, grammar, start, input, ys, N.needs_closed(F, grammar, start, input, ys, hy, hf1),
        ground_steps(t, grammar, input, final_ground(F, Gll.NoPred{}, grammar, start, input, t, er)), hy, hf2)
    case Gll.OutOfFuel{+st}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hd))

# The engine finishes with any fuel above the universe's size.
def gll_done_with(+F: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F) == True{} : Bool})
  -> {R.isDone(Gll.parseWith(F, pred, grammar, start, input)) == True{} : Bool}:
  +s0 = Run.initial(pred, grammar, start, input)
  R.run_done(F, pred, grammar, input, s0, inv_of(pred, grammar, start, input, R.initial_inv(pred, grammar, start, input)),
    Lemma.le_trans(1n+Run.meas(grammar, input, s0), 1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F, R.initial_meas(pred, grammar, start, input), hf))

# THE EXACT PARSER ANSWERS: with fuel 1 + twice the size of the descriptor universe,
# `exactSteps` hands out its steps, on every grammar and input.
law exact_parser_answers:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {N.isSteps(Exact.exactSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, start, input)) == True{} : Bool}

def exact_parser_answers(grammar, start, input):
  +F = {1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) : Nat}
  +hf1 = {Lemma.le_add_right(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) : {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F) == True{} : Bool}}
  ex1(Gll.parseWith(F, Gll.NoPred{}, grammar, start, input), F, grammar, start, input, {==}, gll_done_with(F, Gll.NoPred{}, grammar, start, input, hf1), hf1, Lemma.le_refl(F))

# THE PREDICTING PARSER ANSWERS: with fuel 1 + the size of the descriptor universe + the
# table size (PROOF_GROW.bend), the tables close and the engine with their predict sets
# finishes, so `predictedSteps` hands out its steps, on every grammar and input.
law predicted_parser_answers:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(P.predictedSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), GW.tableSize(grammar, start)), grammar, start, input)) == True{} : Bool}

def predicted_parser_answers(grammar, start, input):
  +F = {1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), GW.tableSize(grammar, start)) : Nat}
  +hu = {Lemma.le_add_right(List.length(&2, Gll.Desc, Run.univ(grammar, input)), GW.tableSize(grammar, start)) : {Nat.is_le(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), F) == True{} : Bool}}
  +ht = {Lemma.le_add_left(List.length(&2, Gll.Desc, Run.univ(grammar, input)), GW.tableSize(grammar, start)) : {Nat.is_le(1n+GW.tableSize(grammar, start), F) == True{} : Bool}}
  %Equal.sym(Bool, P.tablesClosed(grammar, start, Sets.growNulls(F, grammar, []), T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), T.growFollows(F, grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), Sets.growNulls(F, grammar, []), [T.FollowFact{start, None{}}])), True{}, GW.tables_closed(F, grammar, start, ht)) : {R.isAnswer(P.predictPick(_, F, grammar, start, input, P.predictSets(grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), T.growFollows(F, grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), Sets.growNulls(F, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(F, grammar, [])))) == True{} : Bool}
  R.done_answers(Gll.parseWith(F, Gll.Allowed{P.predictSets(grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), T.growFollows(F, grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), Sets.growNulls(F, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(F, grammar, []))}, grammar, start, input), F, Gll.Allowed{P.predictSets(grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), T.growFollows(F, grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), Sets.growNulls(F, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(F, grammar, []))}, grammar, start, input, {==},
    gll_done_with(F, Gll.Allowed{P.predictSets(grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), T.growFollows(F, grammar, T.growFirsts(F, grammar, Sets.growNulls(F, grammar, []), []), Sets.growNulls(F, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(F, grammar, []))}, grammar, start, input, hu))
