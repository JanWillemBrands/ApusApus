import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./SUPPORT.bend as Sup
import ./PROOF_GLL.bend as G
import ./PROOF_HOLD.bend as H
import ./PROOF_STATE.bend as St
import ./PROOF_TREE.bend as Tr
import ./PROOF_PREDICT.bend as Pp
import ./SETS.bend as Sets

# EVERY FACT OF A SUPPORTED STATE HOLDS WHAT THE RULES KEEP. When the root holds a goal
# (PROOF_HOLD.bend) and every rule keeps it, every reached fact holds it, round by round, so
# every fact of a supported state does. With the goal "a fact of a closed plain state"
# (PROOF_STATE.bend): prediction saves work. With the goal "on the parse tree"
# (PROOF_TREE.bend): the LL(1) parser has no dead wood.

# ======== THE TREE GOAL, FACT BY FACT ========

law hold_of_on:
  for fs: +List<Sup.Fact>
  for +tree: Core.Tree
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Tr.allOn(fs, grammar, Core.steps([tree], 0n)) == True{} : Bool}
  {H.allHold(fs, H.OnTree{tree, nulls, firsts, follows}, grammar, input) == True{} : Bool}

def hold_of_on(fs, tree, nulls, firsts, follows, grammar, input, h):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +hf = {H.onTree(f, grammar, Core.steps([tree], 0n)) : Bool}
      Lemma.and_true_intro(hf, H.allHold(rest, H.OnTree{tree, nulls, firsts, follows}, grammar, input), Lemma.and_true_left(hf, Tr.allOn(rest, grammar, Core.steps([tree], 0n)), h),
        hold_of_on(rest, tree, nulls, firsts, follows, grammar, input, Lemma.and_true_right_side(hf, Tr.allOn(rest, grammar, Core.steps([tree], 0n)), h)))

law on_of_hold:
  for fs: +List<Sup.Fact>
  for +tree: Core.Tree
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {H.allHold(fs, H.OnTree{tree, nulls, firsts, follows}, grammar, input) == True{} : Bool}
  {Tr.allOn(fs, grammar, Core.steps([tree], 0n)) == True{} : Bool}

def on_of_hold(fs, tree, nulls, firsts, follows, grammar, input, h):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +hf = {H.onTree(f, grammar, Core.steps([tree], 0n)) : Bool}
      Lemma.and_true_intro(hf, Tr.allOn(rest, grammar, Core.steps([tree], 0n)), Lemma.and_true_left(hf, H.allHold(rest, H.OnTree{tree, nulls, firsts, follows}, grammar, input), h),
        on_of_hold(rest, tree, nulls, firsts, follows, grammar, input, Lemma.and_true_right_side(hf, H.allHold(rest, H.OnTree{tree, nulls, firsts, follows}, grammar, input), h)))

# ======== THE INDUCTION ========

law rule_ok:
  for goal: H.Goal
  for +f: Sup.Fact
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {H.goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hf: {H.holdsF(goal, f, grammar, input) == True{} : Bool}
  for +hr: {H.allHold(reached, goal, grammar, input) == True{} : Bool}
  {H.allHold(Sup.factGives(f, H.predOf(goal, grammar), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def rule_ok(goal, f, grammar, start, input, reached, ok, hf, hr):
  match goal:
    case H.InState{+s, +pr}:
      St.rule_in(f, s, pr, grammar, input, reached, Lemma.and_true_left(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), ok), hf, hr)
    case H.OnTree{+tree, +nulls, +firsts, +follows}:
      +tr = {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) : Bool}
      +tl = {Nat.is_eq(List.length(&2, Nat, Core.leaves([tree])), List.length(&2, Nat, input)) : Bool}
      +chk = {T.checkWith(grammar, start, nulls, firsts, follows) : Bool}
      +rest = Lemma.and_true_right_side(chk, Bool.and(tr, tl), ok)
      +rl = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves([tree])), List.length(&2, Nat, input), Lemma.and_true_right_side(tr, tl, rest))
      hold_of_on(Sup.factGives(f, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, reached), tree, nulls, firsts, follows, grammar, input,
        Tr.rule_on(f, grammar, start, input, tree, Lemma.and_true_left(tr, tl, rest), rl, nulls, firsts, follows, Lemma.and_true_left(chk, Bool.and(tr, tl), ok), reached, hf,
          on_of_hold(reached, tree, nulls, firsts, follows, grammar, input, hr)))

law give_all:
  for fs: +List<Sup.Fact>
  for +goal: H.Goal
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {H.goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hfs: {H.allHold(fs, goal, grammar, input) == True{} : Bool}
  for +hr: {H.allHold(reached, goal, grammar, input) == True{} : Bool}
  {H.allHold(Sup.allGive(fs, H.predOf(goal, grammar), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def give_all(fs, goal, grammar, start, input, reached, ok, hfs, hr):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +hf = {H.holdsF(goal, f, grammar, input) : Bool}
      H.hold_join(Sup.factGives(f, H.predOf(goal, grammar), grammar, input, reached), Sup.allGive(rest, H.predOf(goal, grammar), grammar, input, reached), goal, grammar, input,
        rule_ok(goal, f, grammar, start, input, reached, ok, Lemma.and_true_left(hf, H.allHold(rest, goal, grammar, input), hfs), hr),
        give_all(rest, goal, grammar, start, input, reached, ok, Lemma.and_true_right_side(hf, H.allHold(rest, goal, grammar, input), hfs), hr))

# Every reached fact holds the goal.
law grow_hold:
  for n: Nat
  for +goal: H.Goal
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {H.goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hr: {H.allHold(reached, goal, grammar, input) == True{} : Bool}
  {H.allHold(Sup.growReached(n, H.predOf(goal, grammar), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def grow_hold(n, goal, grammar, start, input, reached, ok, hr):
  match n:
    case 0n:
      hr
    case 1n+(+p):
      +next = Sup.addNew(Sup.allGive(reached, H.predOf(goal, grammar), grammar, input, reached), reached)
      grow_hold(p, goal, grammar, start, input, next, ok,
        H.hold_add(Sup.allGive(reached, H.predOf(goal, grammar), grammar, input, reached), reached, goal, grammar, input, give_all(reached, goal, grammar, start, input, reached, ok, hr, hr), hr))

# ======== PREDICTION SAVES WORK ========

law hold_within:
  for fs: +List<Sup.Fact>
  for +s: Gll.GState
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {H.allHold(fs, H.InState{s, pr}, grammar, input) == True{} : Bool}
  {Sup.factsWithin(fs, s) == True{} : Bool}

def hold_within(fs, s, pr, grammar, input, h):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      Lemma.and_true_intro(Sup.inState(f, s), Sup.factsWithin(rest, s), Lemma.and_true_left(Sup.inState(f, s), H.allHold(rest, H.InState{s, pr}, grammar, input), h),
        hold_within(rest, s, pr, grammar, input, Lemma.and_true_right_side(Sup.inState(f, s), H.allHold(rest, H.InState{s, pr}, grammar, input), h)))

def stateOr(m: Maybe<&2, Gll.GState>, +d: Gll.GState) -> Gll.GState:
  match m:
    case Some{+x}:
      x
    case None{}:
      d

def isNoState(m: Maybe<&2, Gll.GState>) -> Bool:
  match m:
    case Some{x}:
      False{}
    case None{}:
      True{}

law none_state:
  for +s: Gll.GState
  for +e: {None{} == Some{s} : Maybe<&2, Gll.GState>}
  Empty

def none_state(s, e):
  Lemma.true_is_not_false(Equal.cong(Maybe<&2, Gll.GState>, Bool, v => isNoState(v), None{}, Some{s}, e))

def plain_pick(b: Bool, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +plain: Gll.GState,
  +eb: {b == Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))) : Bool},
  +e: {Sup.statePick(b, s) == Some{plain} : Maybe<&2, Gll.GState>},
  +pr: Gll.Pred) -> {H.goalOk(H.InState{plain, pr}, grammar, start, input) == True{} : Bool}:
  match b:
    case True{}:
      +sp = Equal.cong(Maybe<&2, Gll.GState>, Gll.GState, v => stateOr(v, s), Some{s}, Some{plain}, e)
      %sp : {H.goalOk(H.InState{_, pr}, grammar, start, input) == True{} : Bool}
      Equal.sym(Bool, True{}, Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), eb)
    case False{}:
      Empty.absurd({H.goalOk(H.InState{plain, pr}, grammar, start, input) == True{} : Bool}, none_state(plain, e))

def plain_run(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +plain: Gll.GState, +pr: Gll.Pred,
  +e: {Sup.closedPick(r, grammar, start, input) == Some{plain} : Maybe<&2, Gll.GState>}) -> {H.goalOk(H.InState{plain, pr}, grammar, start, input) == True{} : Bool}:
  match r:
    case Gll.GDone{+s}:
      plain_pick(Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), grammar, start, input, s, plain, {==}, e, pr)
    case Gll.OutOfFuel{+s}:
      Empty.absurd({H.goalOk(H.InState{plain, pr}, grammar, start, input) == True{} : Bool}, none_state(plain, e))

def other_pick(b: Bool, +fuel: Nat, +pr: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +s: Gll.GState, +other: Gll.GState,
  +eb: {b == Sup.supported(fuel, pr, grammar, start, input, s) : Bool},
  +e: {Sup.statePick(b, s) == Some{other} : Maybe<&2, Gll.GState>}) -> {Sup.supported(fuel, pr, grammar, start, input, other) == True{} : Bool}:
  match b:
    case True{}:
      +sp = Equal.cong(Maybe<&2, Gll.GState>, Gll.GState, v => stateOr(v, s), Some{s}, Some{other}, e)
      %sp : {Sup.supported(fuel, pr, grammar, start, input, _) == True{} : Bool}
      Equal.sym(Bool, True{}, Sup.supported(fuel, pr, grammar, start, input, s), eb)
    case False{}:
      Empty.absurd({Sup.supported(fuel, pr, grammar, start, input, other) == True{} : Bool}, none_state(other, e))

def other_run(r: Gll.GRun, +fuel: Nat, +pr: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +other: Gll.GState,
  +e: {Sup.supportedPick(r, fuel, pr, grammar, start, input) == Some{other} : Maybe<&2, Gll.GState>}) -> {Sup.supported(fuel, pr, grammar, start, input, other) == True{} : Bool}:
  match r:
    case Gll.GDone{+s}:
      other_pick(Sup.supported(fuel, pr, grammar, start, input, s), fuel, pr, grammar, start, input, s, other, {==}, e)
    case Gll.OutOfFuel{+s}:
      Empty.absurd({Sup.supported(fuel, pr, grammar, start, input, other) == True{} : Bool}, none_state(other, e))

# PREDICTION SAVES WORK: whenever the plain engine's final state is closed and an engine
# run with any predictor ends in a supported state, every fact of the second is a fact of
# the first. The predicting engine has no descriptor, step or edge the plain one lacks.
law predict_saves_work:
  for fuelPlain: Nat
  for fuelOther: Nat
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +plain: Gll.GState
  for +other: Gll.GState
  for +gotPlain: {Sup.closedState(fuelPlain, grammar, start, input) == Some{plain} : Maybe<&2, Gll.GState>}
  for +gotOther: {Sup.supportedState(fuelOther, pr, grammar, start, input) == Some{other} : Maybe<&2, Gll.GState>}
  {Sup.factsWithin(Sup.factsOf(other), plain) == True{} : Bool}

def predict_saves_work(fuelPlain, fuelOther, pr, grammar, start, input, plain, other, gotPlain, gotOther):
  +fo = fuelOther
  +goal = {H.InState{plain, pr} : H.Goal}
  +ok = plain_run(Gll.parse(fuelPlain, grammar, start, input), grammar, start, input, plain, pr, gotPlain)
  +sup = other_run(Gll.parseWith(fo, pr, grammar, start, input), fo, pr, grammar, start, input, other, gotOther)
  +root = Lemma.and_true_right_side(Check.closed(grammar, input, plain), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(plain)), ok)
  +hr0 = Lemma.and_true_intro(Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(plain)), True{}, root, {==})
  +reached = Sup.growReached(fo, pr, grammar, input, Sup.roots(start))
  +hr = grow_hold(fo, goal, grammar, start, input, Sup.roots(start), ok, hr0)
  hold_within(Sup.factsOf(other), plain, pr, grammar, input, H.in_reached(Sup.factsOf(other), reached, goal, grammar, input, sup, hr))

# ======== NO DEAD WOOD FOR AN LL(1) GRAMMAR ========

law hold_right:
  for a: +List<Sup.Fact>
  for +b: +List<Sup.Fact>
  for +goal: H.Goal
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {H.allHold(Sup.joinFacts(a, b), goal, grammar, input) == True{} : Bool}
  {H.allHold(b, goal, grammar, input) == True{} : Bool}

def hold_right(a, b, goal, grammar, input, h):
  match a:
    case Nil{}:
      h
    case Con{+f, +rest}:
      hold_right(rest, b, goal, grammar, input, Lemma.and_true_right_side(H.holdsF(goal, f, grammar, input), H.allHold(Sup.joinFacts(rest, b), goal, grammar, input), h))

def step_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +hy: {Core.member(y, set) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, set) == True{} : Bool}) -> {Core.member(x, set) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Core.member(_, set) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law steps_hold:
  for ys: +List<Core.Bsr>
  for +x: Core.Bsr
  for +tree: Core.Tree
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {H.allHold(Sup.stepFacts(ys), H.OnTree{tree, nulls, firsts, follows}, grammar, input) == True{} : Bool}
  for +m: {Core.member(x, ys) == True{} : Bool}
  {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}

def steps_hold(ys, x, tree, nulls, firsts, follows, grammar, input, h, m):
  match ys:
    case Nil{}:
      Empty.absurd({Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +S = Core.steps([tree], 0n)
      +hrest = {H.allHold(Sup.stepFacts(rest), H.OnTree{tree, nulls, firsts, follows}, grammar, input) : Bool}
      step_pick(x, y, rest, S, Lemma.and_true_left(Core.member(y, S), hrest, h), Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        m2 => steps_hold(rest, x, tree, nulls, firsts, follows, grammar, input, Lemma.and_true_right_side(Core.member(y, S), hrest, h), m2))

def state_steps(s: Gll.GState, +x: Core.Bsr, +tree: Core.Tree, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +h: {H.allHold(Sup.factsOf(s), H.OnTree{tree, nulls, firsts, follows}, grammar, input) == True{} : Bool},
  +m: {Core.member(x, Check.stepsOf(s)) == True{} : Bool}) -> {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}:
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      +goal = {H.OnTree{tree, nulls, firsts, follows} : H.Goal}
      +f4 = Sup.joinFacts(Sup.popFacts(ps), Sup.stepFacts(ys))
      +f3 = Sup.joinFacts(Sup.retFacts(rs), f4)
      +f2 = Sup.joinFacts(Sup.clusterFacts(cs), f3)
      +h2 = hold_right(Sup.descFacts(seen), f2, goal, grammar, input, h)
      +h3 = hold_right(Sup.clusterFacts(cs), f3, goal, grammar, input, h2)
      +h4 = hold_right(Sup.retFacts(rs), f4, goal, grammar, input, h3)
      steps_hold(ys, x, tree, nulls, firsts, follows, grammar, input, hold_right(Sup.popFacts(ps), Sup.stepFacts(ys), goal, grammar, input, h4), m)

def set_member(+s: Gll.GState, +set: +List<Core.Bsr>, +x: Core.Bsr, +es: {Check.stepsOf(s) == set : +List<Core.Bsr>},
  +m: {Core.member(x, set) == True{} : Bool}) -> {Core.member(x, Check.stepsOf(s)) == True{} : Bool}:
  %Equal.sym(+List<Core.Bsr>, Check.stepsOf(s), set, es) : {Core.member(x, _) == True{} : Bool}
  m

# A step the LL(1) parser hands out is a step of the parse tree: every fact of the
# supported state lies on the tree.
def only_step(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +s: Gll.GState,
  +sup: {Sup.supported(fuel, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, start, input, s) == True{} : Bool},
  +x: Core.Bsr,
  +ms: {Core.member(x, Check.stepsOf(s)) == True{} : Bool}) -> {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}:
  +goal = {H.OnTree{tree, nulls, firsts, follows} : H.Goal}
  +tr = {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) : Bool}
  +lenT = List.length(&2, Nat, Core.leaves([tree]))
  +lenI = List.length(&2, Nat, input)
  +gok = Lemma.and_true_intro(T.checkWith(grammar, start, nulls, firsts, follows), Bool.and(tr, Nat.is_eq(lenT, lenI)), ok,
    Lemma.and_true_intro(tr, Nat.is_eq(lenT, lenI), rr, Tr.eq_true(lenT, lenI, rl)))
  +hr0 = hold_of_on(Sup.roots(start), tree, nulls, firsts, follows, grammar, input, Tr.root_on(grammar, start, input, tree, rr))
  +hr = grow_hold(fuel, goal, grammar, start, input, Sup.roots(start), gok, hr0)
  +reached = Sup.growReached(fuel, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, Sup.roots(start))
  state_steps(s, x, tree, nulls, firsts, follows, grammar, input, H.in_reached(Sup.factsOf(s), reached, goal, grammar, input, sup, hr), ms)

def only_pair(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +s: Gll.GState, +set: +List<Core.Bsr>,
  +sup: {Sup.supported(fuel, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, start, input, s) == True{} : Bool},
  +es: {Check.stepsOf(s) == set : +List<Core.Bsr>},
  +x: Core.Bsr, +m: {Core.member(x, set) == True{} : Bool})
  -> &t: Core.Tree -> Core.ParseTree(grammar, start, input, t) & {Core.member(x, Core.steps([t], 0n)) == True{} : Bool}:
  (tree, ((rr, rl), only_step(fuel, grammar, start, input, nulls, firsts, follows, tree, rr, rl, ok, s, sup, x, set_member(s, set, x, es, m))))

def ll1_state(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +s: Gll.GState, +set: +List<Core.Bsr>,
  +eb: {b == Bool.and(Bool.and(Check.closedWith(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), Sup.supported(fuel, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, start, input, s)) : Bool},
  +e: {Check.checkPick(b, s) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.IsExact(grammar, start, input, set):
  match b:
    case True{}:
      +pred = {Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)} : Gll.Pred}
      +cl = {Bool.and(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))) : Bool}
      +both = Equal.sym(Bool, True{}, Bool.and(cl, Sup.supported(fuel, pred, grammar, start, input, s)), eb)
      +hcr = Lemma.and_true_left(cl, Sup.supported(fuel, pred, grammar, start, input, s), both)
      +sup = Lemma.and_true_right_side(cl, Sup.supported(fuel, pred, grammar, start, input, s), both)
      +hc = Lemma.and_true_left(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), hcr)
      +root = Lemma.and_true_right_side(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), hcr)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Check.stepsOf(s)}, Some{set}, e)
      +a1 = {Sets.nullsClosed(grammar, nulls) : Bool}
      +a2 = {T.firstsClosed(grammar, firsts, nulls) : Bool}
      +a3 = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
      +a4 = {T.followHas(start, None{}, follows) : Bool}
      +a5 = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
      +a6 = {T.pairsOk(grammar, firsts, follows, nulls) : Bool}
      +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
      +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
      +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
      +r4 = Lemma.and_true_right_side(a4, Bool.and(a5, a6), r3)
      +cn = Lemma.and_true_left(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
      +cf = Lemma.and_true_left(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
      +cfo = Lemma.and_true_left(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
      +cs = Lemma.and_true_left(a4, Bool.and(a5, a6), r3)
      +cr = Lemma.and_true_left(a5, a6, r4)
      (t2 => x => pt => m => Pp.from_tree(grammar, start, input, firsts, follows, nulls, s, set, cn, cf, cfo, cs, cr, hc, root, es, t2, x, pt, m),
       x => m => only_pair(fuel, grammar, start, input, nulls, firsts, follows, tree, rr, rl, ok, s, set, sup, es, x, m))
    case False{}:
      Empty.absurd(Core.IsExact(grammar, start, input, set), G.none_not_some(set, e))

def ll1_run(r: Gll.GRun, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +set: +List<Core.Bsr>,
  +e: {Pr.ll1Run(r, fuel, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.IsExact(grammar, start, input, set):
  match r:
    case Gll.GDone{+s}:
      +pred = {Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)} : Gll.Pred}
      ll1_state(Bool.and(Bool.and(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), Sup.supported(fuel, pred, grammar, start, input, s)),
        fuel, grammar, start, input, nulls, firsts, follows, tree, rr, rl, ok, s, set, {==}, e)
    case Gll.OutOfFuel{+s}:
      Empty.absurd(Core.IsExact(grammar, start, input, set), G.none_not_some(set, e))

def ll1_tables(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +set: +List<Core.Bsr>,
  +eb: {b == T.checkWith(grammar, start, nulls, firsts, follows) : Bool},
  +e: {Pr.ll1Pick(b, fuel, grammar, start, input, Pr.predictSets(grammar, firsts, follows, nulls)) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.IsExact(grammar, start, input, set):
  match b:
    case True{}:
      +sets = Pr.predictSets(grammar, firsts, follows, nulls)
      ll1_run(Gll.parseWith(fuel, Gll.Allowed{sets}, grammar, start, input), fuel, grammar, start, input, nulls, firsts, follows, tree, rr, rl,
        Equal.sym(Bool, True{}, T.checkWith(grammar, start, nulls, firsts, follows), eb), set, e)
    case False{}:
      Empty.absurd(Core.IsExact(grammar, start, input, set), G.none_not_some(set, e))

# NO DEAD WOOD FOR AN LL(1) GRAMMAR: when the input has a parse tree and the LL(1) parser
# (PREDICT.bend: LL(1) tables, prediction, a closed and supported final state) hands out a
# set of steps, the set is exact: the steps of the parse trees and nothing else.
law ll1_no_dead_wood:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +tree: Core.Tree
  for pt: Core.ParseTree(grammar, start, input, tree)
  for +got: {Pr.ll1Steps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.IsExact(grammar, start, input, set)

def ll1_no_dead_wood(fuel, grammar, start, input, set, tree, pt, got):
  match pt:
    case (+rr, +rl):
      +f = fuel
      +nulls = Sets.growNulls(f, grammar, [])
      +firsts = T.growFirsts(f, grammar, nulls, [])
      +follows = T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}])
      ll1_tables(T.checkWith(grammar, start, nulls, firsts, follows), f, grammar, start, input, nulls, firsts, follows, tree, rr, rl, set, {==}, got)
