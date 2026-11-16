import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./SUPPORT.bend as Sup
import ./PROOF_GLL.bend as G

# WHAT A REACHED FACT MUST HOLD. A goal says what every fact derivable by the engine's rules
# must hold; when the root holds it and every rule keeps it, every reached fact does
# (PROOF_SUPPORT.bend). Two goals: being a fact of a closed state of the plain engine
# (PROOF_STATE.bend), and lying on a given parse tree of an LL(1) grammar (PROOF_TREE.bend).

# ======== ON THE TREE ========

# What a fact on the tree is asked of a step of the tree.
type Ask is Data:
  AskDesc{q: Nat, d: Nat, k: Nat, i: Nat}
  AskCluster{x: Nat, i: Nat}
  AskPop{x: Nat, k: Nat, j: Nat}

# AskDesc: a step of a node of q at k that ends at i after d items (or any step of such a
# node when d is 0 and i is k). AskCluster: a step of a node of x at i. AskPop: the last
# step of a node of x at k, ending at j.
def askAt(ask: Ask, y: Core.Bsr, +grammar: +List<Core.Production>) -> Bool:
  match ask y:
    case AskDesc{+q, +d, +k, +i} Core.Bsr{+yq, +yd, +yi, yk, +yj}:
      Bool.and(Nat.is_eq(yq, q), Bool.and(Nat.is_eq(yi, k), Bool.or(Bool.and(Nat.is_eq(yd, d), Nat.is_eq(yj, i)), Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k)))))
    case AskCluster{+x, +i} Core.Bsr{+yq, yd, +yi, yk, yj}:
      Bool.and(Nat.is_eq(Gll.lhsOf(grammar, yq), x), Nat.is_eq(yi, i))
    case AskPop{+x, +k, +j} Core.Bsr{+yq, +yd, +yi, yk, +yj}:
      Bool.and(Nat.is_eq(Gll.lhsOf(grammar, yq), x), Bool.and(Nat.is_eq(yi, k), Bool.and(Nat.is_eq(yd, List.length(&2, Core.Sym, Core.rhsOf(grammar, yq))), Nat.is_eq(yj, j))))

def anyStep(ys: +List<Core.Bsr>, +ask: Ask, +grammar: +List<Core.Production>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(askAt(ask, y, grammar), anyStep(rest, ask, grammar))

def ntIs(item: Maybe<&2, Core.Sym>, +x: Nat) -> Bool:
  match item:
    case Some{Core.Nonterminal{+z, need}}:
      Nat.is_eq(z, x)
    case Some{Core.Terminal{t}}:
      False{}
    case None{}:
      False{}

# The fact lies on the tree whose steps are `set`.
def onTree(f: Sup.Fact, +grammar: +List<Core.Production>, +set: +List<Core.Bsr>) -> Bool:
  match f:
    case Sup.FDesc{Gll.Desc{+q, +d, +k, +i}}:
      anyStep(set, AskDesc{q, d, k, i}, grammar)
    case Sup.FCluster{Gll.CKey{+x, +i}}:
      anyStep(set, AskCluster{x, i}, grammar)
    case Sup.FRet{Gll.CKey{+x, +i}, Gll.Edge{+q, +d, +k}}:
      Bool.and(anyStep(set, AskDesc{q, d, k, i}, grammar), ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x))
    case Sup.FPop{Gll.CKey{+x, +k}, +j}:
      anyStep(set, AskPop{x, k, j}, grammar)
    case Sup.FStep{+y}:
      Core.member(y, set)

# ======== GOALS ========

type Goal is Data:
  InState{s: Gll.GState, pr: Gll.Pred}
  OnTree{tree: Core.Tree, nulls: +List<Nat>, firsts: +List<T.FirstFact>, follows: +List<T.FollowFact>}

# The predictor of the run the goal speaks about.
def predOf(goal: Goal, +grammar: +List<Core.Production>) -> Gll.Pred:
  match goal:
    case InState{s, +pr}:
      pr
    case OnTree{tree, +nulls, +firsts, +follows}:
      Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}

def holdsF(goal: Goal, f: Sup.Fact, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match goal:
    case InState{+s, pr}:
      Sup.inState(f, s)
    case OnTree{+tree, nulls, firsts, follows}:
      onTree(f, grammar, Core.steps([tree], 0n))

def allHold(fs: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, rest}:
      Bool.and(holdsF(goal, f, grammar, input), allHold(rest, goal, grammar, input))

# InState: the plain engine's state is closed and has the start symbol's cluster. OnTree:
# the tables pass the LL(1) check and the tree is a parse tree of the input.
def goalOk(goal: Goal, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Bool:
  match goal:
    case InState{+s, pr}:
      Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)))
    case OnTree{+tree, +nulls, +firsts, +follows}:
      Bool.and(T.checkWith(grammar, start, nulls, firsts, follows),
        Bool.and(Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([tree])), List.length(&2, Nat, input))))

# ======== LISTS OF FACTS ========

law hold_join:
  for a: +List<Sup.Fact>
  for +b: +List<Sup.Fact>
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ha: {allHold(a, goal, grammar, input) == True{} : Bool}
  for +hb: {allHold(b, goal, grammar, input) == True{} : Bool}
  {allHold(Sup.joinFacts(a, b), goal, grammar, input) == True{} : Bool}

def hold_join(a, b, goal, grammar, input, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+x, +rest}:
      +hx = {holdsF(goal, x, grammar, input) : Bool}
      Lemma.and_true_intro(hx, allHold(Sup.joinFacts(rest, b), goal, grammar, input), Lemma.and_true_left(hx, allHold(rest, goal, grammar, input), ha),
        hold_join(rest, b, goal, grammar, input, Lemma.and_true_right_side(hx, allHold(rest, goal, grammar, input), ha), hb))

def add_pick(have: Bool, +f: Sup.Fact, +acc: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hf: {holdsF(goal, f, grammar, input) == True{} : Bool},
  +ha: {allHold(acc, goal, grammar, input) == True{} : Bool}) -> {allHold(Sup.addPick(have, f, acc), goal, grammar, input) == True{} : Bool}:
  match have:
    case True{}:
      ha
    case False{}:
      Lemma.and_true_intro(holdsF(goal, f, grammar, input), allHold(acc, goal, grammar, input), hf, ha)

law hold_add:
  for new: +List<Sup.Fact>
  for +acc: +List<Sup.Fact>
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hn: {allHold(new, goal, grammar, input) == True{} : Bool}
  for +ha: {allHold(acc, goal, grammar, input) == True{} : Bool}
  {allHold(Sup.addNew(new, acc), goal, grammar, input) == True{} : Bool}

def hold_add(new, acc, goal, grammar, input, hn, ha):
  match new:
    case Nil{}:
      ha
    case Con{+f, +rest}:
      +hf = {holdsF(goal, f, grammar, input) : Bool}
      hold_add(rest, Sup.addPick(Sup.factIn(f, acc), f, acc), goal, grammar, input, Lemma.and_true_right_side(hf, allHold(rest, goal, grammar, input), hn),
        add_pick(Sup.factIn(f, acc), f, acc, goal, grammar, input, Lemma.and_true_left(hf, allHold(rest, goal, grammar, input), hn), ha))

# ======== EQUAL FACTS ========

law fact_eq_sound:
  for a: Sup.Fact
  for b: Sup.Fact
  for +e: {Sup.factEq(a, b) == True{} : Bool}
  {a == b : Sup.Fact}

def fact_eq_sound(a, b, e):
  match a b:
    case Sup.FDesc{+x} Sup.FDesc{+y}:
      Equal.cong(Gll.Desc, Sup.Fact, v => Sup.FDesc{v}, x, y, G.desc_eq_sound(x, y, e))
    case Sup.FCluster{+x} Sup.FCluster{+y}:
      Equal.cong(Gll.CKey, Sup.Fact, v => Sup.FCluster{v}, x, y, G.key_eq_sound(x, y, e))
    case Sup.FRet{+k1, +e1} Sup.FRet{+k2, +e2}:
      +ek = G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Check.edgeEq(e1, e2), e))
      +ee = G.edge_eq_sound(e1, e2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Check.edgeEq(e1, e2), e))
      %ek : {Sup.FRet{k1, e1} == Sup.FRet{_, e2} : Sup.Fact}
      %ee : {Sup.FRet{k1, e1} == Sup.FRet{k1, _} : Sup.Fact}
      {==}
    case Sup.FPop{+k1, +j1} Sup.FPop{+k2, +j2}:
      +ek = G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e))
      +ej = Lemma.nat_eq_sound(j1, j2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e))
      %ek : {Sup.FPop{k1, j1} == Sup.FPop{_, j2} : Sup.Fact}
      %ej : {Sup.FPop{k1, j1} == Sup.FPop{k1, _} : Sup.Fact}
      {==}
    case Sup.FStep{+x} Sup.FStep{+y}:
      Equal.cong(Core.Bsr, Sup.Fact, v => Sup.FStep{v}, x, y, G.bsr_eq_sound(x, y, e))
    case Sup.FDesc{+ax} Sup.FCluster{+bx}:
      Empty.absurd({Sup.FDesc{ax} == Sup.FCluster{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FDesc{+ax} Sup.FRet{+bk, +be}:
      Empty.absurd({Sup.FDesc{ax} == Sup.FRet{bk, be} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FDesc{+ax} Sup.FPop{+bk, +bj}:
      Empty.absurd({Sup.FDesc{ax} == Sup.FPop{bk, bj} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FDesc{+ax} Sup.FStep{+bx}:
      Empty.absurd({Sup.FDesc{ax} == Sup.FStep{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FCluster{+ax} Sup.FDesc{+bx}:
      Empty.absurd({Sup.FCluster{ax} == Sup.FDesc{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FCluster{+ax} Sup.FRet{+bk, +be}:
      Empty.absurd({Sup.FCluster{ax} == Sup.FRet{bk, be} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FCluster{+ax} Sup.FPop{+bk, +bj}:
      Empty.absurd({Sup.FCluster{ax} == Sup.FPop{bk, bj} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FCluster{+ax} Sup.FStep{+bx}:
      Empty.absurd({Sup.FCluster{ax} == Sup.FStep{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FRet{+ak, +ae} Sup.FDesc{+bx}:
      Empty.absurd({Sup.FRet{ak, ae} == Sup.FDesc{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FRet{+ak, +ae} Sup.FCluster{+bx}:
      Empty.absurd({Sup.FRet{ak, ae} == Sup.FCluster{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FRet{+ak, +ae} Sup.FPop{+bk, +bj}:
      Empty.absurd({Sup.FRet{ak, ae} == Sup.FPop{bk, bj} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FRet{+ak, +ae} Sup.FStep{+bx}:
      Empty.absurd({Sup.FRet{ak, ae} == Sup.FStep{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FPop{+ak, +aj} Sup.FDesc{+bx}:
      Empty.absurd({Sup.FPop{ak, aj} == Sup.FDesc{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FPop{+ak, +aj} Sup.FCluster{+bx}:
      Empty.absurd({Sup.FPop{ak, aj} == Sup.FCluster{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FPop{+ak, +aj} Sup.FRet{+bk, +be}:
      Empty.absurd({Sup.FPop{ak, aj} == Sup.FRet{bk, be} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FPop{+ak, +aj} Sup.FStep{+bx}:
      Empty.absurd({Sup.FPop{ak, aj} == Sup.FStep{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FStep{+ax} Sup.FDesc{+bx}:
      Empty.absurd({Sup.FStep{ax} == Sup.FDesc{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FStep{+ax} Sup.FCluster{+bx}:
      Empty.absurd({Sup.FStep{ax} == Sup.FCluster{bx} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FStep{+ax} Sup.FRet{+bk, +be}:
      Empty.absurd({Sup.FStep{ax} == Sup.FRet{bk, be} : Sup.Fact}, Lemma.false_is_not_true(e))
    case Sup.FStep{+ax} Sup.FPop{+bk, +bj}:
      Empty.absurd({Sup.FStep{ax} == Sup.FPop{bk, bj} : Sup.Fact}, Lemma.false_is_not_true(e))

def in_pick(+f: Sup.Fact, +g: Sup.Fact, +rest: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hg: {holdsF(goal, g, grammar, input) == True{} : Bool},
  cases: Either<{Sup.factEq(f, g) == True{} : Bool}, {Sup.factIn(f, rest) == True{} : Bool}>,
  later: {Sup.factIn(f, rest) == True{} : Bool} -> {holdsF(goal, f, grammar, input) == True{} : Bool}) -> {holdsF(goal, f, grammar, input) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Sup.Fact, f, g, fact_eq_sound(f, g, e)) : {holdsF(goal, _, grammar, input) == True{} : Bool}
      hg
    case Inr{m}:
      later(m)

law fact_in_hold:
  for reached: +List<Sup.Fact>
  for +f: Sup.Fact
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +m: {Sup.factIn(f, reached) == True{} : Bool}
  for +hr: {allHold(reached, goal, grammar, input) == True{} : Bool}
  {holdsF(goal, f, grammar, input) == True{} : Bool}

def fact_in_hold(reached, f, goal, grammar, input, m, hr):
  match reached:
    case Nil{}:
      Empty.absurd({holdsF(goal, f, grammar, input) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+g, +rest}:
      +hg = {holdsF(goal, g, grammar, input) : Bool}
      in_pick(f, g, rest, goal, grammar, input, Lemma.and_true_left(hg, allHold(rest, goal, grammar, input), hr), Lemma.or_true_cases(Sup.factEq(f, g), Sup.factIn(f, rest), m),
        m2 => fact_in_hold(rest, f, goal, grammar, input, m2, Lemma.and_true_right_side(hg, allHold(rest, goal, grammar, input), hr)))

law in_reached:
  for fs: +List<Sup.Fact>
  for +reached: +List<Sup.Fact>
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +all: {Sup.allFactsIn(fs, reached) == True{} : Bool}
  for +hr: {allHold(reached, goal, grammar, input) == True{} : Bool}
  {allHold(fs, goal, grammar, input) == True{} : Bool}

def in_reached(fs, reached, goal, grammar, input, all, hr):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      Lemma.and_true_intro(holdsF(goal, f, grammar, input), allHold(rest, goal, grammar, input),
        fact_in_hold(reached, f, goal, grammar, input, Lemma.and_true_left(Sup.factIn(f, reached), Sup.allFactsIn(rest, reached), all), hr),
        in_reached(rest, reached, goal, grammar, input, Lemma.and_true_right_side(Sup.factIn(f, reached), Sup.allFactsIn(rest, reached), all), hr))

def if_in(b: Bool, +fs: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>,
  hb: {b == True{} : Bool} -> {allHold(fs, goal, grammar, input) == True{} : Bool}) -> {allHold(Sup.factsIf(b, fs), goal, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      hb({==})
    case False{}:
      {==}

