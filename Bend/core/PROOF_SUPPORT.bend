import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./SUPPORT.bend as Sup
import ./PROOF_GLL.bend as G

# EVERY FACT OF A SUPPORTED STATE HOLDS WHAT THE RULES KEEP. A goal says what a fact must
# hold. When the root holds it and every rule keeps it (`rule_ok`), every reached fact
# holds it, round by round, so every fact of a supported state does. The goal here: being a
# fact of a closed state of the plain engine (`predict_saves_work`).

# ======== GOALS ========

type Goal is Data:
  InState{s: Gll.GState, pr: Gll.Pred}

# The predictor of the run the goal speaks about.
def predOf(goal: Goal) -> Gll.Pred:
  match goal:
    case InState{s, +pr}:
      pr

def holdsF(goal: Goal, f: Sup.Fact, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match goal:
    case InState{+s, pr}:
      Sup.inState(f, s)

def allHold(fs: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, rest}:
      Bool.and(holdsF(goal, f, grammar, input), allHold(rest, goal, grammar, input))

def goalOk(goal: Goal, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Bool:
  match goal:
    case InState{+s, pr}:
      Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)))

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

# ======== THE RULES KEEP: A CLOSED PLAIN STATE ========

def token_in(b: Bool, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +h: {Check.tokenOk(b, q, d, k, i, s) == True{} : Bool}) -> {allHold(Sup.tokenGives(b, q, d, k, i), InState{s, pr}, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+d, k, 1n+i}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+d, k, i, 1n+i}, s) : Bool}
      Lemma.and_true_intro(sd, Bool.and(sy, True{}), Lemma.and_true_left(sd, sy, h), Lemma.and_true_intro(sy, True{}, Lemma.and_true_right_side(sd, sy, h), {==}))
    case False{}:
      {==}

def empty_in(d: Nat, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +k: Nat, +i: Nat,
  +h: {Check.emptyOk(d, q, k, i, s) == True{} : Bool}) -> {allHold(Sup.emptyGives(d, q, k, i), InState{s, pr}, grammar, input) == True{} : Bool}:
  match d:
    case 0n:
      Lemma.and_true_intro(Check.stepIn(Core.Bsr{q, 0n, k, i, i}, s), True{}, h, {==})
    case 1n+(+e):
      {==}

def item_in(item: Maybe<&2, Core.Sym>, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +h: {Check.itemOk(item, grammar, input, q, d, k, i, s) == True{} : Bool}) -> {allHold(Sup.itemGives(item, grammar, input, q, d, k, i), InState{s, pr}, grammar, input) == True{} : Bool}:
  match item:
    case Some{Core.Terminal{+t}}:
      token_in(Core.tokIs(Core.tokAt(input, i), t), s, pr, grammar, input, q, d, k, i, h)
    case Some{Core.Nonterminal{+x, +need}}:
      +kc = {Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(s)) : Bool}
      +kr = {Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, d, k}, Check.returnsOf(s)) : Bool}
      Lemma.and_true_intro(kc, Bool.and(kr, True{}), Lemma.and_true_left(kc, kr, h), Lemma.and_true_intro(kr, True{}, Lemma.and_true_right_side(kc, kr, h), {==}))
    case None{}:
      +em = {Check.emptyOk(d, q, k, i, s) : Bool}
      +po = {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(s)) : Bool}
      Lemma.and_true_intro(po, allHold(Sup.emptyGives(d, q, k, i), InState{s, pr}, grammar, input), Lemma.and_true_right_side(em, po, h),
        empty_in(d, s, pr, grammar, input, q, k, i, Lemma.and_true_left(em, po, h)))

def desc_in(d: Gll.Desc, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hf: {Check.seenIn(d, s) == True{} : Bool}) -> {allHold(Sup.descGives(d, grammar, input), InState{s, pr}, grammar, input) == True{} : Bool}:
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      item_in(Gll.nthSym(Core.rhsOf(grammar, q), dot), s, pr, grammar, input, q, dot, k, i,
        G.desc_ok(Check.seenOf(s), Gll.Desc{q, dot, k, i}, grammar, input, s, G.closed_descs(Gll.NoPred{}, grammar, input, s, hc), hf))

def seed_pick(a: Bool, b: Bool, +d: Gll.Desc, +plainRest: +List<Gll.Desc>, +predRest: +List<Gll.Desc>, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +h: {Check.allSeen(Gll.keepDesc(b, d, plainRest), s) == True{} : Bool},
  later: {Check.allSeen(plainRest, s) == True{} : Bool} -> {allHold(Sup.descFacts(predRest), InState{s, pr}, grammar, input) == True{} : Bool})
  -> {allHold(Sup.descFacts(Gll.keepDesc(Bool.and(a, b), d, predRest)), InState{s, pr}, grammar, input) == True{} : Bool}:
  match a b:
    case True{} True{}:
      Lemma.and_true_intro(Check.seenIn(d, s), allHold(Sup.descFacts(predRest), InState{s, pr}, grammar, input),
        Lemma.and_true_left(Check.seenIn(d, s), Check.allSeen(plainRest, s), h), later(Lemma.and_true_right_side(Check.seenIn(d, s), Check.allSeen(plainRest, s), h)))
    case False{} True{}:
      later(Lemma.and_true_right_side(Check.seenIn(d, s), Check.allSeen(plainRest, s), h))
    case True{} False{}:
      later(h)
    case False{} False{}:
      later(h)

# The predictor's seeds are among the plain ones.
law seeds_in:
  for g: +List<Core.Production>
  for +pr: Gll.Pred
  for +tok: Maybe<&2, Nat>
  for +x: Nat
  for +base: Nat
  for +i: Nat
  for +s: Gll.GState
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Check.allSeen(Gll.productionsOf(g, Gll.NoPred{}, tok, x, base, i), s) == True{} : Bool}
  {allHold(Sup.descFacts(Gll.productionsOf(g, pr, tok, x, base, i)), InState{s, pr}, grammar, input) == True{} : Bool}

def seeds_in(g, pr, tok, x, base, i, s, grammar, input, h):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      seed_pick(Gll.admits(pr, base, tok), Nat.is_eq(lhs, x), Gll.Desc{base, 0n, i, i}, Gll.productionsOf(rest, Gll.NoPred{}, tok, x, 1n+base, i), Gll.productionsOf(rest, pr, tok, x, 1n+base, i), s, pr, grammar, input, h,
        h2 => seeds_in(rest, pr, tok, x, 1n+base, i, s, grammar, input, h2))

def resume_pick(b: Bool, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat,
  +h: {Check.resumeOk(b, q, dot, k, kc, j, s) == True{} : Bool}) -> {allHold(Sup.resumeOk(b, q, dot, k, kc, j), InState{s, pr}, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, s) : Bool}
      Lemma.and_true_intro(sd, Bool.and(sy, True{}), Lemma.and_true_left(sd, sy, h), Lemma.and_true_intro(sy, True{}, Lemma.and_true_right_side(sd, sy, h), {==}))
    case False{}:
      {==}

def resume_in(edge: Gll.Edge, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +kc: Nat, +j: Nat,
  +h: {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}) -> {allHold(Sup.resumeGives(edge, grammar, kc, j), InState{s, pr}, grammar, input) == True{} : Bool}:
  match edge:
    case Gll.Edge{+q, +dot, +k}:
      resume_pick(Gll.needHolds(Gll.needAt(grammar, q, dot), kc, j), s, pr, grammar, input, q, dot, k, kc, j, h)

# A return edge and a pop of its cluster, both in the closed state: the resumed facts are too.
def joined_in(key: Gll.CKey, +edge: Gll.Edge, +j: Nat, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hret: {Check.retIn(key, edge, Check.returnsOf(s)) == True{} : Bool},
  +hpop: {Gll.popIn(key, j, Check.popsOf(s)) == True{} : Bool}) -> {allHold(Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), InState{s, pr}, grammar, input) == True{} : Bool}:
  match key:
    case Gll.CKey{+x, +kc}:
      +ep = G.ret_ok(Check.returnsOf(s), Gll.CKey{x, kc}, edge, grammar, Check.popsOf(s), s, G.closed_returns(Gll.NoPred{}, grammar, input, s, hc), hret)
      resume_in(edge, s, pr, grammar, input, kc, j, G.pop_ok(Check.popsOf(s), x, kc, edge, j, grammar, s, ep, hpop))

def if_in(b: Bool, +fs: +List<Sup.Fact>, +goal: Goal, +grammar: +List<Core.Production>, +input: +List<Nat>,
  hb: {b == True{} : Bool} -> {allHold(fs, goal, grammar, input) == True{} : Bool}) -> {allHold(Sup.factsIf(b, fs), goal, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      hb({==})
    case False{}:
      {==}

law ret_in:
  for rs: +List<Sup.Fact>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +s: Gll.GState
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hc: {Check.closed(grammar, input, s) == True{} : Bool}
  for +hret: {Check.retIn(key, edge, Check.returnsOf(s)) == True{} : Bool}
  for +hr: {allHold(rs, InState{s, pr}, grammar, input) == True{} : Bool}
  {allHold(Sup.retGives(rs, grammar, key, edge), InState{s, pr}, grammar, input) == True{} : Bool}

def ret_in(rs, key, edge, s, pr, grammar, input, hc, hret, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FPop{+k2, +j}, +rest}:
      +goal = {InState{s, pr} : Goal}
      +hp = {Gll.popIn(k2, j, Check.popsOf(s)) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      hold_join(mine, Sup.retGives(rest, grammar, key, edge), goal, grammar, input,
        if_in(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), goal, grammar, input,
          eb => joined_in(key, edge, j, s, pr, grammar, input, hc, hret,
            {(%Equal.sym(Gll.CKey, key, k2, G.key_eq_sound(key, k2, eb)) : {Gll.popIn(_, j, Check.popsOf(s)) == True{} : Bool}
              Lemma.and_true_left(hp, allHold(rest, goal, grammar, input), hr)) : {Gll.popIn(key, j, Check.popsOf(s)) == True{} : Bool}})),
        ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(hp, allHold(rest, goal, grammar, input), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.seenIn(d, s), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Gll.keyIn(c, Check.clustersOf(s)), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FRet{+k2, +e2}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.retIn(k2, e2, Check.returnsOf(s)), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FStep{+y}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.stepIn(y, s), allHold(rest, InState{s, pr}, grammar, input), hr))

law pop_in:
  for rs: +List<Sup.Fact>
  for +key: Gll.CKey
  for +j: Nat
  for +s: Gll.GState
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hc: {Check.closed(grammar, input, s) == True{} : Bool}
  for +hpop: {Gll.popIn(key, j, Check.popsOf(s)) == True{} : Bool}
  for +hr: {allHold(rs, InState{s, pr}, grammar, input) == True{} : Bool}
  {allHold(Sup.popGives(rs, grammar, key, j), InState{s, pr}, grammar, input) == True{} : Bool}

def pop_in(rs, key, j, s, pr, grammar, input, hc, hpop, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FRet{+k2, +edge}, +rest}:
      +goal = {InState{s, pr} : Goal}
      +hrt = {Check.retIn(k2, edge, Check.returnsOf(s)) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      hold_join(mine, Sup.popGives(rest, grammar, key, j), goal, grammar, input,
        if_in(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), goal, grammar, input,
          eb => joined_in(key, edge, j, s, pr, grammar, input, hc,
            {(%Equal.sym(Gll.CKey, key, k2, G.key_eq_sound(key, k2, eb)) : {Check.retIn(_, edge, Check.returnsOf(s)) == True{} : Bool}
              Lemma.and_true_left(hrt, allHold(rest, goal, grammar, input), hr)) : {Check.retIn(key, edge, Check.returnsOf(s)) == True{} : Bool}}, hpop)),
        pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(hrt, allHold(rest, goal, grammar, input), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Check.seenIn(d, s), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Gll.keyIn(c, Check.clustersOf(s)), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FPop{+k2, +j2}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Gll.popIn(k2, j2, Check.popsOf(s)), allHold(rest, InState{s, pr}, grammar, input), hr))
    case Con{Sup.FStep{+y}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Check.stepIn(y, s), allHold(rest, InState{s, pr}, grammar, input), hr))

def rule_in(f: Sup.Fact, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +reached: +List<Sup.Fact>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hf: {Sup.inState(f, s) == True{} : Bool},
  +hr: {allHold(reached, InState{s, pr}, grammar, input) == True{} : Bool})
  -> {allHold(Sup.factGives(f, pr, grammar, input, reached), InState{s, pr}, grammar, input) == True{} : Bool}:
  match f:
    case Sup.FDesc{+d}:
      desc_in(d, s, pr, grammar, input, hc, hf)
    case Sup.FCluster{Gll.CKey{+x, +i}}:
      seeds_in(grammar, pr, Core.tokAt(input, i), x, 0n, i, s, grammar, input,
        G.cluster_seeds(Check.clustersOf(s), x, i, Gll.NoPred{}, grammar, input, s, G.closed_clusters(Gll.NoPred{}, grammar, input, s, hc), hf))
    case Sup.FRet{+key, +edge}:
      ret_in(reached, key, edge, s, pr, grammar, input, hc, hf, hr)
    case Sup.FPop{+key, +j}:
      pop_in(reached, key, j, s, pr, grammar, input, hc, hf, hr)
    case Sup.FStep{+y}:
      {==}

# ======== THE INDUCTION ========

law rule_ok:
  for goal: Goal
  for +f: Sup.Fact
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hf: {holdsF(goal, f, grammar, input) == True{} : Bool}
  for +hr: {allHold(reached, goal, grammar, input) == True{} : Bool}
  {allHold(Sup.factGives(f, predOf(goal), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def rule_ok(goal, f, grammar, start, input, reached, ok, hf, hr):
  match goal:
    case InState{+s, +pr}:
      rule_in(f, s, pr, grammar, input, reached, Lemma.and_true_left(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), ok), hf, hr)

law give_all:
  for fs: +List<Sup.Fact>
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hfs: {allHold(fs, goal, grammar, input) == True{} : Bool}
  for +hr: {allHold(reached, goal, grammar, input) == True{} : Bool}
  {allHold(Sup.allGive(fs, predOf(goal), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def give_all(fs, goal, grammar, start, input, reached, ok, hfs, hr):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      +hf = {holdsF(goal, f, grammar, input) : Bool}
      hold_join(Sup.factGives(f, predOf(goal), grammar, input, reached), Sup.allGive(rest, predOf(goal), grammar, input, reached), goal, grammar, input,
        rule_ok(goal, f, grammar, start, input, reached, ok, Lemma.and_true_left(hf, allHold(rest, goal, grammar, input), hfs), hr),
        give_all(rest, goal, grammar, start, input, reached, ok, Lemma.and_true_right_side(hf, allHold(rest, goal, grammar, input), hfs), hr))

# Every reached fact holds the goal.
law grow_hold:
  for n: Nat
  for +goal: Goal
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +reached: +List<Sup.Fact>
  for +ok: {goalOk(goal, grammar, start, input) == True{} : Bool}
  for +hr: {allHold(reached, goal, grammar, input) == True{} : Bool}
  {allHold(Sup.growReached(n, predOf(goal), grammar, input, reached), goal, grammar, input) == True{} : Bool}

def grow_hold(n, goal, grammar, start, input, reached, ok, hr):
  match n:
    case 0n:
      hr
    case 1n+(+p):
      +next = Sup.addNew(Sup.allGive(reached, predOf(goal), grammar, input, reached), reached)
      grow_hold(p, goal, grammar, start, input, next, ok,
        hold_add(Sup.allGive(reached, predOf(goal), grammar, input, reached), reached, goal, grammar, input, give_all(reached, goal, grammar, start, input, reached, ok, hr, hr), hr))

# ======== PREDICTION SAVES WORK ========

law hold_within:
  for fs: +List<Sup.Fact>
  for +s: Gll.GState
  for +pr: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {allHold(fs, InState{s, pr}, grammar, input) == True{} : Bool}
  {Sup.factsWithin(fs, s) == True{} : Bool}

def hold_within(fs, s, pr, grammar, input, h):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      Lemma.and_true_intro(Sup.inState(f, s), Sup.factsWithin(rest, s), Lemma.and_true_left(Sup.inState(f, s), allHold(rest, InState{s, pr}, grammar, input), h),
        hold_within(rest, s, pr, grammar, input, Lemma.and_true_right_side(Sup.inState(f, s), allHold(rest, InState{s, pr}, grammar, input), h)))

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
  +pr: Gll.Pred) -> {goalOk(InState{plain, pr}, grammar, start, input) == True{} : Bool}:
  match b:
    case True{}:
      +sp = Equal.cong(Maybe<&2, Gll.GState>, Gll.GState, v => stateOr(v, s), Some{s}, Some{plain}, e)
      %sp : {goalOk(InState{_, pr}, grammar, start, input) == True{} : Bool}
      Equal.sym(Bool, True{}, Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), eb)
    case False{}:
      Empty.absurd({goalOk(InState{plain, pr}, grammar, start, input) == True{} : Bool}, none_state(plain, e))

def plain_run(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +plain: Gll.GState, +pr: Gll.Pred,
  +e: {Sup.closedPick(r, grammar, start, input) == Some{plain} : Maybe<&2, Gll.GState>}) -> {goalOk(InState{plain, pr}, grammar, start, input) == True{} : Bool}:
  match r:
    case Gll.GDone{+s}:
      plain_pick(Bool.and(Check.closed(grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), grammar, start, input, s, plain, {==}, e, pr)
    case Gll.OutOfFuel{+s}:
      Empty.absurd({goalOk(InState{plain, pr}, grammar, start, input) == True{} : Bool}, none_state(plain, e))

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
  +goal = {InState{plain, pr} : Goal}
  +ok = plain_run(Gll.parse(fuelPlain, grammar, start, input), grammar, start, input, plain, pr, gotPlain)
  +sup = other_run(Gll.parseWith(fo, pr, grammar, start, input), fo, pr, grammar, start, input, other, gotOther)
  +root = Lemma.and_true_right_side(Check.closed(grammar, input, plain), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(plain)), ok)
  +hr0 = Lemma.and_true_intro(Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(plain)), True{}, root, {==})
  +reached = Sup.growReached(fo, pr, grammar, input, Sup.roots(start))
  +hr = grow_hold(fo, goal, grammar, start, input, Sup.roots(start), ok, hr0)
  hold_within(Sup.factsOf(other), plain, pr, grammar, input, in_reached(Sup.factsOf(other), reached, goal, grammar, input, sup, hr))
