import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./SUPPORT.bend as Sup
import ./PROOF_GLL.bend as G
import ./PROOF_HOLD.bend as H

# THE RULES KEEP A CLOSED PLAIN STATE: every fact a rule gives from facts of a closed state of
# the plain engine is in that state (whatever the predictor of the run the rules follow).

# ======== THE RULES KEEP: A CLOSED PLAIN STATE ========

def token_in(b: Bool, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +h: {Check.tokenOk(b, q, d, k, i, s) == True{} : Bool}) -> {H.allHold(Sup.tokenGives(b, q, d, k, i), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+d, k, 1n+i}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+d, k, i, 1n+i}, s) : Bool}
      Lemma.and_true_intro(sd, Bool.and(sy, True{}), Lemma.and_true_left(sd, sy, h), Lemma.and_true_intro(sy, True{}, Lemma.and_true_right_side(sd, sy, h), {==}))
    case False{}:
      {==}

def empty_in(d: Nat, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +k: Nat, +i: Nat,
  +h: {Check.emptyOk(d, q, k, i, s) == True{} : Bool}) -> {H.allHold(Sup.emptyGives(d, q, k, i), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match d:
    case 0n:
      Lemma.and_true_intro(Check.stepIn(Core.Bsr{q, 0n, k, i, i}, s), True{}, h, {==})
    case 1n+(+e):
      {==}

def item_in(item: Maybe<&2, Core.Sym>, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +h: {Check.itemOk(item, grammar, input, q, d, k, i, s) == True{} : Bool}) -> {H.allHold(Sup.itemGives(item, grammar, input, q, d, k, i), H.InState{s, pr}, grammar, input) == True{} : Bool}:
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
      Lemma.and_true_intro(po, H.allHold(Sup.emptyGives(d, q, k, i), H.InState{s, pr}, grammar, input), Lemma.and_true_right_side(em, po, h),
        empty_in(d, s, pr, grammar, input, q, k, i, Lemma.and_true_left(em, po, h)))

def desc_in(d: Gll.Desc, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hf: {Check.seenIn(d, s) == True{} : Bool}) -> {H.allHold(Sup.descGives(d, grammar, input), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      item_in(Gll.nthSym(Core.rhsOf(grammar, q), dot), s, pr, grammar, input, q, dot, k, i,
        G.desc_ok(Check.seenOf(s), Gll.Desc{q, dot, k, i}, grammar, input, s, G.closed_descs(Gll.NoPred{}, grammar, input, s, hc), hf))

def seed_pick(a: Bool, b: Bool, +d: Gll.Desc, +plainRest: +List<Gll.Desc>, +predRest: +List<Gll.Desc>, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +h: {Check.allSeen(Gll.keepDesc(b, d, plainRest), s) == True{} : Bool},
  later: {Check.allSeen(plainRest, s) == True{} : Bool} -> {H.allHold(Sup.descFacts(predRest), H.InState{s, pr}, grammar, input) == True{} : Bool})
  -> {H.allHold(Sup.descFacts(Gll.keepDesc(Bool.and(a, b), d, predRest)), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match a b:
    case True{} True{}:
      Lemma.and_true_intro(Check.seenIn(d, s), H.allHold(Sup.descFacts(predRest), H.InState{s, pr}, grammar, input),
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
  {H.allHold(Sup.descFacts(Gll.productionsOf(g, pr, tok, x, base, i)), H.InState{s, pr}, grammar, input) == True{} : Bool}

def seeds_in(g, pr, tok, x, base, i, s, grammar, input, h):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      seed_pick(Gll.admits(pr, base, tok), Nat.is_eq(lhs, x), Gll.Desc{base, 0n, i, i}, Gll.productionsOf(rest, Gll.NoPred{}, tok, x, 1n+base, i), Gll.productionsOf(rest, pr, tok, x, 1n+base, i), s, pr, grammar, input, h,
        h2 => seeds_in(rest, pr, tok, x, 1n+base, i, s, grammar, input, h2))

def resume_pick(b: Bool, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat,
  +h: {Check.resumeOk(b, q, dot, k, kc, j, s) == True{} : Bool}) -> {H.allHold(Sup.resumeOk(b, q, dot, k, kc, j), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, s) : Bool}
      Lemma.and_true_intro(sd, Bool.and(sy, True{}), Lemma.and_true_left(sd, sy, h), Lemma.and_true_intro(sy, True{}, Lemma.and_true_right_side(sd, sy, h), {==}))
    case False{}:
      {==}

def resume_in(edge: Gll.Edge, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +kc: Nat, +j: Nat,
  +h: {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}) -> {H.allHold(Sup.resumeGives(edge, grammar, kc, j), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match edge:
    case Gll.Edge{+q, +dot, +k}:
      resume_pick(Gll.needHolds(Gll.needAt(grammar, q, dot), kc, j), s, pr, grammar, input, q, dot, k, kc, j, h)

# A return edge and a pop of its cluster, both in the closed state: the resumed facts are too.
def joined_in(key: Gll.CKey, +edge: Gll.Edge, +j: Nat, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hret: {Check.retIn(key, edge, Check.returnsOf(s)) == True{} : Bool},
  +hpop: {Gll.popIn(key, j, Check.popsOf(s)) == True{} : Bool}) -> {H.allHold(Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), H.InState{s, pr}, grammar, input) == True{} : Bool}:
  match key:
    case Gll.CKey{+x, +kc}:
      +ep = G.ret_ok(Check.returnsOf(s), Gll.CKey{x, kc}, edge, grammar, Check.popsOf(s), s, G.closed_returns(Gll.NoPred{}, grammar, input, s, hc), hret)
      resume_in(edge, s, pr, grammar, input, kc, j, G.pop_ok(Check.popsOf(s), x, kc, edge, j, grammar, s, ep, hpop))

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
  for +hr: {H.allHold(rs, H.InState{s, pr}, grammar, input) == True{} : Bool}
  {H.allHold(Sup.retGives(rs, grammar, key, edge), H.InState{s, pr}, grammar, input) == True{} : Bool}

def ret_in(rs, key, edge, s, pr, grammar, input, hc, hret, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FPop{+k2, +j}, +rest}:
      +goal = {H.InState{s, pr} : H.Goal}
      +hp = {Gll.popIn(k2, j, Check.popsOf(s)) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      H.hold_join(mine, Sup.retGives(rest, grammar, key, edge), goal, grammar, input,
        H.if_in(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), goal, grammar, input,
          eb => joined_in(key, edge, j, s, pr, grammar, input, hc, hret,
            {(%Equal.sym(Gll.CKey, key, k2, G.key_eq_sound(key, k2, eb)) : {Gll.popIn(_, j, Check.popsOf(s)) == True{} : Bool}
              Lemma.and_true_left(hp, H.allHold(rest, goal, grammar, input), hr)) : {Gll.popIn(key, j, Check.popsOf(s)) == True{} : Bool}})),
        ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(hp, H.allHold(rest, goal, grammar, input), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.seenIn(d, s), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Gll.keyIn(c, Check.clustersOf(s)), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FRet{+k2, +e2}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.retIn(k2, e2, Check.returnsOf(s)), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FStep{+y}, +rest}:
      ret_in(rest, key, edge, s, pr, grammar, input, hc, hret, Lemma.and_true_right_side(Check.stepIn(y, s), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))

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
  for +hr: {H.allHold(rs, H.InState{s, pr}, grammar, input) == True{} : Bool}
  {H.allHold(Sup.popGives(rs, grammar, key, j), H.InState{s, pr}, grammar, input) == True{} : Bool}

def pop_in(rs, key, j, s, pr, grammar, input, hc, hpop, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FRet{+k2, +edge}, +rest}:
      +goal = {H.InState{s, pr} : H.Goal}
      +hrt = {Check.retIn(k2, edge, Check.returnsOf(s)) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      H.hold_join(mine, Sup.popGives(rest, grammar, key, j), goal, grammar, input,
        H.if_in(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), goal, grammar, input,
          eb => joined_in(key, edge, j, s, pr, grammar, input, hc,
            {(%Equal.sym(Gll.CKey, key, k2, G.key_eq_sound(key, k2, eb)) : {Check.retIn(_, edge, Check.returnsOf(s)) == True{} : Bool}
              Lemma.and_true_left(hrt, H.allHold(rest, goal, grammar, input), hr)) : {Check.retIn(key, edge, Check.returnsOf(s)) == True{} : Bool}}, hpop)),
        pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(hrt, H.allHold(rest, goal, grammar, input), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Check.seenIn(d, s), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Gll.keyIn(c, Check.clustersOf(s)), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FPop{+k2, +j2}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Gll.popIn(k2, j2, Check.popsOf(s)), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))
    case Con{Sup.FStep{+y}, +rest}:
      pop_in(rest, key, j, s, pr, grammar, input, hc, hpop, Lemma.and_true_right_side(Check.stepIn(y, s), H.allHold(rest, H.InState{s, pr}, grammar, input), hr))

def rule_in(f: Sup.Fact, +s: Gll.GState, +pr: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +reached: +List<Sup.Fact>,
  +hc: {Check.closed(grammar, input, s) == True{} : Bool},
  +hf: {Sup.inState(f, s) == True{} : Bool},
  +hr: {H.allHold(reached, H.InState{s, pr}, grammar, input) == True{} : Bool})
  -> {H.allHold(Sup.factGives(f, pr, grammar, input, reached), H.InState{s, pr}, grammar, input) == True{} : Bool}:
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

