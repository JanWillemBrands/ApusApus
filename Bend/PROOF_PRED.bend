import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./FIRST.bend as First
import ./LEMMAS.bend as Lemma
import ./PROOF_SETS.bend as Sets
import ./PROOF_TABLES.bend as Tab
import ./PROOF_ADMIT.bend as Adm

# PREDICTION IN THE WALK, FOR BOTH MODES. Without prediction every fact here is True; with
# it, the facts say what may come after the sequence being walked, and that the tables'
# FOLLOW check covers it.

# The tables are closed (always, without prediction).
def predOk(pr: Gll.Pred, +grammar: +List<Spec.Production>, +start: Nat) -> Bool:
  match pr:
    case Gll.NoPred{}:
      True{}
    case Gll.Predict{+t}:
      First.tablesClosed(grammar, start, t)

# What comes at fin, where the sequence at (index, rpath) ends, may come after it.
def ctxOk(pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +fin: Nat) -> Bool:
  match pr:
    case Gll.NoPred{}:
      True{}
    case Gll.Predict{+t}:
      Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath))

def afterPick(+t: Gll.Tables, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, rpath: +List<Nat>, +fin: Nat) -> Bool:
  match rpath:
    case Con{+m, +outer}:
      Gll.lsHas(List.get(&2, Nat, input, fin), Gll.predictAt(grammar, t, index, outer, 1n+m))
    case Nil{}:
      True{}

# For the rounds of the loop at rpath = m <> outer: what comes at fin, where the loop ends,
# may come after the loop.
def afterOk(pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +fin: Nat) -> Bool:
  match pr:
    case Gll.NoPred{}:
      True{}
    case Gll.Predict{+t}:
      afterPick(t, grammar, input, index, rpath, fin)

# The FOLLOW check holds for the sequence at (index, rpath), with nesting fuel ff.
def foOk(pr: Gll.Pred, +ff: Nat, +grammar: +List<Spec.Production>, +index: Nat, +rpath: +List<Nat>) -> Bool:
  match pr:
    case Gll.NoPred{}:
      True{}
    case Gll.Predict{+t}:
      First.followsOk(ff, Gll.MItems{}, Gll.seqAt(grammar, index, rpath), [], grammar, t, index, rpath, 0n)

# For the rounds of the loop at rpath = m <> outer: the check for the sequence around it.
def foLoop(+pr: Gll.Pred, +ff: Nat, +grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>) -> Bool:
  match rpath:
    case Con{m, +outer}:
      foOk(pr, ff, grammar, index, outer)
    case Nil{}:
      True{}

def Spells(+forest: +List<Spec.Tree>, +input: +List<Nat>, +pos: Nat) -> Data:
  {Spec.leaves(forest) == Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(forest))) : +List<Nat>}

law prods_of:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}

def prods_of(grammar, start, t, po):
  Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po)

# ---- G1: a descriptor of a parse tree is admitted ----

law admit_any:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +fin: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +fit: {Spec.fits(forest, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +finEq: {Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ctx: {ctxOk(pr, grammar, input, index, rpath, fin) == True{} : Bool}
  for +reads: {Bool.or(Bool.not(Adm.seedReads(grammar, index, dot, rpath, k, pos)), Bool.not(List.is_empty(&2, Nat, Spec.leaves(forest)))) == True{} : Bool}
  {Gll.admits(pr, grammar, input, Gll.Desc{index, rpath, dot, k, pos}) == True{} : Bool}

def admit_any(pr, grammar, start, input, index, rpath, dot, k, forest, pos, fin, po, fit, sp, finEq, ctx, reads):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      Adm.admit_for(dot, rpath, grammar, t, prods_of(grammar, start, t, po), input, index, k, forest, pos, fin, fit, sp, finEq, ctx, reads)

law lhs_of_is:
  for +grammar: +List<Spec.Production>
  for p: Nat
  for +a: Nat
  for e: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  {Gll.lhsOf(grammar, p) == a : Nat}

def lhs_of_is(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, rhs}, rest} 0n:
      Lemma.nat_eq_sound(lhs, a, e)
    case Con{prod, +rest} 1n+q:
      lhs_of_is(rest, q, a, e)

# ---- G2: the child of a nonterminal ends where FOLLOW allows ----

law ctx_node:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +ff: Nat
  for +x: Nat
  for +q: Nat
  for +ts: +List<Spec.Tree>
  for +cpos: Nat
  for +fin: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +fo: {foOk(pr, ff, grammar, index, rpath) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spTs: Spells(ts, input, cpos)
  for +finEq: {Nat.add(cpos, List.length(&2, Nat, Spec.leaves(ts))) == fin : Nat}
  for +ctx: {ctxOk(pr, grammar, input, index, rpath, fin) == True{} : Bool}
  {ctxOk(pr, grammar, input, q, [], cpos) == True{} : Bool}

def ctx_node(pr, grammar, start, input, index, rpath, dot, ff, x, q, ts, cpos, fin, po, fo, itemEq, lhsOk, fitTs, spTs, finEq, ctx):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      +pcs = prods_of(grammar, start, t, po)
      +tok = List.get(&2, Nat, input, cpos)
      +have = Adm.admit_core(grammar, t, pcs, input, index, rpath, 1n+dot, ts, cpos, fin, fitTs, spTs, finEq, ctx)
      +sub0 = Adm.fo_item_nt(Gll.seqAt(grammar, index, rpath), dot, ff, grammar, t, index, rpath, 0n, x, fo, itemEq)
      +sub = Equal.trans(Bool, First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+dot), Gll.lsAt(Gll.folTab(t), x)), First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+Nat.add(dot, 0n)), Gll.lsAt(Gll.folTab(t), x)), True{},
        Equal.cong(Nat, Bool, v => First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+v), Gll.lsAt(Gll.folTab(t), x)), dot, Nat.add(dot, 0n), Equal.sym(Nat, Nat.add(dot, 0n), dot, Lemma.add_zero_right(dot))), sub0)
      +inFol = Sets.ls_sub_has(tok, Gll.predictAt(grammar, t, index, rpath, 1n+dot), Gll.lsAt(Gll.folTab(t), x), sub, have)
      Equal.trans(Bool, Gll.lsHas(tok, Gll.lsAt(Gll.folTab(t), Gll.lhsOf(grammar, q))), Gll.lsHas(tok, Gll.lsAt(Gll.folTab(t), x)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(tok, Gll.lsAt(Gll.folTab(t), v)), Gll.lhsOf(grammar, q), x, lhs_of_is(grammar, q, x, lhsOk)), inFol)

# ---- G3: an alternative of a bracket ends where the rest of the sequence may start ----

law ctx_pick:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +a: Nat
  for +ts: +List<Spec.Tree>
  for +cpos: Nat
  for +fin: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spTs: Spells(ts, input, cpos)
  for +finEq: {Nat.add(cpos, List.length(&2, Nat, Spec.leaves(ts))) == fin : Nat}
  for +ctx: {ctxOk(pr, grammar, input, index, rpath, fin) == True{} : Bool}
  {ctxOk(pr, grammar, input, index, a <> (dot <> rpath), cpos) == True{} : Bool}

def ctx_pick(pr, grammar, start, input, index, rpath, dot, a, ts, cpos, fin, po, fitTs, spTs, finEq, ctx):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      +have = Adm.admit_core(grammar, t, prods_of(grammar, start, t, po), input, index, rpath, 1n+dot, ts, cpos, fin, fitTs, spTs, finEq, ctx)
      Sets.ls_has_union_right(List.get(&2, Nat, input, cpos), Gll.loopFirst(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), t), Gll.predictAt(grammar, t, index, rpath, 1n+dot), have)

# ---- G4: the rounds of a loop end where the rest of the sequence may start ----

law after_loop:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +ts: +List<Spec.Tree>
  for +cpos: Nat
  for +fin: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spTs: Spells(ts, input, cpos)
  for +finEq: {Nat.add(cpos, List.length(&2, Nat, Spec.leaves(ts))) == fin : Nat}
  for +ctx: {ctxOk(pr, grammar, input, index, rpath, fin) == True{} : Bool}
  {afterOk(pr, grammar, input, index, dot <> rpath, cpos) == True{} : Bool}

def after_loop(pr, grammar, start, input, index, rpath, dot, ts, cpos, fin, po, fitTs, spTs, finEq, ctx):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      Adm.admit_core(grammar, t, prods_of(grammar, start, t, po), input, index, rpath, 1n+dot, ts, cpos, fin, fitTs, spTs, finEq, ctx)

# ---- G5: a round of a loop ends where another round or the rest after the loop may start ----

# The bracket item of a loop path: the item m of the sequence outside it.
def loopAt(+grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>) -> Maybe<&2, Spec.Item>:
  match rpath:
    case Con{+m, +outer}:
      Gll.nthItem(Gll.seqAt(grammar, index, outer), m)
    case Nil{}:
      None{}

law loop_repeat:
  for kind: Spec.Bracket
  for e: {Gll.isLoop(kind) == True{} : Bool}
  {Gll.isRepeat(kind) == True{} : Bool}

def loop_repeat(kind, e):
  match kind:
    case Spec.Group{}:
      e
    case Spec.Optional{}:
      e
    case Spec.Closure{}:
      {==}
    case Spec.Positive{}:
      {==}

law round_split:
  for lv: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pcs: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rr: +List<Spec.Tree>
  for +e: Nat
  for +fin: Nat
  for +lvEq: {Spec.leaves(rr) == lv : +List<Nat>}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isRep: {Gll.isRepeat(kind) == True{} : Bool}
  for +after: {Gll.lsHas(List.get(&2, Nat, input, fin), Gll.predictAt(grammar, t, index, outer, 1n+m)) == True{} : Bool}
  for +fitRr: {Spec.fits(rr, grammar, Spec.times(List.length(&2, Spec.Tree, rr), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spRr: Spells(rr, input, e)
  for +finEq: {Nat.add(e, List.length(&2, Nat, Spec.leaves(rr))) == fin : Nat}
  {Gll.lsHas(List.get(&2, Nat, input, e), Gll.lsUnion(Gll.loopFirst(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), t), Gll.predictAt(grammar, t, index, outer, 1n+m))) == True{} : Bool}

def round_split(lv, grammar, t, pcs, input, index, m, outer, kind, alts, rr, e, fin, lvEq, itemEq, isRep, after, fitRr, spRr, finEq):
  match lv:
    case Nil{}:
      +lf = Gll.loopFirst(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), t)
      +pa = Gll.predictAt(grammar, t, index, outer, 1n+m)
      +len0 = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(rr), [], lvEq)
      +eFin = Equal.trans(Nat, e, Nat.add(e, List.length(&2, Nat, Spec.leaves(rr))), fin,
        Equal.trans(Nat, e, Nat.add(e, 0n), Nat.add(e, List.length(&2, Nat, Spec.leaves(rr))), Equal.sym(Nat, Nat.add(e, 0n), e, Lemma.add_zero_right(e)), Equal.cong(Nat, Nat, v => Nat.add(e, v), 0n, List.length(&2, Nat, Spec.leaves(rr)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(rr)), 0n, len0))),
        finEq)
      +atE = Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, e), pa), Gll.lsHas(List.get(&2, Nat, input, fin), pa), True{}, Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), pa), e, fin, eFin), after)
      Sets.ls_has_union_right(List.get(&2, Nat, input, e), lf, pa, atE)
    case Con{+k0, +w}:
      +lf = Gll.loopFirst(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), t)
      +pa = Gll.predictAt(grammar, t, index, outer, 1n+m)
      +spK = Equal.trans(+List<Nat>, k0 <> w, Spec.leaves(rr), Lemma.slice(input, e, List.length(&2, Nat, k0 <> w)), Equal.sym(+List<Nat>, Spec.leaves(rr), k0 <> w, lvEq),
        Equal.trans(+List<Nat>, Spec.leaves(rr), Lemma.slice(input, e, List.length(&2, Nat, Spec.leaves(rr))), Lemma.slice(input, e, List.length(&2, Nat, k0 <> w)), spRr,
          Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.slice(input, e, List.length(&2, Nat, v)), Spec.leaves(rr), k0 <> w, lvEq)))
      +getK = Adm.leaf_token(input, e, k0, w, spK)
      +inAlts = Tab.times_first(List.length(&2, Spec.Tree, rr), Gll.nestFuel(), alts, t, Some{k0}, Tab.first_sound(rr, 1n+Gll.nestFuel(), Spec.times(List.length(&2, Spec.Tree, rr), Spec.Brack{Spec.Group{}, alts}), grammar, t, pcs, fitRr, k0, w, lvEq))
      +inLoop = Sets.ls_has_if(Gll.isRepeat(kind), Some{k0}, Gll.firstOf(Gll.infoAlts(alts, t)), isRep, inAlts)
      +inLf = Equal.trans(Bool, Gll.lsHas(Some{k0}, lf), Gll.lsHas(Some{k0}, Gll.loopFirst(Some{Spec.Brack{kind, alts}}, t)), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(Some{k0}, Gll.loopFirst(v, t)), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq), inLoop)
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, e), Gll.lsUnion(lf, pa)), Gll.lsHas(Some{k0}, Gll.lsUnion(lf, pa)), True{},
        Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.lsUnion(lf, pa)), List.get(&2, Nat, input, e), Some{k0}, getK),
        Sets.ls_has_union_left(Some{k0}, lf, pa, inLf))

law ctx_round:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +index: Nat
  for rpath: +List<Nat>
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rr: +List<Spec.Tree>
  for +e: Nat
  for +fin: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +loopEq: {loopAt(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  for +after: {afterOk(pr, grammar, input, index, rpath, fin) == True{} : Bool}
  for +fitRr: {Spec.fits(rr, grammar, Spec.times(List.length(&2, Spec.Tree, rr), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spRr: Spells(rr, input, e)
  for +finEq: {Nat.add(e, List.length(&2, Nat, Spec.leaves(rr))) == fin : Nat}
  {ctxOk(pr, grammar, input, index, a <> rpath, e) == True{} : Bool}

def ctx_round(pr, grammar, start, input, index, rpath, a, kind, alts, rr, e, fin, po, loopEq, isL, after, fitRr, spRr, finEq):
  match pr rpath:
    case Gll.NoPred{} _:
      {==}
    case Gll.Predict{+t} Nil{}:
      Empty.absurd({Gll.lsHas(List.get(&2, Nat, input, e), Gll.contextAfter(grammar, t, index, [a])) == True{} : Bool}, Adm.none_not_some(Spec.Brack{kind, alts}, loopEq))
    case Gll.Predict{+t} Con{+m, +outer}:
      round_split(Spec.leaves(rr), grammar, t, prods_of(grammar, start, t, po), input, index, m, outer, kind, alts, rr, e, fin, {==}, loopEq, loop_repeat(kind, isL), after, fitRr, spRr, finEq)

# ---- G6-G8: the FOLLOW check, carried into a production's sequence and into brackets ----

law fo_node:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +q: Nat
  for +x: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {foOk(pr, Gll.nestFuel(), grammar, q, []) == True{} : Bool}

def fo_node(pr, grammar, start, q, x, po, lhsOk):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      +rhs = Spec.rhsOf(grammar, q)
      +info = Gll.infoItems(rhs, t)
      +all = Tab.prod_at(grammar, q, x, t, prods_of(grammar, start, t, po), lhsOk)
      +rest = Lemma.and_true_right_side(Bool.or(Bool.not(Gll.nulOf(info)), Gll.boolAt(Gll.nulTab(t), x)), Bool.and(First.lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x)), First.followsOk(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, q, [], 0n)), all)
      Lemma.and_true_right_side(First.lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x)), First.followsOk(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, q, [], 0n), rest)

law fo_pick:
  for +pr: Gll.Pred
  for +ff: Nat
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +fo: {foOk(pr, ff, grammar, index, rpath) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  {foOk(pr, Adm.pred2(ff), grammar, index, a <> (dot <> rpath)) == True{} : Bool}

def fo_pick(pr, ff, grammar, index, rpath, dot, kind, alts, a, fo, itemEq, isA):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      +p2 = Adm.pred2(ff)
      +path = {a <> (dot <> rpath) : +List<Nat>}
      +r0 = Adm.fo_item_br(Gll.seqAt(grammar, index, rpath), dot, ff, grammar, t, index, rpath, 0n, kind, alts, a, fo, itemEq, isA)
      +r1 = Equal.trans(Bool, First.followsOk(p2, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, path, 0n), First.followsOk(p2, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (Nat.add(dot, 0n) <> rpath), 0n), True{},
        Equal.cong(Nat, Bool, v => First.followsOk(p2, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (v <> rpath), 0n), dot, Nat.add(dot, 0n), Equal.sym(Nat, Nat.add(dot, 0n), dot, Lemma.add_zero_right(dot))), r0)
      Equal.trans(Bool, First.followsOk(p2, Gll.MItems{}, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), [], grammar, t, index, path, 0n), First.followsOk(p2, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, path, 0n), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => First.followsOk(p2, Gll.MItems{}, Gll.bracketAlt(v, a), [], grammar, t, index, path, 0n), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{kind, alts}}, itemEq), r1)

# A round of the loop at rpath = m <> outer, with alternative a.
law fo_round:
  for +pr: Gll.Pred
  for +ff: Nat
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for rpath: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +fo: {foLoop(pr, ff, grammar, index, rpath) == True{} : Bool}
  for +loopEq: {loopAt(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  {foOk(pr, Adm.pred2(ff), grammar, index, a <> rpath) == True{} : Bool}

def fo_round(pr, ff, grammar, index, rpath, kind, alts, a, fo, loopEq, isA):
  match rpath:
    case Nil{}:
      Empty.absurd({foOk(pr, Adm.pred2(ff), grammar, index, [a]) == True{} : Bool}, Adm.none_not_some(Spec.Brack{kind, alts}, loopEq))
    case Con{+m, +outer}:
      fo_pick(pr, ff, grammar, index, outer, m, kind, alts, a, fo, loopEq, isA)

# ---- G9: the end of the input may follow the start symbol ----

law get_end:
  for input: +List<Nat>
  {List.get(&2, Nat, input, List.length(&2, Nat, input)) == None{} : Maybe<&2, Nat>}

def get_end(input):
  match input:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      get_end(rest)

law root_ctx:
  for +pr: Gll.Pred
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +q: Nat
  for +po: {predOk(pr, grammar, start) == True{} : Bool}
  for +lhsOk: {Spec.lhsIs(grammar, q, start) == True{} : Bool}
  {ctxOk(pr, grammar, input, q, [], List.length(&2, Nat, input)) == True{} : Bool}

def root_ctx(pr, grammar, start, input, q, po, lhsOk):
  match pr:
    case Gll.NoPred{}:
      {==}
    case Gll.Predict{+t}:
      +endOk = Lemma.and_true_right_side(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po)
      +lhsEq = lhs_of_is(grammar, q, start, lhsOk)
      +s1 = Equal.trans(Bool, Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), Gll.lhsOf(grammar, q))), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), v)), Gll.lhsOf(grammar, q), start, lhsEq), endOk)
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, List.length(&2, Nat, input)), Gll.lsAt(Gll.folTab(t), Gll.lhsOf(grammar, q))), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), Gll.lhsOf(grammar, q))), True{},
        Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.lsAt(Gll.folTab(t), Gll.lhsOf(grammar, q))), List.get(&2, Nat, input, List.length(&2, Nat, input)), None{}, get_end(input)), s1)
