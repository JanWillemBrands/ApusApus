import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C

# THE ENGINE'S STEPS REST ON EARLIER STEPS (RUN.bend, `groundOk`): every operation of the
# engine keeps it, one operation at a time. A new step's prefix is completed by an older
# step, and its item is a token or a completed production of the nonterminal; a new
# descriptor's prefix by a step; a new return edge by its caller's prefix; a new pop by the
# step that completed the production. This is what makes the steps real (PROOF_FOUND.bend).

# ======== MORE STEPS KEEP WHAT IS DONE ========

law done_of_member:
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +x: Core.Bsr
  for ys: +List<Core.Bsr>
  for +m: {Core.member(x, ys) == True{} : Bool}
  for +db: {Run.doneBy(q, ks, d, e, x) == True{} : Bool}
  {Run.segDone(q, ks, d, e, ys) == True{} : Bool}

def done_head(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +x: Core.Bsr, +y: Core.Bsr, +eq: {x == y : Core.Bsr},
  +db: {Run.doneBy(q, ks, d, e, x) == True{} : Bool}) -> {Run.doneBy(q, ks, d, e, y) == True{} : Bool}:
  %eq : {Run.doneBy(q, ks, d, e, _) == True{} : Bool}
  db

def done_pick(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +db: {Run.doneBy(q, ks, d, e, x) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Run.segDone(q, ks, d, e, rest) == True{} : Bool}) -> {Run.segDone(q, ks, d, e, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{b}:
      Lemma.or_true_left_intro(Run.doneBy(q, ks, d, e, y), Run.segDone(q, ks, d, e, rest), done_head(q, ks, d, e, x, y, G.bsr_eq_sound(x, y, b), db))
    case Inr{m}:
      Lemma.or_true_right_intro(Run.doneBy(q, ks, d, e, y), Run.segDone(q, ks, d, e, rest), later(m))

def done_of_member(q, ks, d, e, x, ys, m, db):
  match ys:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      done_pick(q, ks, d, e, x, y, rest, db, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m), m2 => done_of_member(q, ks, d, e, x, rest, m2, db))

def seg_pick(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +s: Core.Bsr, +rest: +List<Core.Bsr>, +ys2: +List<Core.Bsr>,
  +ms: {Core.member(s, ys2) == True{} : Bool},
  cases: Either<{Run.doneBy(q, ks, d, e, s) == True{} : Bool}, {Run.segDone(q, ks, d, e, rest) == True{} : Bool}>,
  later: {Run.segDone(q, ks, d, e, rest) == True{} : Bool} -> {Run.segDone(q, ks, d, e, ys2) == True{} : Bool}) -> {Run.segDone(q, ks, d, e, ys2) == True{} : Bool}:
  match cases:
    case Inl{db}:
      done_of_member(q, ks, d, e, s, ys2, ms, db)
    case Inr{h}:
      later(h)

law seg_mono:
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for ys1: +List<Core.Bsr>
  for +ys2: +List<Core.Bsr>
  for +sub: {Core.allIn(ys1, ys2) == True{} : Bool}
  for +h: {Run.segDone(q, ks, d, e, ys1) == True{} : Bool}
  {Run.segDone(q, ks, d, e, ys2) == True{} : Bool}

def seg_mono(q, ks, d, e, ys1, ys2, sub, h):
  match ys1:
    case Nil{}:
      Empty.absurd({Run.segDone(q, ks, d, e, ys2) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+s, +rest}:
      seg_pick(q, ks, d, e, s, rest, ys2, Lemma.and_true_left(Core.member(s, ys2), Core.allIn(rest, ys2), sub),
        Lemma.or_true_cases(Run.doneBy(q, ks, d, e, s), Run.segDone(q, ks, d, e, rest), h),
        m => seg_mono(q, ks, d, e, rest, ys2, Lemma.and_true_right_side(Core.member(s, ys2), Core.allIn(rest, ys2), sub), m))

def prod_pick(+lhs: Nat, +x: Nat, +base: Nat, +k: Nat, +j: Nat, +len: Nat, +R: Bool, +R2: Bool, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  cases: Either<{Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys1)) == True{} : Bool}, {R == True{} : Bool}>,
  later: {R == True{} : Bool} -> {R2 == True{} : Bool}) -> {Bool.or(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys2)), R2) == True{} : Bool}:
  match cases:
    case Inl{+a}:
      Lemma.or_true_left_intro(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys2)), R2,
        Lemma.and_true_intro(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys2), Lemma.and_true_left(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys1), a),
          seg_mono(base, k, len, j, ys1, ys2, sub, Lemma.and_true_right_side(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys1), a))))
    case Inr{h}:
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys2)), R2, later(h))

law prod_mono:
  for g: +List<Core.Production>
  for +base: Nat
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +ys1: +List<Core.Bsr>
  for +ys2: +List<Core.Bsr>
  for +sub: {Core.allIn(ys1, ys2) == True{} : Bool}
  for +h: {Run.prodDone(g, base, x, k, j, ys1) == True{} : Bool}
  {Run.prodDone(g, base, x, k, j, ys2) == True{} : Bool}

def prod_mono(g, base, x, k, j, ys1, ys2, sub, h):
  match g:
    case Nil{}:
      h
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +len = List.length(&2, Core.Sym, rhs)
      prod_pick(lhs, x, base, k, j, len, Run.prodDone(rest, 1n+base, x, k, j, ys1), Run.prodDone(rest, 1n+base, x, k, j, ys2), ys1, ys2, sub,
        Lemma.or_true_cases(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys1)), Run.prodDone(rest, 1n+base, x, k, j, ys1), h),
        m => prod_mono(rest, 1n+base, x, k, j, ys1, ys2, sub, m))

def prefix_mono(+q: Nat, +ks: Nat, d: Nat, +k: Nat, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  +h: {Run.prefixDone(q, ks, d, k, ys1) == True{} : Bool}) -> {Run.prefixDone(q, ks, d, k, ys2) == True{} : Bool}:
  match d:
    case 0n:
      h
    case 1n+(+m):
      seg_mono(q, ks, 1n+m, k, ys1, ys2, sub, h)

def desc_mono(d: Gll.Desc, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  +h: {Run.descGround(d, ys1) == True{} : Bool}) -> {Run.descGround(d, ys2) == True{} : Bool}:
  match d:
    case Gll.Desc{+q, +dd, +k, +i}:
      prefix_mono(q, k, dd, i, ys1, ys2, sub, h)

def edge_mono(e: Gll.Edge, +x: Nat, +kc: Nat, +grammar: +List<Core.Production>, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  +h: {Run.edgeGround(e, x, kc, grammar, ys1) == True{} : Bool}) -> {Run.edgeGround(e, x, kc, grammar, ys2) == True{} : Bool}:
  match e:
    case Gll.Edge{+q, +d, +k}:
      +it = {Run.itemIsNT(Gll.nthSym(Core.rhsOf(grammar, q), d), x) : Bool}
      Lemma.and_true_intro(Run.prefixDone(q, k, d, kc, ys2), it, prefix_mono(q, k, d, kc, ys1, ys2, sub, Lemma.and_true_left(Run.prefixDone(q, k, d, kc, ys1), it, h)),
        Lemma.and_true_right_side(Run.prefixDone(q, k, d, kc, ys1), it, h))

def ret_mono(r: Gll.Ret, +grammar: +List<Core.Production>, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  +h: {Run.retGround(r, grammar, ys1) == True{} : Bool}) -> {Run.retGround(r, grammar, ys2) == True{} : Bool}:
  match r:
    case Gll.Ret{Gll.CKey{+x, +kc}, +e}:
      edge_mono(e, x, kc, grammar, ys1, ys2, sub, h)

def pop_mono(p: Gll.Pop, +grammar: +List<Core.Production>, +ys1: +List<Core.Bsr>, +ys2: +List<Core.Bsr>, +sub: {Core.allIn(ys1, ys2) == True{} : Bool},
  +h: {Run.popGround(p, grammar, ys1) == True{} : Bool}) -> {Run.popGround(p, grammar, ys2) == True{} : Bool}:
  match p:
    case Gll.Pop{Gll.CKey{+x, +kc}, +j}:
      prod_mono(grammar, 0n, x, kc, j, ys1, ys2, sub, h)

law descs_mono:
  for ds: +List<Gll.Desc>
  for +ys1: +List<Core.Bsr>
  for +ys2: +List<Core.Bsr>
  for +sub: {Core.allIn(ys1, ys2) == True{} : Bool}
  for +h: {Run.descsGrounded(ds, ys1) == True{} : Bool}
  {Run.descsGrounded(ds, ys2) == True{} : Bool}

def descs_mono(ds, ys1, ys2, sub, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      Lemma.and_true_intro(Run.descGround(d, ys2), Run.descsGrounded(rest, ys2), desc_mono(d, ys1, ys2, sub, Lemma.and_true_left(Run.descGround(d, ys1), Run.descsGrounded(rest, ys1), h)),
        descs_mono(rest, ys1, ys2, sub, Lemma.and_true_right_side(Run.descGround(d, ys1), Run.descsGrounded(rest, ys1), h)))

law rets_mono:
  for rs: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +ys1: +List<Core.Bsr>
  for +ys2: +List<Core.Bsr>
  for +sub: {Core.allIn(ys1, ys2) == True{} : Bool}
  for +h: {Run.retsGrounded(rs, grammar, ys1) == True{} : Bool}
  {Run.retsGrounded(rs, grammar, ys2) == True{} : Bool}

def rets_mono(rs, grammar, ys1, ys2, sub, h):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Lemma.and_true_intro(Run.retGround(r, grammar, ys2), Run.retsGrounded(rest, grammar, ys2), ret_mono(r, grammar, ys1, ys2, sub, Lemma.and_true_left(Run.retGround(r, grammar, ys1), Run.retsGrounded(rest, grammar, ys1), h)),
        rets_mono(rest, grammar, ys1, ys2, sub, Lemma.and_true_right_side(Run.retGround(r, grammar, ys1), Run.retsGrounded(rest, grammar, ys1), h)))

law pops_mono:
  for ps: +List<Gll.Pop>
  for +grammar: +List<Core.Production>
  for +ys1: +List<Core.Bsr>
  for +ys2: +List<Core.Bsr>
  for +sub: {Core.allIn(ys1, ys2) == True{} : Bool}
  for +h: {Run.popsGrounded(ps, grammar, ys1) == True{} : Bool}
  {Run.popsGrounded(ps, grammar, ys2) == True{} : Bool}

def pops_mono(ps, grammar, ys1, ys2, sub, h):
  match ps:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      Lemma.and_true_intro(Run.popGround(r, grammar, ys2), Run.popsGrounded(rest, grammar, ys2), pop_mono(r, grammar, ys1, ys2, sub, Lemma.and_true_left(Run.popGround(r, grammar, ys1), Run.popsGrounded(rest, grammar, ys1), h)),
        pops_mono(rest, grammar, ys1, ys2, sub, Lemma.and_true_right_side(Run.popGround(r, grammar, ys1), Run.popsGrounded(rest, grammar, ys1), h)))

law steps_trans:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +zs: +List<Core.Bsr>
  for +h1: {Core.allIn(xs, ys) == True{} : Bool}
  for +h2: {Core.allIn(ys, zs) == True{} : Bool}
  {Core.allIn(xs, zs) == True{} : Bool}

def steps_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, zs), Core.allIn(rest, zs), G.all_in_member(ys, zs, x, h2, Lemma.and_true_left(Core.member(x, ys), Core.allIn(rest, ys), h1)),
        steps_trans(rest, ys, zs, Lemma.and_true_right_side(Core.member(x, ys), Core.allIn(rest, ys), h1), h2))

# ======== ONE OPERATION ========

# The state after rests on its steps, and has kept every step.
def GStep(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState) -> Type:
  {Run.groundOk(grammar, input, t) == True{} : Bool} & {Core.allIn(Check.stepsOf(s), Check.stepsOf(t)) == True{} : Bool}

def gstep_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState, +w1: {Core.allIn(Check.stepsOf(s), Check.stepsOf(s1)) == True{} : Bool}, p2: GStep(grammar, input, s1, t)) -> GStep(grammar, input, s, t):
  match p2:
    case (+g2, w2):
      (g2, steps_trans(Check.stepsOf(s), Check.stepsOf(s1), Check.stepsOf(t), w1, w2))

def gstep_trans(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState, p1: GStep(grammar, input, s, s1), p2: GStep(grammar, input, s1, t)) -> GStep(grammar, input, s, t):
  match p1:
    case (+g1, w1):
      gstep_join(grammar, input, s, s1, t, w1, p2)

def gstep_refl(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool}) -> GStep(grammar, input, s, s):
  (h, C.step_refl(Check.stepsOf(s)))

def step_pick_g(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +y: Core.Bsr, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +gy: {Run.groundedIn(y, grammar, input, ys) == True{} : Bool}, +h: {Run.groundOk(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool}) -> GStep(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.stepPick(b, y, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match b:
    case True{}:
      gstep_refl(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, h)
    case False{}:
      +SG = {Run.stepsGrounded(ys, grammar, input) : Bool}
      +DG = {Run.descsGrounded(seen, ys) : Bool}
      +RG = {Run.retsGrounded(rs, grammar, ys) : Bool}
      +PG = {Run.popsGrounded(ps, grammar, ys) : Bool}
      +r1 = Lemma.and_true_right_side(SG, Bool.and(DG, Bool.and(RG, PG)), h)
      +r2 = Lemma.and_true_right_side(DG, Bool.and(RG, PG), r1)
      +w = C.step_weaken(ys, y, ys, C.step_refl(ys))
      +y2 = {y <> ys : +List<Core.Bsr>}
      +g = Lemma.and_true_intro(Run.stepsGrounded(y2, grammar, input), Bool.and(Run.descsGrounded(seen, y2), Bool.and(Run.retsGrounded(rs, grammar, y2), Run.popsGrounded(ps, grammar, y2))),
        Lemma.and_true_intro(Run.groundedIn(y, grammar, input, ys), SG, gy, Lemma.and_true_left(SG, Bool.and(DG, Bool.and(RG, PG)), h)),
        Lemma.and_true_intro(Run.descsGrounded(seen, y2), Bool.and(Run.retsGrounded(rs, grammar, y2), Run.popsGrounded(ps, grammar, y2)), descs_mono(seen, ys, y2, w, Lemma.and_true_left(DG, Bool.and(RG, PG), r1)),
          Lemma.and_true_intro(Run.retsGrounded(rs, grammar, y2), Run.popsGrounded(ps, grammar, y2), rets_mono(rs, grammar, ys, y2, w, Lemma.and_true_left(RG, PG, r2)),
            pops_mono(ps, grammar, ys, y2, w, Lemma.and_true_right_side(RG, PG, r2)))))
      (g, w)

# A new step whose prefix and item rest on the steps there.
def with_step_g(+grammar: +List<Core.Production>, +input: +List<Nat>, +y: Core.Bsr, s: Gll.GState, +gy: {Run.groundedIn(y, grammar, input, Check.stepsOf(s)) == True{} : Bool}, +h: {Run.groundOk(grammar, input, s) == True{} : Bool}) -> GStep(grammar, input, s, Gll.withStep(y, s)):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      step_pick_g(Core.member(y, ys), grammar, input, y, seen, todo, cs, rs, ps, ys, gy, h)

def desc_pick_g(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +gd: {Run.descGround(d, ys) == True{} : Bool}, +h: {Run.groundOk(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool}) -> GStep(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.descPick(b, d, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match b:
    case True{}:
      gstep_refl(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, h)
    case False{}:
      +SG = {Run.stepsGrounded(ys, grammar, input) : Bool}
      +DG = {Run.descsGrounded(seen, ys) : Bool}
      +RP = {Bool.and(Run.retsGrounded(rs, grammar, ys), Run.popsGrounded(ps, grammar, ys)) : Bool}
      +r1 = Lemma.and_true_right_side(SG, Bool.and(DG, RP), h)
      (Lemma.and_true_intro(SG, Bool.and(Run.descsGrounded(d <> seen, ys), RP), Lemma.and_true_left(SG, Bool.and(DG, RP), h),
         Lemma.and_true_intro(Run.descsGrounded(d <> seen, ys), RP, Lemma.and_true_intro(Run.descGround(d, ys), DG, gd, Lemma.and_true_left(DG, RP, r1)), Lemma.and_true_right_side(DG, RP, r1))),
       C.step_refl(ys))

# A new descriptor whose prefix is done.
def with_desc_g(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, s: Gll.GState, +gd: {Run.descGround(d, Check.stepsOf(s)) == True{} : Bool}, +h: {Run.groundOk(grammar, input, s) == True{} : Bool}) -> GStep(grammar, input, s, Gll.withDesc(d, s)):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      desc_pick_g(Gll.descIn(d, seen), grammar, input, d, seen, todo, cs, rs, ps, ys, gd, h)

# ======== A DESCRIPTOR AND ITS STEP ========

def commute2(b1: Bool, b2: Bool, +d: Gll.Desc, +y: Core.Bsr, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +e1: {Gll.descIn(d, seen) == b1 : Bool}, +e2: {Core.member(y, ys) == b2 : Bool})
  -> {Gll.withStep(y, Gll.descPick(b1, d, Gll.GState{seen, todo, cs, rs, ps, ys})) == Gll.withDesc(d, Gll.stepPick(b2, y, Gll.GState{seen, todo, cs, rs, ps, ys})) : Gll.GState}:
  match b1 b2:
    case True{} True{}:
      %Equal.sym(Bool, Core.member(y, ys), True{}, e2) : {Gll.stepPick(_, y, Gll.GState{seen, todo, cs, rs, ps, ys}) == Gll.descPick(Gll.descIn(d, seen), d, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}
      %Equal.sym(Bool, Gll.descIn(d, seen), True{}, e1) : {Gll.GState{seen, todo, cs, rs, ps, ys} == Gll.descPick(_, d, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}
      {==}
    case True{} False{}:
      +t = {Gll.GState{seen, todo, cs, rs, ps, y <> ys} : Gll.GState}
      %Equal.sym(Bool, Core.member(y, ys), False{}, e2) : {Gll.stepPick(_, y, Gll.GState{seen, todo, cs, rs, ps, ys}) == Gll.descPick(Gll.descIn(d, seen), d, t) : Gll.GState}
      %Equal.sym(Bool, Gll.descIn(d, seen), True{}, e1) : {t == Gll.descPick(_, d, t) : Gll.GState}
      {==}
    case False{} True{}:
      +t = {Gll.GState{d <> seen, d <> todo, cs, rs, ps, ys} : Gll.GState}
      %Equal.sym(Bool, Core.member(y, ys), True{}, e2) : {Gll.stepPick(_, y, t) == Gll.descPick(Gll.descIn(d, seen), d, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}
      %Equal.sym(Bool, Gll.descIn(d, seen), False{}, e1) : {t == Gll.descPick(_, d, Gll.GState{seen, todo, cs, rs, ps, ys}) : Gll.GState}
      {==}
    case False{} False{}:
      +t = {Gll.GState{d <> seen, d <> todo, cs, rs, ps, ys} : Gll.GState}
      +u = {Gll.GState{seen, todo, cs, rs, ps, y <> ys} : Gll.GState}
      %Equal.sym(Bool, Core.member(y, ys), False{}, e2) : {Gll.stepPick(_, y, t) == Gll.descPick(Gll.descIn(d, seen), d, u) : Gll.GState}
      %Equal.sym(Bool, Gll.descIn(d, seen), False{}, e1) : {Gll.GState{d <> seen, d <> todo, cs, rs, ps, y <> ys} == Gll.descPick(_, d, u) : Gll.GState}
      {==}

# Adding a descriptor and adding a step commute.
law commute:
  for +d: Gll.Desc
  for +y: Core.Bsr
  for s: Gll.GState
  {Gll.withStep(y, Gll.withDesc(d, s)) == Gll.withDesc(d, Gll.withStep(y, s)) : Gll.GState}

def commute(d, y, s):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      commute2(Gll.descIn(d, seen), Core.member(y, ys), d, y, seen, todo, cs, rs, ps, ys, {==}, {==})

def step_in_pick(b: Bool, +y: Core.Bsr, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +e: {Core.member(y, ys) == b : Bool}) -> {Core.member(y, Check.stepsOf(Gll.stepPick(b, y, Gll.GState{seen, todo, cs, rs, ps, ys}))) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      Lemma.or_true_left_intro(Core.bsrEq(y, y), Core.member(y, ys), C.bsr_eq_refl(y))

def step_in_with(+y: Core.Bsr, s: Gll.GState) -> {Core.member(y, Check.stepsOf(Gll.withStep(y, s))) == True{} : Bool}:
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      step_in_pick(Core.member(y, ys), y, seen, todo, cs, rs, ps, ys, {==})

def done_self(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +mid: Nat) -> {Run.doneBy(q, ks, d, e, Core.Bsr{q, d, ks, mid, e}) == True{} : Bool}:
  Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e))), Lemma.nat_eq_refl(q),
    Lemma.and_true_intro(Nat.is_eq(ks, ks), Bool.and(Nat.is_eq(d, d), Nat.is_eq(e, e)), Lemma.nat_eq_refl(ks),
      Lemma.and_true_intro(Nat.is_eq(d, d), Nat.is_eq(e, e), Lemma.nat_eq_refl(d), Lemma.nat_eq_refl(e))))

def ground_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +t1: Gll.GState, +t2: Gll.GState, +e: {t1 == t2 : Gll.GState}, +g: {Run.groundOk(grammar, input, t2) == True{} : Bool}) -> {Run.groundOk(grammar, input, t1) == True{} : Bool}:
  %Equal.sym(Gll.GState, t1, t2, e) : {Run.groundOk(grammar, input, _) == True{} : Bool}
  g

def steps_to(+xs: +List<Core.Bsr>, +t1: Gll.GState, +t2: Gll.GState, +e: {t1 == t2 : Gll.GState}, +w: {Core.allIn(xs, Check.stepsOf(t2)) == True{} : Bool}) -> {Core.allIn(xs, Check.stepsOf(t1)) == True{} : Bool}:
  %Equal.sym(Gll.GState, t1, t2, e) : {Core.allIn(xs, Check.stepsOf(_)) == True{} : Bool}
  w

def gstep_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t1: Gll.GState, +t2: Gll.GState, +e: {t1 == t2 : Gll.GState}, p: GStep(grammar, input, s, t2)) -> GStep(grammar, input, s, t1):
  match p:
    case (+g, w):
      (ground_to(grammar, input, t1, t2, e, g), steps_to(Check.stepsOf(s), t1, t2, e, w))

def resume_two_g(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, p1: GStep(grammar, input, s, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s)))
  -> GStep(grammar, input, s, Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s))):
  match p1:
    case (+g1, +w1):
      +s1 = Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s)
      +gd = done_of_member(q, k, 1n+dot, j, Core.Bsr{q, 1n+dot, k, kc, j}, Check.stepsOf(s1), step_in_with(Core.Bsr{q, 1n+dot, k, kc, j}, s), done_self(q, k, 1n+dot, j, kc))
      gstep_join(grammar, input, s, s1, Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, s1), w1, with_desc_g(grammar, input, Gll.Desc{q, 1n+dot, k, j}, s1, gd, g1))

# A resumed step and its descriptor: the step first, then the descriptor its step completes.
def resume_pick_g(ok: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +gp: {Run.prefixDone(q, k, dot, kc, Check.stepsOf(s)) == True{} : Bool},
  gi: {ok == True{} : Bool} -> {Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, kc, j, Check.stepsOf(s)) == True{} : Bool})
  -> GStep(grammar, input, s, Gll.resumePick(ok, q, dot, k, kc, j, s)):
  match ok:
    case True{}:
      gstep_to(grammar, input, s, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, s)), Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s)), commute(Gll.Desc{q, 1n+dot, k, j}, Core.Bsr{q, 1n+dot, k, kc, j}, s), resume_two_g(grammar, input, q, dot, k, kc, j, s,
        with_step_g(grammar, input, Core.Bsr{q, 1n+dot, k, kc, j}, s, Lemma.and_true_intro(Run.prefixDone(q, k, dot, kc, Check.stepsOf(s)), Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, kc, j, Check.stepsOf(s)), gp, gi({==})), h)))
    case False{}:
      gstep_refl(grammar, input, s, h)

# ======== RESUMING ========

def nat_to(+a: Nat, +b: Nat, +x: Nat, +kc: Nat, +j: Nat, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +e: {a == b : Nat},
  +h: {Run.prodDone(grammar, 0n, b, kc, j, ys) == True{} : Bool}) -> {Run.prodDone(grammar, 0n, a, kc, j, ys) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Run.prodDone(grammar, 0n, _, kc, j, ys) == True{} : Bool}
  h

# The resumed item: a nonterminal x whose production is done, within its need.
def item_from(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +j: Nat, +ys: +List<Core.Bsr>,
  +hnt: {Run.itemIsNT(item, x) == True{} : Bool}, +hn: {Gll.needHolds(Gll.needOf(item), kc, j) == True{} : Bool},
  +pd: {Run.prodDone(grammar, 0n, x, kc, j, ys) == True{} : Bool}) -> {Run.itemDone(item, grammar, input, kc, j, ys) == True{} : Bool}:
  match item:
    case Some{Core.Nonterminal{+x2, +need}}:
      Lemma.and_true_intro(Gll.needHolds(need, kc, j), Run.prodDone(grammar, 0n, x2, kc, j, ys), hn, nat_to(x2, x, x, kc, j, grammar, ys, Lemma.nat_eq_sound(x2, x, hnt), pd))
    case Some{Core.Terminal{+t}}:
      Empty.absurd({Run.itemDone(Some{Core.Terminal{t}}, grammar, input, kc, j, ys) == True{} : Bool}, Lemma.false_is_not_true(hnt))
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hnt))

def resume_g(edge: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +rg: {Run.edgeGround(edge, x, kc, grammar, Check.stepsOf(s)) == True{} : Bool}, +pd: {Run.prodDone(grammar, 0n, x, kc, j, Check.stepsOf(s)) == True{} : Bool})
  -> GStep(grammar, input, s, Gll.resume(grammar, edge, kc, j, s)):
  match edge:
    case Gll.Edge{+q, +dot, +k}:
      +item = Gll.nthSym(Core.rhsOf(grammar, q), dot)
      +P = {Run.prefixDone(q, k, dot, kc, Check.stepsOf(s)) : Bool}
      resume_pick_g(Gll.needHolds(Gll.needAt(grammar, q, dot), kc, j), grammar, input, q, dot, k, kc, j, s, h, Lemma.and_true_left(P, Run.itemIsNT(item, x), rg),
        ok => item_from(item, grammar, input, x, kc, j, Check.stepsOf(s), Lemma.and_true_right_side(P, Run.itemIsNT(item, x), rg), ok, pd))

def resume_if_g(hit: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +edge: Gll.Edge, +x: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  rg: {hit == True{} : Bool} -> {Run.edgeGround(edge, x, kc, grammar, Check.stepsOf(s)) == True{} : Bool},
  pd: {hit == True{} : Bool} -> {Run.prodDone(grammar, 0n, x, kc, j, Check.stepsOf(s)) == True{} : Bool})
  -> GStep(grammar, input, s, Gll.resumeIf(hit, grammar, edge, kc, j, s)):
  match hit:
    case True{}:
      resume_g(edge, grammar, input, x, kc, j, s, h, rg({==}), pd({==}))
    case False{}:
      gstep_refl(grammar, input, s, h)

def key_parts(+x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat, +eh: {Gll.keyEq(Gll.CKey{x, kc}, Gll.CKey{x2, kc2}) == True{} : Bool})
  -> {x2 == x : Nat} & {kc2 == kc : Nat}:
  +a = Lemma.and_true_left(Nat.is_eq(x, x2), Nat.is_eq(kc, kc2), eh)
  +b = Lemma.and_true_right_side(Nat.is_eq(x, x2), Nat.is_eq(kc, kc2), eh)
  (Equal.sym(Nat, x, x2, Lemma.nat_eq_sound(x, x2, a)), Equal.sym(Nat, kc, kc2, Lemma.nat_eq_sound(kc, kc2, b)))

def edge_keys2(+e: Gll.Edge, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat, +ex: {x2 == x : Nat}, +ek: {kc2 == kc : Nat},
  +h: {Run.edgeGround(e, x2, kc2, grammar, ys) == True{} : Bool}) -> {Run.edgeGround(e, x, kc, grammar, ys) == True{} : Bool}:
  %ex : {Run.edgeGround(e, _, kc, grammar, ys) == True{} : Bool}
  %ek : {Run.edgeGround(e, x2, _, grammar, ys) == True{} : Bool}
  h

def pop_keys2(+j: Nat, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat, +ex: {x2 == x : Nat}, +ek: {kc2 == kc : Nat},
  +h: {Run.prodDone(grammar, 0n, x2, kc2, j, ys) == True{} : Bool}) -> {Run.prodDone(grammar, 0n, x, kc, j, ys) == True{} : Bool}:
  %ex : {Run.prodDone(grammar, 0n, _, kc, j, ys) == True{} : Bool}
  %ek : {Run.prodDone(grammar, 0n, x2, _, j, ys) == True{} : Bool}
  h

def edge_keys(+e: Gll.Edge, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat,
  p: {x2 == x : Nat} & {kc2 == kc : Nat}, +h: {Run.edgeGround(e, x2, kc2, grammar, ys) == True{} : Bool}) -> {Run.edgeGround(e, x, kc, grammar, ys) == True{} : Bool}:
  match p:
    case (+ex, ek):
      edge_keys2(e, grammar, ys, x, kc, x2, kc2, ex, ek, h)

# A return edge of the hit key: the key's components are the cluster's.
def hit_edge(+x: Nat, +kc: Nat, k2: Gll.CKey, +e2: Gll.Edge, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>,
  +eh: {Gll.keyEq(Gll.CKey{x, kc}, k2) == True{} : Bool}, +h: {Run.retGround(Gll.Ret{k2, e2}, grammar, ys) == True{} : Bool})
  -> {Run.edgeGround(e2, x, kc, grammar, ys) == True{} : Bool}:
  match k2:
    case Gll.CKey{+x2, +kc2}:
      edge_keys(e2, grammar, ys, x, kc, x2, kc2, key_parts(x, kc, x2, kc2, eh), h)

def pop_keys(+j: Nat, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat,
  p: {x2 == x : Nat} & {kc2 == kc : Nat}, +h: {Run.prodDone(grammar, 0n, x2, kc2, j, ys) == True{} : Bool}) -> {Run.prodDone(grammar, 0n, x, kc, j, ys) == True{} : Bool}:
  match p:
    case (+ex, ek):
      pop_keys2(j, grammar, ys, x, kc, x2, kc2, ex, ek, h)

def hit_pop(+x: Nat, +kc: Nat, k2: Gll.CKey, +j: Nat, +grammar: +List<Core.Production>, +ys: +List<Core.Bsr>,
  +eh: {Gll.keyEq(Gll.CKey{x, kc}, k2) == True{} : Bool}, +h: {Run.popGround(Gll.Pop{k2, j}, grammar, ys) == True{} : Bool})
  -> {Run.prodDone(grammar, 0n, x, kc, j, ys) == True{} : Bool}:
  match k2:
    case Gll.CKey{+x2, +kc2}:
      pop_keys(j, grammar, ys, x, kc, x2, kc2, key_parts(x, kc, x2, kc2, eh), h)

def all_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +j: Nat, +rest: +List<Gll.Ret>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +hr: {Run.retsGrounded(rest, grammar, Check.stepsOf(s)) == True{} : Bool}, +pd: {Run.prodDone(grammar, 0n, x, kc, j, Check.stepsOf(s)) == True{} : Bool},
  p1: GStep(grammar, input, s, s1),
  later: {Run.groundOk(grammar, input, s1) == True{} : Bool} -> {Run.retsGrounded(rest, grammar, Check.stepsOf(s1)) == True{} : Bool} -> {Run.prodDone(grammar, 0n, x, kc, j, Check.stepsOf(s1)) == True{} : Bool} -> GStep(grammar, input, s1, t))
  -> GStep(grammar, input, s, t):
  match p1:
    case (+g1, +w1):
      gstep_join(grammar, input, s, s1, t, w1,
        later(g1, rets_mono(rest, grammar, Check.stepsOf(s), Check.stepsOf(s1), w1, hr), prod_mono(grammar, 0n, x, kc, j, Check.stepsOf(s), Check.stepsOf(s1), w1, pd)))

# Resuming every caller of a cluster that ended, given the pop's production is done.
law resume_all_g:
  for rets: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +j: Nat
  for +s: Gll.GState
  for +h: {Run.groundOk(grammar, input, s) == True{} : Bool}
  for +hr: {Run.retsGrounded(rets, grammar, Check.stepsOf(s)) == True{} : Bool}
  for +pd: {Run.popGround(Gll.Pop{key, j}, grammar, Check.stepsOf(s)) == True{} : Bool}
  GStep(grammar, input, s, Gll.resumeAll(rets, grammar, key, j, s))

def resume_all_g(rets, grammar, input, key, j, s, h, hr, pd):
  match rets key:
    case Nil{} +key0:
      gstep_refl(grammar, input, s, h)
    case Con{Gll.Ret{+k2, +e2}, +rest} Gll.CKey{+x, +kc}:
      +hd = Lemma.and_true_left(Run.retGround(Gll.Ret{k2, e2}, grammar, Check.stepsOf(s)), Run.retsGrounded(rest, grammar, Check.stepsOf(s)), hr)
      +tl = Lemma.and_true_right_side(Run.retGround(Gll.Ret{k2, e2}, grammar, Check.stepsOf(s)), Run.retsGrounded(rest, grammar, Check.stepsOf(s)), hr)
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)
      all_join(grammar, input, x, kc, j, rest, s, s1, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, s1), tl, pd,
        resume_if_g(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, input, e2, x, kc, j, s, h, eh => hit_edge(x, kc, k2, e2, grammar, Check.stepsOf(s), eh, hd), z => pd),
        g1 => r1 => p1 => resume_all_g(rest, grammar, input, Gll.CKey{x, kc}, j, s1, g1, r1, p1))

def pops_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +edge: Gll.Edge, +rest: +List<Gll.Pop>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +hp: {Run.popsGrounded(rest, grammar, Check.stepsOf(s)) == True{} : Bool}, +eg: {Run.edgeGround(edge, x, kc, grammar, Check.stepsOf(s)) == True{} : Bool},
  p1: GStep(grammar, input, s, s1),
  later: {Run.groundOk(grammar, input, s1) == True{} : Bool} -> {Run.popsGrounded(rest, grammar, Check.stepsOf(s1)) == True{} : Bool} -> {Run.edgeGround(edge, x, kc, grammar, Check.stepsOf(s1)) == True{} : Bool} -> GStep(grammar, input, s1, t))
  -> GStep(grammar, input, s, t):
  match p1:
    case (+g1, +w1):
      gstep_join(grammar, input, s, s1, t, w1,
        later(g1, pops_mono(rest, grammar, Check.stepsOf(s), Check.stepsOf(s1), w1, hp), edge_mono(edge, x, kc, grammar, Check.stepsOf(s), Check.stepsOf(s1), w1, eg)))

# Resuming a new caller at every place its cluster already ended.
law resume_pops_g:
  for pops: +List<Gll.Pop>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +edge: Gll.Edge
  for +s: Gll.GState
  for +h: {Run.groundOk(grammar, input, s) == True{} : Bool}
  for +hp: {Run.popsGrounded(pops, grammar, Check.stepsOf(s)) == True{} : Bool}
  for +eg: {Run.retGround(Gll.Ret{key, edge}, grammar, Check.stepsOf(s)) == True{} : Bool}
  GStep(grammar, input, s, Gll.resumePops(pops, grammar, key, edge, s))

def resume_pops_g(pops, grammar, input, key, edge, s, h, hp, eg):
  match pops key:
    case Nil{} +key0:
      gstep_refl(grammar, input, s, h)
    case Con{Gll.Pop{+k2, +j}, +rest} Gll.CKey{+x, +kc}:
      +hd = Lemma.and_true_left(Run.popGround(Gll.Pop{k2, j}, grammar, Check.stepsOf(s)), Run.popsGrounded(rest, grammar, Check.stepsOf(s)), hp)
      +tl = Lemma.and_true_right_side(Run.popGround(Gll.Pop{k2, j}, grammar, Check.stepsOf(s)), Run.popsGrounded(rest, grammar, Check.stepsOf(s)), hp)
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)
      pops_join(grammar, input, x, kc, edge, rest, s, s1, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, s1), tl, eg,
        resume_if_g(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, input, edge, x, kc, j, s, h, z => eg, eh => hit_pop(x, kc, k2, j, grammar, Check.stepsOf(s), eh, hd)),
        g1 => p1 => e1 => resume_pops_g(rest, grammar, input, Gll.CKey{x, kc}, edge, s1, g1, p1, e1))

# ======== SEEDS, CALLS, LEAVES ========

# A seed: the empty prefix of a production, where it starts.
def zeroDesc(d: Gll.Desc) -> Bool:
  match d:
    case Gll.Desc{+q, 0n, +k, +i}:
      Nat.is_eq(k, i)
    case Gll.Desc{+q, 1n+(+m), +k, +i}:
      False{}

def allZero(ds: +List<Gll.Desc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, rest}:
      Bool.and(zeroDesc(d), allZero(rest))

def zero_ground(d: Gll.Desc, +ys: +List<Core.Bsr>, +h: {zeroDesc(d) == True{} : Bool}) -> {Run.descGround(d, ys) == True{} : Bool}:
  match d:
    case Gll.Desc{+q, 0n, +k, +i}:
      h
    case Gll.Desc{+q, 1n+(+m), +k, +i}:
      Empty.absurd({Run.descGround(Gll.Desc{q, 1n+m, k, i}, ys) == True{} : Bool}, Lemma.false_is_not_true(h))

def keep_zero(c: Bool, +base: Nat, +i: Nat, +more: +List<Gll.Desc>, +h: {allZero(more) == True{} : Bool})
  -> {allZero(Gll.keepDesc(c, Gll.Desc{base, 0n, i, i}, more)) == True{} : Bool}:
  match c:
    case True{}:
      Lemma.and_true_intro(Nat.is_eq(i, i), allZero(more), Lemma.nat_eq_refl(i), h)
    case False{}:
      h

law seeds_zero:
  for g: +List<Core.Production>
  for +base: Nat
  for +pred: Gll.Pred
  for +tok: Maybe<&2, Nat>
  for +x: Nat
  for +i: Nat
  {allZero(Gll.productionsOf(g, pred, tok, x, base, i)) == True{} : Bool}

def seeds_zero(g, base, pred, tok, x, i):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      keep_zero(Bool.and(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x)), base, i, Gll.productionsOf(rest, pred, tok, x, 1n+base, i), seeds_zero(rest, 1n+base, pred, tok, x, i))

def descs_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState, p1: GStep(grammar, input, s, s1), later: {Run.groundOk(grammar, input, s1) == True{} : Bool} -> GStep(grammar, input, s1, t)) -> GStep(grammar, input, s, t):
  match p1:
    case (+g1, +w1):
      gstep_join(grammar, input, s, s1, t, w1, later(g1))

law with_descs_g:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +h: {Run.groundOk(grammar, input, s) == True{} : Bool}
  for +hz: {allZero(ds) == True{} : Bool}
  GStep(grammar, input, s, Gll.withDescs(ds, s))

def with_descs_g(ds, grammar, input, s, h, hz):
  match ds:
    case Nil{}:
      gstep_refl(grammar, input, s, h)
    case Con{+d, +rest}:
      +s1 = Gll.withDesc(d, s)
      descs_join(grammar, input, s, s1, Gll.withDescs(rest, s1),
        with_desc_g(grammar, input, d, s, zero_ground(d, Check.stepsOf(s), Lemma.and_true_left(zeroDesc(d), allZero(rest), hz)), h),
        g1 => with_descs_g(rest, grammar, input, s1, g1, Lemma.and_true_right_side(zeroDesc(d), allZero(rest), hz)))

def call_pick_g2(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +g0: {Run.groundOk(grammar, input, Gll.GState{seen, todo, cs, Gll.Ret{key, edge} <> rs, ps, ys}) == True{} : Bool},
  +hp: {Run.popsGrounded(ps, grammar, ys) == True{} : Bool}, +eg: {Run.retGround(Gll.Ret{key, edge}, grammar, ys) == True{} : Bool}, +hz: {allZero(seeds) == True{} : Bool})
  -> GStep(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.callPick(b, grammar, key, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match b:
    case False{}:
      with_descs_g(seeds, grammar, input, Gll.GState{seen, todo, key <> cs, Gll.Ret{key, edge} <> rs, ps, ys}, g0, hz)
    case True{}:
      resume_pops_g(ps, grammar, input, key, edge, Gll.GState{seen, todo, cs, Gll.Ret{key, edge} <> rs, ps, ys}, g0, hp, eg)

def call_pick_g(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +edge: Gll.Edge, +seeds: +List<Gll.Desc>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +h: {Run.groundOk(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool}, +eg: {Run.retGround(Gll.Ret{key, edge}, grammar, ys) == True{} : Bool}, +hz: {allZero(seeds) == True{} : Bool})
  -> GStep(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.callPick(b, grammar, key, edge, seeds, Gll.GState{seen, todo, cs, rs, ps, ys})):
  +SG = {Run.stepsGrounded(ys, grammar, input) : Bool}
  +DG = {Run.descsGrounded(seen, ys) : Bool}
  +RG = {Run.retsGrounded(rs, grammar, ys) : Bool}
  +PG = {Run.popsGrounded(ps, grammar, ys) : Bool}
  +r1 = Lemma.and_true_right_side(SG, Bool.and(DG, Bool.and(RG, PG)), h)
  +r2 = Lemma.and_true_right_side(DG, Bool.and(RG, PG), r1)
  +rs2 = {Gll.Ret{key, edge} <> rs : +List<Gll.Ret>}
  +g0 = Lemma.and_true_intro(SG, Bool.and(DG, Bool.and(Run.retsGrounded(rs2, grammar, ys), PG)), Lemma.and_true_left(SG, Bool.and(DG, Bool.and(RG, PG)), h),
    Lemma.and_true_intro(DG, Bool.and(Run.retsGrounded(rs2, grammar, ys), PG), Lemma.and_true_left(DG, Bool.and(RG, PG), r1),
      Lemma.and_true_intro(Run.retsGrounded(rs2, grammar, ys), PG, Lemma.and_true_intro(Run.retGround(Gll.Ret{key, edge}, grammar, ys), RG, eg, Lemma.and_true_left(RG, PG, r2)), Lemma.and_true_right_side(RG, PG, r2))))
  call_pick_g2(b, grammar, input, key, edge, seeds, seen, todo, cs, rs, ps, ys, g0, Lemma.and_true_right_side(RG, PG, r2), eg, hz)

# A call: a new return edge whose caller's prefix is done, then seeds or resumes.
def call_g(+grammar: +List<Core.Production>, +input: +List<Nat>, +pred: Gll.Pred, +x: Nat, +i: Nat, +edge: Gll.Edge, s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +eg: {Run.retGround(Gll.Ret{Gll.CKey{x, i}, edge}, grammar, Check.stepsOf(s)) == True{} : Bool}) -> GStep(grammar, input, s, Gll.call(pred, grammar, input, x, i, edge, s)):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      +key = {Gll.CKey{x, i} : Gll.CKey}
      +seeds = Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i)
      call_pick_g(Gll.keyIn(key, cs), grammar, input, key, edge, seeds, seen, todo, cs, rs, ps, ys, h, eg, seeds_zero(grammar, 0n, pred, Core.tokAt(input, i), x, i))

def leave_pick_g(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +j: Nat,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +h: {Run.groundOk(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool}, +pg: {Run.popGround(Gll.Pop{key, j}, grammar, ys) == True{} : Bool})
  -> GStep(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.leavePick(b, grammar, key, j, Gll.GState{seen, todo, cs, rs, ps, ys})):
  match b:
    case True{}:
      gstep_refl(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, h)
    case False{}:
      +SG = {Run.stepsGrounded(ys, grammar, input) : Bool}
      +DG = {Run.descsGrounded(seen, ys) : Bool}
      +RG = {Run.retsGrounded(rs, grammar, ys) : Bool}
      +PG = {Run.popsGrounded(ps, grammar, ys) : Bool}
      +r1 = Lemma.and_true_right_side(SG, Bool.and(DG, Bool.and(RG, PG)), h)
      +r2 = Lemma.and_true_right_side(DG, Bool.and(RG, PG), r1)
      +ps2 = {Gll.Pop{key, j} <> ps : +List<Gll.Pop>}
      +s0 = {Gll.GState{seen, todo, cs, rs, ps2, ys} : Gll.GState}
      +g0 = Lemma.and_true_intro(SG, Bool.and(DG, Bool.and(RG, Run.popsGrounded(ps2, grammar, ys))), Lemma.and_true_left(SG, Bool.and(DG, Bool.and(RG, PG)), h),
        Lemma.and_true_intro(DG, Bool.and(RG, Run.popsGrounded(ps2, grammar, ys)), Lemma.and_true_left(DG, Bool.and(RG, PG), r1),
          Lemma.and_true_intro(RG, Run.popsGrounded(ps2, grammar, ys), Lemma.and_true_left(RG, PG, r2),
            Lemma.and_true_intro(Run.popGround(Gll.Pop{key, j}, grammar, ys), PG, pg, Lemma.and_true_right_side(RG, PG, r2)))))
      resume_all_g(rs, grammar, input, key, j, s0, g0, Lemma.and_true_left(RG, PG, r2), pg)

# Leaving a cluster: a new pop, its production done, resumes every caller.
def leave_g(+grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +j: Nat, s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +pg: {Run.popGround(Gll.Pop{key, j}, grammar, Check.stepsOf(s)) == True{} : Bool}) -> GStep(grammar, input, s, Gll.leave(grammar, key, j, s)):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      leave_pick_g(Gll.popIn(key, j, ps), grammar, input, key, j, seen, todo, cs, rs, ps, ys, h, pg)

# ======== THE END OF A PRODUCTION ========

def maybeSome(m: Maybe<&2, Core.Sym>) -> Bool:
  match m:
    case Some{s}:
      True{}
    case None{}:
      False{}

def none_empty(items: +List<Core.Sym>, +h: {Gll.nthSym(items, 0n) == None{} : Maybe<&2, Core.Sym>}) -> {List.is_empty(&2, Core.Sym, items) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Core.Sym>, Bool, v => maybeSome(v), Some{x}, None{}, h)))

def empty_len(items: +List<Core.Sym>, +h: {List.is_empty(&2, Core.Sym, items) == True{} : Bool}) -> {List.length(&2, Core.Sym, items) == 0n : Nat}:
  match items:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Empty.absurd({1n+List.length(&2, Core.Sym, rest) == 0n : Nat}, Lemma.false_is_not_true(h))

law len_of_none:
  for items: +List<Core.Sym>
  for d: Nat
  for +h: {Gll.nthSym(items, d) == None{} : Maybe<&2, Core.Sym>}
  for +hb: {Nat.is_le(d, List.length(&2, Core.Sym, items)) == True{} : Bool}
  {d == List.length(&2, Core.Sym, items) : Nat}

def len_of_none(items, d, h, hb):
  match items d:
    case Nil{} +d0:
      C.le_zero_eq(d0, hb)
    case Con{+x, +rest} 0n:
      Empty.absurd({0n == 1n+List.length(&2, Core.Sym, rest) : Nat}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Core.Sym>, Bool, v => maybeSome(v), Some{x}, None{}, h)))
    case Con{+x, +rest} 1n+(+m):
      Equal.cong(Nat, Nat, v => 1n+v, m, List.length(&2, Core.Sym, rest), len_of_none(rest, m, h, hb))

law lhs_of:
  for grammar: +List<Core.Production>
  for q: Nat
  for +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool}
  {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == True{} : Bool}

def lhs_of(grammar, q, hq):
  match grammar q:
    case Nil{} +q0:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hq))
    case Con{Core.Production{+l, +r}, +rest} 0n:
      Lemma.nat_eq_refl(l)
    case Con{Core.Production{+l, +r}, +rest} 1n+(+n):
      lhs_of(rest, n, hq)

def seg_base0(+base: Nat, +k: Nat, +len: Nat, +j: Nat, +ys: +List<Core.Bsr>, +h: {Run.segDone(Nat.add(base, 0n), k, len, j, ys) == True{} : Bool})
  -> {Run.segDone(base, k, len, j, ys) == True{} : Bool}:
  %Lemma.add_zero_right(base) : {Run.segDone(_, k, len, j, ys) == True{} : Bool}
  h

def seg_base1(+base: Nat, +n: Nat, +k: Nat, +len: Nat, +j: Nat, +ys: +List<Core.Bsr>, +h: {Run.segDone(Nat.add(base, 1n+n), k, len, j, ys) == True{} : Bool})
  -> {Run.segDone(Nat.add(1n+base, n), k, len, j, ys) == True{} : Bool}:
  %Lemma.add_succ_right(base, n) : {Run.segDone(_, k, len, j, ys) == True{} : Bool}
  h

# A production done, and its nonterminal, give the nonterminal done.
law prod_done:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +k: Nat
  for +j: Nat
  for +ys: +List<Core.Bsr>
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +hs: {Run.segDone(Nat.add(base, q), k, List.length(&2, Core.Sym, Core.rhsOf(g, q)), j, ys) == True{} : Bool}
  {Run.prodDone(g, base, x, k, j, ys) == True{} : Bool}

def prod_done(g, q, x, base, k, j, ys, h, hs):
  match g q:
    case Nil{} +q0:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +len = List.length(&2, Core.Sym, rhs)
      Lemma.or_true_left_intro(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys)), Run.prodDone(rest, 1n+base, x, k, j, ys),
        Lemma.and_true_intro(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys), h, seg_base0(base, k, len, j, ys, hs)))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +len = List.length(&2, Core.Sym, rhs)
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(lhs, x), Run.segDone(base, k, len, j, ys)), Run.prodDone(rest, 1n+base, x, k, j, ys),
        prod_done(rest, n, x, 1n+base, k, j, ys, h, seg_base1(base, n, k, List.length(&2, Core.Sym, Core.rhsOf(rest, n)), j, ys, hs)))

def seg_len(+q: Nat, +k: Nat, +a: Nat, +b: Nat, +j: Nat, +ys: +List<Core.Bsr>, +e: {a == b : Nat},
  +h: {Run.segDone(q, k, a, j, ys) == True{} : Bool}) -> {Run.segDone(q, k, b, j, ys) == True{} : Bool}:
  %e : {Run.segDone(q, k, _, j, ys) == True{} : Bool}
  h

def end_zero(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +he: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == True{} : Bool},
  p1: GStep(grammar, input, s, Gll.withStep(Core.Bsr{q, 0n, k, i, i}, s)))
  -> GStep(grammar, input, s, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Gll.withStep(Core.Bsr{q, 0n, k, i, i}, s))):
  match p1:
    case (+g1, +w1):
      +b0 = {Core.Bsr{q, 0n, k, i, i} : Core.Bsr}
      +s1 = Gll.withStep(b0, s)
      +sd = done_of_member(q, k, 0n, i, b0, Check.stepsOf(s1), step_in_with(b0, s), done_self(q, k, 0n, i, i))
      +pg = prod_done(grammar, q, Gll.lhsOf(grammar, q), 0n, k, i, Check.stepsOf(s1), lhs_of(grammar, q, hq),
        seg_len(q, k, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), i, Check.stepsOf(s1), Equal.sym(Nat, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), 0n, empty_len(Core.rhsOf(grammar, q), he)), sd))
      gstep_join(grammar, input, s, s1, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, s1), w1, leave_g(grammar, input, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, s1, g1, pg))

# The end of a production: the empty step if it is empty, then the pop of its cluster.
def end_g(dot: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +gp: {Run.prefixDone(q, k, dot, i, Check.stepsOf(s)) == True{} : Bool},
  +gn: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == None{} : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool})
  -> GStep(grammar, input, s, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Gll.emptyIf(dot, q, k, i, s))):
  match dot:
    case 0n:
      +he = none_empty(Core.rhsOf(grammar, q), gn)
      end_zero(grammar, input, q, k, i, s, hq, he,
        with_step_g(grammar, input, Core.Bsr{q, 0n, k, i, i}, s, Lemma.and_true_intro(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Bool.and(Nat.is_eq(k, i), Nat.is_eq(i, i)), he,
          Lemma.and_true_intro(Nat.is_eq(k, i), Nat.is_eq(i, i), gp, Lemma.nat_eq_refl(i))), h))
    case 1n+(+m):
      leave_g(grammar, input, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, s, h,
        prod_done(grammar, q, Gll.lhsOf(grammar, q), 0n, k, i, Check.stepsOf(s), lhs_of(grammar, q, hq), seg_len(q, k, 1n+m, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), i, Check.stepsOf(s), len_of_none(Core.rhsOf(grammar, q), 1n+m, gn, hd), gp)))

# ======== ONE STEP ========

def match_g(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +gp: {Run.prefixDone(q, k, dot, i, Check.stepsOf(s)) == True{} : Bool},
  gi: {b == True{} : Bool} -> {Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, i, 1n+i, Check.stepsOf(s)) == True{} : Bool}) -> GStep(grammar, input, s, Gll.matchToken(b, q, dot, k, i, s)):
  match b:
    case True{}:
      resume_pick_g(True{}, grammar, input, q, dot, k, i, 1n+i, s, h, gp, z => gi({==}))
    case False{}:
      gstep_refl(grammar, input, s, h)

def item_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +item: Maybe<&2, Core.Sym>, +k: Nat, +j: Nat, +ys: +List<Core.Bsr>,
  +ie: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == item : Maybe<&2, Core.Sym>}, +h: {Run.itemDone(item, grammar, input, k, j, ys) == True{} : Bool}) -> {Run.itemDone(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, k, j, ys) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), dot), item, ie) : {Run.itemDone(_, grammar, input, k, j, ys) == True{} : Bool}
  h

def nt_to(+grammar: +List<Core.Production>, +q: Nat, +dot: Nat, +item: Maybe<&2, Core.Sym>, +x: Nat,
  +ie: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == item : Maybe<&2, Core.Sym>}, +h: {Run.itemIsNT(item, x) == True{} : Bool}) -> {Run.itemIsNT(Gll.nthSym(Core.rhsOf(grammar, q), dot), x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), dot), item, ie) : {Run.itemIsNT(_, x) == True{} : Bool}
  h

def step_item_g(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +pred: Gll.Pred, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +h: {Run.groundOk(grammar, input, s) == True{} : Bool},
  +gp: {Run.prefixDone(q, k, dot, i, Check.stepsOf(s)) == True{} : Bool},
  +ie: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == item : Maybe<&2, Core.Sym>},
  +hq: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool})
  -> GStep(grammar, input, s, Gll.stepItem(item, pred, grammar, input, q, dot, k, i, s)):
  match item:
    case Some{Core.Terminal{+t}}:
      match_g(Core.tokIs(Core.tokAt(input, i), t), grammar, input, q, dot, k, i, s, h, gp,
        eb => item_to(grammar, input, q, dot, Some{Core.Terminal{t}}, i, 1n+i, Check.stepsOf(s), ie,
          Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, i), t), Nat.is_eq(1n+i, 1n+i), eb, Lemma.nat_eq_refl(1n+i))))
    case Some{Core.Nonterminal{+x, +need}}:
      call_g(grammar, input, pred, x, i, Gll.Edge{q, dot, k}, s, h,
        Lemma.and_true_intro(Run.prefixDone(q, k, dot, i, Check.stepsOf(s)), Run.itemIsNT(Gll.nthSym(Core.rhsOf(grammar, q), dot), x), gp, nt_to(grammar, q, dot, Some{Core.Nonterminal{x, need}}, x, ie, Lemma.nat_eq_refl(x))))
    case None{}:
      end_g(dot, grammar, input, q, k, i, s, h, gp, ie, hq, hd)

def desc_pick_at(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +ys: +List<Core.Bsr>,
  +hy: {Run.descGround(y, ys) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Run.descGround(x, ys) == True{} : Bool}) -> {Run.descGround(x, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Run.descGround(_, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law desc_at:
  for ds: +List<Gll.Desc>
  for +x: Gll.Desc
  for +ys: +List<Core.Bsr>
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.descsGrounded(ds, ys) == True{} : Bool}
  {Run.descGround(x, ys) == True{} : Bool}

def desc_at(ds, x, ys, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Run.descGround(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      desc_pick_at(x, y, rest, ys, Lemma.and_true_left(Run.descGround(y, ys), Run.descsGrounded(rest, ys), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => desc_at(rest, x, ys, m2, Lemma.and_true_right_side(Run.descGround(y, ys), Run.descsGrounded(rest, ys), h)))

# One iteration keeps everything resting on the steps.
law ground_step:
  for d: Gll.Desc
  for +rest: +List<Gll.Desc>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +seen: +List<Gll.Desc>
  for +cs: +List<Gll.CKey>
  for +rs: +List<Gll.Ret>
  for +ps: +List<Gll.Pop>
  for +ys: +List<Core.Bsr>
  for +h: {Run.groundOk(grammar, input, Gll.GState{seen, d <> rest, cs, rs, ps, ys}) == True{} : Bool}
  for +hin: {Gll.descIn(d, seen) == True{} : Bool}
  for +hb: {Run.descBound(d, grammar, input) == True{} : Bool}
  GStep(grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys}))

def ground_step(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h, hin, hb):
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      +A = {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) : Bool}
      +Bd = {Nat.is_le(dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
      +KI = {Bool.and(Nat.is_le(k, List.length(&2, Nat, input)), Nat.is_le(i, List.length(&2, Nat, input))) : Bool}
      +r1 = Lemma.and_true_right_side(A, Bool.and(Bd, KI), hb)
      +gp = desc_at(seen, Gll.Desc{q, dot, k, i}, ys, hin, Lemma.and_true_left(Run.descsGrounded(seen, ys), Bool.and(Run.retsGrounded(rs, grammar, ys), Run.popsGrounded(ps, grammar, ys)),
        Lemma.and_true_right_side(Run.stepsGrounded(ys, grammar, input), Bool.and(Run.descsGrounded(seen, ys), Bool.and(Run.retsGrounded(rs, grammar, ys), Run.popsGrounded(ps, grammar, ys))), h)))
      step_item_g(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, pred, q, dot, k, i, s0, h, gp, {==}, Lemma.and_true_left(A, Bool.and(Bd, KI), hb), Lemma.and_true_left(Bd, KI, r1))

def ground_first(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, p: GStep(grammar, input, s, t)) -> {Run.groundOk(grammar, input, t) == True{} : Bool}:
  match p:
    case (+g, w):
      g

# The engine's first state rests on its steps.
law initial_ground:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {Run.groundOk(grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool}

def initial_ground(pred, grammar, start, input):
  +s0 = {Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []} : Gll.GState}
  +seeds = Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n)
  ground_first(grammar, input, s0, Gll.withDescs(seeds, s0), with_descs_g(seeds, grammar, input, s0, {==}, seeds_zero(grammar, 0n, pred, Core.tokAt(input, 0n), start, 0n)))

