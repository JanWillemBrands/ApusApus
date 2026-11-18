import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C

# THE ENGINE ENDS CLOSED. Every iteration of the worklist loop keeps RUN.bend's invariant, so
# when nothing is left to do the state is closed (CHECK.bend).

# ======== EQUALITY ========

def key_eq_refl(c: Gll.CKey) -> {Gll.keyEq(c, c) == True{} : Bool}:
  match c:
    case Gll.CKey{+x, +i}:
      Lemma.and_true_intro(Nat.is_eq(x, x), Nat.is_eq(i, i), Lemma.nat_eq_refl(x), Lemma.nat_eq_refl(i))

def edge_eq_refl(e: Gll.Edge) -> {Check.edgeEq(e, e) == True{} : Bool}:
  match e:
    case Gll.Edge{+q, +dt, +k}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(dt, dt), Nat.is_eq(k, k)), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(dt, dt), Nat.is_eq(k, k), Lemma.nat_eq_refl(dt), Lemma.nat_eq_refl(k)))

# ======== MEMBERSHIP IN A LARGER LIST ========

law desc_trans:
  for xs: +List<Gll.Desc>
  for +ys: +List<Gll.Desc>
  for +zs: +List<Gll.Desc>
  for +h1: {Run.subDescs(xs, ys) == True{} : Bool}
  for +h2: {Run.subDescs(ys, zs) == True{} : Bool}
  {Run.subDescs(xs, zs) == True{} : Bool}

def desc_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, zs), Run.subDescs(rest, zs), C.desc_sub(ys, x, zs, Lemma.and_true_left(Gll.descIn(x, ys), Run.subDescs(rest, ys), h1), h2),
        desc_trans(rest, ys, zs, Lemma.and_true_right_side(Gll.descIn(x, ys), Run.subDescs(rest, ys), h1), h2))

def key_pick(+x: Gll.CKey, +y: Gll.CKey, +rest: +List<Gll.CKey>, +ys: +List<Gll.CKey>,
  +hy: {Gll.keyIn(y, ys) == True{} : Bool},
  cases: Either<{Gll.keyEq(x, y) == True{} : Bool}, {Gll.keyIn(x, rest) == True{} : Bool}>,
  later: {Gll.keyIn(x, rest) == True{} : Bool} -> {Gll.keyIn(x, ys) == True{} : Bool}) -> {Gll.keyIn(x, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.CKey, x, y, G.key_eq_sound(x, y, e)) : {Gll.keyIn(_, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law key_sub:
  for xs: +List<Gll.CKey>
  for +x: Gll.CKey
  for +ys: +List<Gll.CKey>
  for +m: {Gll.keyIn(x, xs) == True{} : Bool}
  for +h: {Run.subKeys(xs, ys) == True{} : Bool}
  {Gll.keyIn(x, ys) == True{} : Bool}

def key_sub(xs, x, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.keyIn(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      key_pick(x, y, rest, ys, Lemma.and_true_left(Gll.keyIn(y, ys), Run.subKeys(rest, ys), h), Lemma.or_true_cases(Gll.keyEq(x, y), Gll.keyIn(x, rest), m),
        m2 => key_sub(rest, x, ys, m2, Lemma.and_true_right_side(Gll.keyIn(y, ys), Run.subKeys(rest, ys), h)))

law key_weaken:
  for xs: +List<Gll.CKey>
  for +y: Gll.CKey
  for +ys: +List<Gll.CKey>
  for +h: {Run.subKeys(xs, ys) == True{} : Bool}
  {Run.subKeys(xs, y <> ys) == True{} : Bool}

def key_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.keyIn(x, y <> ys), Run.subKeys(rest, y <> ys),
        Lemma.or_true_right_intro(Gll.keyEq(x, y), Gll.keyIn(x, ys), Lemma.and_true_left(Gll.keyIn(x, ys), Run.subKeys(rest, ys), h)),
        key_weaken(rest, y, ys, Lemma.and_true_right_side(Gll.keyIn(x, ys), Run.subKeys(rest, ys), h)))

law key_refl:
  for xs: +List<Gll.CKey>
  {Run.subKeys(xs, xs) == True{} : Bool}

def key_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.keyIn(x, x <> rest), Run.subKeys(rest, x <> rest), Lemma.or_true_left_intro(Gll.keyEq(x, x), Gll.keyIn(x, rest), key_eq_refl(x)),
        key_weaken(rest, x, rest, key_refl(rest)))

law key_trans:
  for xs: +List<Gll.CKey>
  for +ys: +List<Gll.CKey>
  for +zs: +List<Gll.CKey>
  for +h1: {Run.subKeys(xs, ys) == True{} : Bool}
  for +h2: {Run.subKeys(ys, zs) == True{} : Bool}
  {Run.subKeys(xs, zs) == True{} : Bool}

def key_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.keyIn(x, zs), Run.subKeys(rest, zs), key_sub(ys, x, zs, Lemma.and_true_left(Gll.keyIn(x, ys), Run.subKeys(rest, ys), h1), h2),
        key_trans(rest, ys, zs, Lemma.and_true_right_side(Gll.keyIn(x, ys), Run.subKeys(rest, ys), h1), h2))

def step_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ys: +List<Core.Bsr>,
  +hy: {Core.member(y, ys) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, ys) == True{} : Bool}) -> {Core.member(x, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Core.member(_, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law step_sub:
  for xs: +List<Core.Bsr>
  for +x: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +m: {Core.member(x, xs) == True{} : Bool}
  for +h: {Core.allIn(xs, ys) == True{} : Bool}
  {Core.member(x, ys) == True{} : Bool}

def step_sub(xs, x, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Core.member(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      step_pick(x, y, rest, ys, Lemma.and_true_left(Core.member(y, ys), Core.allIn(rest, ys), h), Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        m2 => step_sub(rest, x, ys, m2, Lemma.and_true_right_side(Core.member(y, ys), Core.allIn(rest, ys), h)))

law step_trans:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +zs: +List<Core.Bsr>
  for +h1: {Core.allIn(xs, ys) == True{} : Bool}
  for +h2: {Core.allIn(ys, zs) == True{} : Bool}
  {Core.allIn(xs, zs) == True{} : Bool}

def step_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, zs), Core.allIn(rest, zs), step_sub(ys, x, zs, Lemma.and_true_left(Core.member(x, ys), Core.allIn(rest, ys), h1), h2),
        step_trans(rest, ys, zs, Lemma.and_true_right_side(Core.member(x, ys), Core.allIn(rest, ys), h1), h2))

def ret_pick(+a: Gll.CKey, +b: Gll.Edge, +a2: Gll.CKey, +b2: Gll.Edge, +rest: +List<Gll.Ret>, +ys: +List<Gll.Ret>,
  +hy: {Check.retIn(a2, b2, ys) == True{} : Bool},
  cases: Either<{Bool.and(Gll.keyEq(a, a2), Check.edgeEq(b, b2)) == True{} : Bool}, {Check.retIn(a, b, rest) == True{} : Bool}>,
  later: {Check.retIn(a, b, rest) == True{} : Bool} -> {Check.retIn(a, b, ys) == True{} : Bool}) -> {Check.retIn(a, b, ys) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +ea = G.key_eq_sound(a, a2, Lemma.and_true_left(Gll.keyEq(a, a2), Check.edgeEq(b, b2), e))
      +eb = G.edge_eq_sound(b, b2, Lemma.and_true_right_side(Gll.keyEq(a, a2), Check.edgeEq(b, b2), e))
      %Equal.sym(Gll.CKey, a, a2, ea) : {Check.retIn(_, b, ys) == True{} : Bool}
      %Equal.sym(Gll.Edge, b, b2, eb) : {Check.retIn(a2, _, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law ret_sub:
  for xs: +List<Gll.Ret>
  for +a: Gll.CKey
  for +b: Gll.Edge
  for +ys: +List<Gll.Ret>
  for +m: {Check.retIn(a, b, xs) == True{} : Bool}
  for +h: {Run.subRets(xs, ys) == True{} : Bool}
  {Check.retIn(a, b, ys) == True{} : Bool}

def ret_sub(xs, a, b, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Check.retIn(a, b, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Ret{+a2, +b2}, +rest}:
      ret_pick(a, b, a2, b2, rest, ys, Lemma.and_true_left(Check.retIn(a2, b2, ys), Run.subRets(rest, ys), h), Lemma.or_true_cases(Bool.and(Gll.keyEq(a, a2), Check.edgeEq(b, b2)), Check.retIn(a, b, rest), m),
        m2 => ret_sub(rest, a, b, ys, m2, Lemma.and_true_right_side(Check.retIn(a2, b2, ys), Run.subRets(rest, ys), h)))

law ret_weaken:
  for xs: +List<Gll.Ret>
  for +a: Gll.CKey
  for +b: Gll.Edge
  for +ys: +List<Gll.Ret>
  for +h: {Run.subRets(xs, ys) == True{} : Bool}
  {Run.subRets(xs, Gll.Ret{a, b} <> ys) == True{} : Bool}

def ret_weaken(xs, a, b, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+a2, +b2}, +rest}:
      Lemma.and_true_intro(Check.retIn(a2, b2, Gll.Ret{a, b} <> ys), Run.subRets(rest, Gll.Ret{a, b} <> ys),
        Lemma.or_true_right_intro(Bool.and(Gll.keyEq(a2, a), Check.edgeEq(b2, b)), Check.retIn(a2, b2, ys), Lemma.and_true_left(Check.retIn(a2, b2, ys), Run.subRets(rest, ys), h)),
        ret_weaken(rest, a, b, ys, Lemma.and_true_right_side(Check.retIn(a2, b2, ys), Run.subRets(rest, ys), h)))

law ret_refl:
  for xs: +List<Gll.Ret>
  {Run.subRets(xs, xs) == True{} : Bool}

def ret_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+a, +b}, +rest}:
      Lemma.and_true_intro(Check.retIn(a, b, Gll.Ret{a, b} <> rest), Run.subRets(rest, Gll.Ret{a, b} <> rest),
        Lemma.or_true_left_intro(Bool.and(Gll.keyEq(a, a), Check.edgeEq(b, b)), Check.retIn(a, b, rest), Lemma.and_true_intro(Gll.keyEq(a, a), Check.edgeEq(b, b), key_eq_refl(a), edge_eq_refl(b))),
        ret_weaken(rest, a, b, rest, ret_refl(rest)))

law ret_trans:
  for xs: +List<Gll.Ret>
  for +ys: +List<Gll.Ret>
  for +zs: +List<Gll.Ret>
  for +h1: {Run.subRets(xs, ys) == True{} : Bool}
  for +h2: {Run.subRets(ys, zs) == True{} : Bool}
  {Run.subRets(xs, zs) == True{} : Bool}

def ret_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+a, +b}, +rest}:
      Lemma.and_true_intro(Check.retIn(a, b, zs), Run.subRets(rest, zs), ret_sub(ys, a, b, zs, Lemma.and_true_left(Check.retIn(a, b, ys), Run.subRets(rest, ys), h1), h2),
        ret_trans(rest, ys, zs, Lemma.and_true_right_side(Check.retIn(a, b, ys), Run.subRets(rest, ys), h1), h2))

def pop_pick(+a: Gll.CKey, +b: Nat, +a2: Gll.CKey, +b2: Nat, +rest: +List<Gll.Pop>, +ys: +List<Gll.Pop>,
  +hy: {Gll.popIn(a2, b2, ys) == True{} : Bool},
  cases: Either<{Bool.and(Gll.keyEq(a, a2), Nat.is_eq(b, b2)) == True{} : Bool}, {Gll.popIn(a, b, rest) == True{} : Bool}>,
  later: {Gll.popIn(a, b, rest) == True{} : Bool} -> {Gll.popIn(a, b, ys) == True{} : Bool}) -> {Gll.popIn(a, b, ys) == True{} : Bool}:
  match cases:
    case Inl{+e}:
      +ea = G.key_eq_sound(a, a2, Lemma.and_true_left(Gll.keyEq(a, a2), Nat.is_eq(b, b2), e))
      +eb = Lemma.nat_eq_sound(b, b2, Lemma.and_true_right_side(Gll.keyEq(a, a2), Nat.is_eq(b, b2), e))
      %Equal.sym(Gll.CKey, a, a2, ea) : {Gll.popIn(_, b, ys) == True{} : Bool}
      %Equal.sym(Nat, b, b2, eb) : {Gll.popIn(a2, _, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law pop_sub:
  for xs: +List<Gll.Pop>
  for +a: Gll.CKey
  for +b: Nat
  for +ys: +List<Gll.Pop>
  for +m: {Gll.popIn(a, b, xs) == True{} : Bool}
  for +h: {Run.subPops(xs, ys) == True{} : Bool}
  {Gll.popIn(a, b, ys) == True{} : Bool}

def pop_sub(xs, a, b, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.popIn(a, b, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Gll.Pop{+a2, +b2}, +rest}:
      pop_pick(a, b, a2, b2, rest, ys, Lemma.and_true_left(Gll.popIn(a2, b2, ys), Run.subPops(rest, ys), h), Lemma.or_true_cases(Bool.and(Gll.keyEq(a, a2), Nat.is_eq(b, b2)), Gll.popIn(a, b, rest), m),
        m2 => pop_sub(rest, a, b, ys, m2, Lemma.and_true_right_side(Gll.popIn(a2, b2, ys), Run.subPops(rest, ys), h)))

law pop_weaken:
  for xs: +List<Gll.Pop>
  for +a: Gll.CKey
  for +b: Nat
  for +ys: +List<Gll.Pop>
  for +h: {Run.subPops(xs, ys) == True{} : Bool}
  {Run.subPops(xs, Gll.Pop{a, b} <> ys) == True{} : Bool}

def pop_weaken(xs, a, b, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Pop{+a2, +b2}, +rest}:
      Lemma.and_true_intro(Gll.popIn(a2, b2, Gll.Pop{a, b} <> ys), Run.subPops(rest, Gll.Pop{a, b} <> ys),
        Lemma.or_true_right_intro(Bool.and(Gll.keyEq(a2, a), Nat.is_eq(b2, b)), Gll.popIn(a2, b2, ys), Lemma.and_true_left(Gll.popIn(a2, b2, ys), Run.subPops(rest, ys), h)),
        pop_weaken(rest, a, b, ys, Lemma.and_true_right_side(Gll.popIn(a2, b2, ys), Run.subPops(rest, ys), h)))

law pop_refl:
  for xs: +List<Gll.Pop>
  {Run.subPops(xs, xs) == True{} : Bool}

def pop_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Pop{+a, +b}, +rest}:
      Lemma.and_true_intro(Gll.popIn(a, b, Gll.Pop{a, b} <> rest), Run.subPops(rest, Gll.Pop{a, b} <> rest),
        Lemma.or_true_left_intro(Bool.and(Gll.keyEq(a, a), Nat.is_eq(b, b)), Gll.popIn(a, b, rest), Lemma.and_true_intro(Gll.keyEq(a, a), Nat.is_eq(b, b), key_eq_refl(a), Lemma.nat_eq_refl(b))),
        pop_weaken(rest, a, b, rest, pop_refl(rest)))

law pop_trans:
  for xs: +List<Gll.Pop>
  for +ys: +List<Gll.Pop>
  for +zs: +List<Gll.Pop>
  for +h1: {Run.subPops(xs, ys) == True{} : Bool}
  for +h2: {Run.subPops(ys, zs) == True{} : Bool}
  {Run.subPops(xs, zs) == True{} : Bool}

def pop_trans(xs, ys, zs, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case Con{Gll.Pop{+a, +b}, +rest}:
      Lemma.and_true_intro(Gll.popIn(a, b, zs), Run.subPops(rest, zs), pop_sub(ys, a, b, zs, Lemma.and_true_left(Gll.popIn(a, b, ys), Run.subPops(rest, ys), h1), h2),
        pop_trans(rest, ys, zs, Lemma.and_true_right_side(Gll.popIn(a, b, ys), Run.subPops(rest, ys), h1), h2))

# ======== GROWTH OF STATES ========

law grows_refl:
  for s: Gll.GState
  {Run.grows(s, s) == True{} : Bool}

def grows_refl(s):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      Lemma.and_true_intro(Run.subDescs(seen, seen), Bool.and(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys)))), C.desc_refl(seen),
        Lemma.and_true_intro(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys))), key_refl(cs),
          Lemma.and_true_intro(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys)), ret_refl(rs),
            Lemma.and_true_intro(Run.subPops(ps, ps), Core.allIn(ys, ys), pop_refl(ps), C.step_refl(ys)))))

law grows_trans:
  for s: Gll.GState
  for t: Gll.GState
  for u: Gll.GState
  for +g1: {Run.grows(s, t) == True{} : Bool}
  for +g2: {Run.grows(t, u) == True{} : Bool}
  {Run.grows(s, u) == True{} : Bool}

def grows_trans(s, t, u, g1, g2):
  match s t u:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2} Gll.GState{+seen3, +todo3, +cs3, +rs3, +ps3, +ys3}:
      Lemma.and_true_intro(Run.subDescs(seen1, seen3), Bool.and(Run.subKeys(cs1, cs3), Bool.and(Run.subRets(rs1, rs3), Bool.and(Run.subPops(ps1, ps3), Core.allIn(ys1, ys3)))), desc_trans(seen1, seen2, seen3, Lemma.and_true_left(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g1), Lemma.and_true_left(Run.subDescs(seen2, seen3), Bool.and(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)))), g2)),
        Lemma.and_true_intro(Run.subKeys(cs1, cs3), Bool.and(Run.subRets(rs1, rs3), Bool.and(Run.subPops(ps1, ps3), Core.allIn(ys1, ys3))), key_trans(cs1, cs2, cs3, Lemma.and_true_left(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g1)), Lemma.and_true_left(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3))), Lemma.and_true_right_side(Run.subDescs(seen2, seen3), Bool.and(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)))), g2))),
          Lemma.and_true_intro(Run.subRets(rs1, rs3), Bool.and(Run.subPops(ps1, ps3), Core.allIn(ys1, ys3)), ret_trans(rs1, rs2, rs3, Lemma.and_true_left(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g1))), Lemma.and_true_left(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)), Lemma.and_true_right_side(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3))), Lemma.and_true_right_side(Run.subDescs(seen2, seen3), Bool.and(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)))), g2)))),
            Lemma.and_true_intro(Run.subPops(ps1, ps3), Core.allIn(ys1, ys3), pop_trans(ps1, ps2, ps3, Lemma.and_true_left(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2), Lemma.and_true_right_side(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g1)))), Lemma.and_true_left(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3), Lemma.and_true_right_side(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)), Lemma.and_true_right_side(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3))), Lemma.and_true_right_side(Run.subDescs(seen2, seen3), Bool.and(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)))), g2))))),
              step_trans(ys1, ys2, ys3, Lemma.and_true_right_side(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2), Lemma.and_true_right_side(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g1)))), Lemma.and_true_right_side(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3), Lemma.and_true_right_side(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)), Lemma.and_true_right_side(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3))), Lemma.and_true_right_side(Run.subDescs(seen2, seen3), Bool.and(Run.subKeys(cs2, cs3), Bool.and(Run.subRets(rs2, rs3), Bool.and(Run.subPops(ps2, ps3), Core.allIn(ys2, ys3)))), g2)))))))))

law seen_grow:
  for s: Gll.GState
  for t: Gll.GState
  for +d: Gll.Desc
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +m: {Check.seenIn(d, s) == True{} : Bool}
  {Check.seenIn(d, t) == True{} : Bool}

def seen_grow(s, t, d, g, m):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      C.desc_sub(seen1, d, seen2, m, Lemma.and_true_left(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g))

law key_grow:
  for s: Gll.GState
  for t: Gll.GState
  for +c: Gll.CKey
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +m: {Gll.keyIn(c, Check.clustersOf(s)) == True{} : Bool}
  {Gll.keyIn(c, Check.clustersOf(t)) == True{} : Bool}

def key_grow(s, t, c, g, m):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      key_sub(cs1, c, cs2, m, Lemma.and_true_left(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g)))

law ret_grow:
  for s: Gll.GState
  for t: Gll.GState
  for +a: Gll.CKey
  for +b: Gll.Edge
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +m: {Check.retIn(a, b, Check.returnsOf(s)) == True{} : Bool}
  {Check.retIn(a, b, Check.returnsOf(t)) == True{} : Bool}

def ret_grow(s, t, a, b, g, m):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      ret_sub(rs1, a, b, rs2, m, Lemma.and_true_left(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g))))

law pop_grow:
  for s: Gll.GState
  for t: Gll.GState
  for +a: Gll.CKey
  for +b: Nat
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +m: {Gll.popIn(a, b, Check.popsOf(s)) == True{} : Bool}
  {Gll.popIn(a, b, Check.popsOf(t)) == True{} : Bool}

def pop_grow(s, t, a, b, g, m):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      pop_sub(ps1, a, b, ps2, m, Lemma.and_true_left(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2), Lemma.and_true_right_side(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g)))))

law step_grow:
  for s: Gll.GState
  for t: Gll.GState
  for +y: Core.Bsr
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +m: {Check.stepIn(y, s) == True{} : Bool}
  {Check.stepIn(y, t) == True{} : Bool}

def step_grow(s, t, y, g, m):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      step_sub(ys1, y, ys2, m, Lemma.and_true_right_side(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2), Lemma.and_true_right_side(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)), Lemma.and_true_right_side(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2))), Lemma.and_true_right_side(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g)))))

# ======== THE CHECKS ONLY GROW TRUER ========

def token_grow(b: Bool, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +t: Gll.GState, +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.tokenOk(b, q, d, k, i, s) == True{} : Bool}) -> {Check.tokenOk(b, q, d, k, i, t) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+d, k, 1n+i}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+d, k, i, 1n+i}, s) : Bool}
      Lemma.and_true_intro(Check.seenIn(Gll.Desc{q, 1n+d, k, 1n+i}, t), Check.stepIn(Core.Bsr{q, 1n+d, k, i, 1n+i}, t),
        seen_grow(s, t, Gll.Desc{q, 1n+d, k, 1n+i}, g, Lemma.and_true_left(sd, sy, h)),
        step_grow(s, t, Core.Bsr{q, 1n+d, k, i, 1n+i}, g, Lemma.and_true_right_side(sd, sy, h)))
    case False{}:
      {==}

def empty_grow(dot: Nat, +q: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +t: Gll.GState, +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.emptyOk(dot, q, k, i, s) == True{} : Bool}) -> {Check.emptyOk(dot, q, k, i, t) == True{} : Bool}:
  match dot:
    case 0n:
      step_grow(s, t, Core.Bsr{q, 0n, k, i, i}, g, h)
    case 1n+(+e):
      {==}

def item_grow(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +t: Gll.GState,
  +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.itemOk(item, grammar, input, q, d, k, i, s) == True{} : Bool}) -> {Check.itemOk(item, grammar, input, q, d, k, i, t) == True{} : Bool}:
  match item:
    case Some{Core.Terminal{+tk}}:
      token_grow(Core.tokIs(Core.tokAt(input, i), tk), q, d, k, i, s, t, g, h)
    case Some{Core.Nonterminal{+x, +need}}:
      +kc = {Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(s)) : Bool}
      +kr = {Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, d, k}, Check.returnsOf(s)) : Bool}
      Lemma.and_true_intro(Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(t)), Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, d, k}, Check.returnsOf(t)),
        key_grow(s, t, Gll.CKey{x, i}, g, Lemma.and_true_left(kc, kr, h)),
        ret_grow(s, t, Gll.CKey{x, i}, Gll.Edge{q, d, k}, g, Lemma.and_true_right_side(kc, kr, h)))
    case None{}:
      +em = {Check.emptyOk(d, q, k, i, s) : Bool}
      +po = {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(s)) : Bool}
      Lemma.and_true_intro(Check.emptyOk(d, q, k, i, t), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(t)),
        empty_grow(d, q, k, i, s, t, g, Lemma.and_true_left(em, po, h)),
        pop_grow(s, t, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, g, Lemma.and_true_right_side(em, po, h)))

law desc_ok_grow:
  for dd: Gll.Desc
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +h: {Check.descOk(dd, grammar, input, s) == True{} : Bool}
  {Check.descOk(dd, grammar, input, t) == True{} : Bool}

def desc_ok_grow(dd, grammar, input, s, t, g, h):
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      item_grow(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, q, d, k, i, s, t, g, h)

law seen_all_grow:
  for ds: +List<Gll.Desc>
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +h: {Check.allSeen(ds, s) == True{} : Bool}
  {Check.allSeen(ds, t) == True{} : Bool}

def seen_all_grow(ds, s, t, g, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      Lemma.and_true_intro(Check.seenIn(d, t), Check.allSeen(rest, t), seen_grow(s, t, d, g, Lemma.and_true_left(Check.seenIn(d, s), Check.allSeen(rest, s), h)),
        seen_all_grow(rest, s, t, g, Lemma.and_true_right_side(Check.seenIn(d, s), Check.allSeen(rest, s), h)))

law clusters_grow:
  for cs: +List<Gll.CKey>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +h: {Check.allClusters(cs, pred, grammar, input, s) == True{} : Bool}
  {Check.allClusters(cs, pred, grammar, input, t) == True{} : Bool}

def clusters_grow(cs, pred, grammar, input, s, t, g, h):
  match cs:
    case Nil{}:
      {==}
    case Con{Gll.CKey{+x, +i}, +rest}:
      +sd = Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i)
      Lemma.and_true_intro(Check.allSeen(sd, t), Check.allClusters(rest, pred, grammar, input, t),
        seen_all_grow(sd, s, t, g, Lemma.and_true_left(Check.allSeen(sd, s), Check.allClusters(rest, pred, grammar, input, s), h)),
        clusters_grow(rest, pred, grammar, input, s, t, g, Lemma.and_true_right_side(Check.allSeen(sd, s), Check.allClusters(rest, pred, grammar, input, s), h)))

def resume_ok_grow(b: Bool, +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +t: Gll.GState, +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.resumeOk(b, q, d, k, kc, j, s) == True{} : Bool}) -> {Check.resumeOk(b, q, d, k, kc, j, t) == True{} : Bool}:
  match b:
    case True{}:
      +sd = {Check.seenIn(Gll.Desc{q, 1n+d, k, j}, s) : Bool}
      +sy = {Check.stepIn(Core.Bsr{q, 1n+d, k, kc, j}, s) : Bool}
      Lemma.and_true_intro(Check.seenIn(Gll.Desc{q, 1n+d, k, j}, t), Check.stepIn(Core.Bsr{q, 1n+d, k, kc, j}, t),
        seen_grow(s, t, Gll.Desc{q, 1n+d, k, j}, g, Lemma.and_true_left(sd, sy, h)),
        step_grow(s, t, Core.Bsr{q, 1n+d, k, kc, j}, g, Lemma.and_true_right_side(sd, sy, h)))
    case False{}:
      {==}

def edge_ok_grow(edge: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +kc: Nat, +j: Nat, +s: Gll.GState, +t: Gll.GState, +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.edgeOk(edge, grammar, kc, j, s) == True{} : Bool}) -> {Check.edgeOk(edge, grammar, kc, j, t) == True{} : Bool}:
  match edge:
    case Gll.Edge{+q, +d, +k}:
      resume_ok_grow(Gll.needHolds(Gll.needAt(grammar, q, d), kc, j), q, d, k, kc, j, s, t, g, h)

def hit_grow(hit: Bool, +edge: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +kc: Nat, +j: Nat, +s: Gll.GState, +t: Gll.GState, +g: {Run.grows(s, t) == True{} : Bool},
  +h: {Check.hitOk(hit, edge, grammar, kc, j, s) == True{} : Bool}) -> {Check.hitOk(hit, edge, grammar, kc, j, t) == True{} : Bool}:
  match hit:
    case True{}:
      edge_ok_grow(edge, grammar, input, kc, j, s, t, g, h)
    case False{}:
      {==}

law edge_pops_grow:
  for pops: +List<Gll.Pop>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +edge: Gll.Edge
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +h: {Check.edgePops(pops, grammar, key, edge, s) == True{} : Bool}
  {Check.edgePops(pops, grammar, key, edge, t) == True{} : Bool}

def edge_pops_grow(pops, grammar, input, key, edge, s, t, g, h):
  match pops key:
    case Nil{} +key0:
      {==}
    case Con{Gll.Pop{+k2, +j}, +rest} Gll.CKey{+x, +kc}:
      +hs = {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, s) : Bool}
      +more = {Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, s) : Bool}
      Lemma.and_true_intro(Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, t), Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, t),
        hit_grow(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, input, kc, j, s, t, g, Lemma.and_true_left(hs, more, h)),
        edge_pops_grow(rest, grammar, input, Gll.CKey{x, kc}, edge, s, t, g, Lemma.and_true_right_side(hs, more, h)))

law returns_grow:
  for rs: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +pops: +List<Gll.Pop>
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +h: {Check.allReturns(rs, grammar, pops, s) == True{} : Bool}
  {Check.allReturns(rs, grammar, pops, t) == True{} : Bool}

def returns_grow(rs, grammar, input, pops, s, t, g, h):
  match rs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+key, +edge}, +rest}:
      +ep = {Check.edgePops(pops, grammar, key, edge, s) : Bool}
      +more = {Check.allReturns(rest, grammar, pops, s) : Bool}
      Lemma.and_true_intro(Check.edgePops(pops, grammar, key, edge, t), Check.allReturns(rest, grammar, pops, t),
        edge_pops_grow(pops, grammar, input, key, edge, s, t, g, Lemma.and_true_left(ep, more, h)),
        returns_grow(rest, grammar, input, pops, s, t, g, Lemma.and_true_right_side(ep, more, h)))

law queued_grow:
  for ds: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +todo2: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  for +st: {Run.subDescs(todo, todo2) == True{} : Bool}
  for +h: {Run.queuedOk(ds, todo, grammar, input, s) == True{} : Bool}
  {Run.queuedOk(ds, todo2, grammar, input, t) == True{} : Bool}

def queued_pick(+d: Gll.Desc, +todo: +List<Gll.Desc>, +todo2: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState,
  +g: {Run.grows(s, t) == True{} : Bool}, +st: {Run.subDescs(todo, todo2) == True{} : Bool},
  cases: Either<{Gll.descIn(d, todo) == True{} : Bool}, {Check.descOk(d, grammar, input, s) == True{} : Bool}>)
  -> {Bool.or(Gll.descIn(d, todo2), Check.descOk(d, grammar, input, t)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      Lemma.or_true_left_intro(Gll.descIn(d, todo2), Check.descOk(d, grammar, input, t), C.desc_sub(todo, d, todo2, m, st))
    case Inr{h}:
      Lemma.or_true_right_intro(Gll.descIn(d, todo2), Check.descOk(d, grammar, input, t), desc_ok_grow(d, grammar, input, s, t, g, h))

def queued_grow(ds, todo, todo2, grammar, input, s, t, g, st, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +here = {Bool.or(Gll.descIn(d, todo), Check.descOk(d, grammar, input, s)) : Bool}
      +more = {Run.queuedOk(rest, todo, grammar, input, s) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(d, todo2), Check.descOk(d, grammar, input, t)), Run.queuedOk(rest, todo2, grammar, input, t),
        queued_pick(d, todo, todo2, grammar, input, s, t, g, st, Lemma.or_true_cases(Gll.descIn(d, todo), Check.descOk(d, grammar, input, s), Lemma.and_true_left(here, more, h))),
        queued_grow(rest, todo, todo2, grammar, input, s, t, g, st, Lemma.and_true_right_side(here, more, h)))

law pops_keyed_grow:
  for ps: +List<Gll.Pop>
  for +cs: +List<Gll.CKey>
  for +cs2: +List<Gll.CKey>
  for +sk: {Run.subKeys(cs, cs2) == True{} : Bool}
  for +h: {Run.popsKeyed(ps, cs) == True{} : Bool}
  {Run.popsKeyed(ps, cs2) == True{} : Bool}

def pops_keyed_grow(ps, cs, cs2, sk, h):
  match ps:
    case Nil{}:
      {==}
    case Con{Gll.Pop{+key, +j}, +rest}:
      Lemma.and_true_intro(Gll.keyIn(key, cs2), Run.popsKeyed(rest, cs2), key_sub(cs, key, cs2, Lemma.and_true_left(Gll.keyIn(key, cs), Run.popsKeyed(rest, cs), h), sk),
        pops_keyed_grow(rest, cs, cs2, sk, Lemma.and_true_right_side(Gll.keyIn(key, cs), Run.popsKeyed(rest, cs), h)))

law descs_keyed_grow:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +cs2: +List<Gll.CKey>
  for +sk: {Run.subKeys(cs, cs2) == True{} : Bool}
  for +h: {Run.descsKeyed(ds, grammar, cs) == True{} : Bool}
  {Run.descsKeyed(ds, grammar, cs2) == True{} : Bool}

def descs_keyed_grow(ds, grammar, input, cs, cs2, sk, h):
  match ds:
    case Nil{}:
      {==}
    case Con{Gll.Desc{+q, +d, +k, +i}, +rest}:
      +key = {Gll.CKey{Gll.lhsOf(grammar, q), k} : Gll.CKey}
      Lemma.and_true_intro(Gll.keyIn(key, cs2), Run.descsKeyed(rest, grammar, cs2), key_sub(cs, key, cs2, Lemma.and_true_left(Gll.keyIn(key, cs), Run.descsKeyed(rest, grammar, cs), h), sk),
        descs_keyed_grow(rest, grammar, input, cs, cs2, sk, Lemma.and_true_right_side(Gll.keyIn(key, cs), Run.descsKeyed(rest, grammar, cs), h)))

law rets_keyed_grow:
  for rs: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +cs2: +List<Gll.CKey>
  for +sk: {Run.subKeys(cs, cs2) == True{} : Bool}
  for +h: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool}
  {Run.retsKeyed(rs, grammar, cs2) == True{} : Bool}

def rets_keyed_grow(rs, grammar, input, cs, cs2, sk, h):
  match rs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{+key0, Gll.Edge{+q, +d, +k}}, +rest}:
      +key = {Gll.CKey{Gll.lhsOf(grammar, q), k} : Gll.CKey}
      Lemma.and_true_intro(Gll.keyIn(key, cs2), Run.retsKeyed(rest, grammar, cs2), key_sub(cs, key, cs2, Lemma.and_true_left(Gll.keyIn(key, cs), Run.retsKeyed(rest, grammar, cs), h), sk),
        rets_keyed_grow(rest, grammar, input, cs, cs2, sk, Lemma.and_true_right_side(Gll.keyIn(key, cs), Run.retsKeyed(rest, grammar, cs), h)))

# ======== ADDING OPERATIONS ========

def Adds(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState) -> Type:
  {Run.addsB(grammar, input, s, t) == True{} : Bool} & {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>} &
  {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>} & {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>}

# Elements of the lists the conditions range over.
def nq_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +old: +List<Gll.Desc>, +todo: +List<Gll.Desc>,
  +hy: {Bool.or(Gll.descIn(y, old), Gll.descIn(y, todo)) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) == True{} : Bool})
  -> {Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Bool.or(Gll.descIn(_, old), Gll.descIn(_, todo)) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law nq_at:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.newQueued(ds, old, todo) == True{} : Bool}
  {Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) == True{} : Bool}

def nq_at(ds, old, todo, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Bool.or(Gll.descIn(y, old), Gll.descIn(y, todo)) : Bool}
      nq_pick(x, y, rest, old, todo, Lemma.and_true_left(hy, Run.newQueued(rest, old, todo), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => nq_at(rest, old, todo, x, m2, Lemma.and_true_right_side(hy, Run.newQueued(rest, old, todo), h)))

def nk_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +hy: {Bool.or(Gll.descIn(y, old), Run.keyedDesc(y, grammar, cs)) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)) == True{} : Bool})
  -> {Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Bool.or(Gll.descIn(_, old), Run.keyedDesc(_, grammar, cs)) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law nk_at:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.newKeyed(ds, old, grammar, cs) == True{} : Bool}
  {Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)) == True{} : Bool}

def nk_at(ds, old, grammar, input, cs, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Bool.or(Gll.descIn(y, old), Run.keyedDesc(y, grammar, cs)) : Bool}
      nk_pick(x, y, rest, old, grammar, input, cs, Lemma.and_true_left(hy, Run.newKeyed(rest, old, grammar, cs), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => nk_at(rest, old, grammar, input, cs, x, m2, Lemma.and_true_right_side(hy, Run.newKeyed(rest, old, grammar, cs), h)))

def qd_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState,
  +hy: {Bool.or(Gll.descIn(y, todo), Check.descOk(y, grammar, input, s)) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, s)) == True{} : Bool})
  -> {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, s)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Bool.or(Gll.descIn(_, todo), Check.descOk(_, grammar, input, s)) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law queued_at:
  for ds: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.queuedOk(ds, todo, grammar, input, s) == True{} : Bool}
  {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, s)) == True{} : Bool}

def queued_at(ds, todo, grammar, input, s, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, s)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Bool.or(Gll.descIn(y, todo), Check.descOk(y, grammar, input, s)) : Bool}
      qd_pick(x, y, rest, todo, grammar, input, s, Lemma.and_true_left(hy, Run.queuedOk(rest, todo, grammar, input, s), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => queued_at(rest, todo, grammar, input, s, x, m2, Lemma.and_true_right_side(hy, Run.queuedOk(rest, todo, grammar, input, s), h)))

def kd_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +hy: {Run.keyedDesc(y, grammar, cs) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Run.keyedDesc(x, grammar, cs) == True{} : Bool}) -> {Run.keyedDesc(x, grammar, cs) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Run.keyedDesc(_, grammar, cs) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

def keyed_head(y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +h: {Run.descsKeyed(y <> rest, grammar, cs) == True{} : Bool}) -> {Run.keyedDesc(y, grammar, cs) == True{} : Bool}:
  match y:
    case Gll.Desc{+q, +d, +k, +i}:
      Lemma.and_true_left(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.descsKeyed(rest, grammar, cs), h)

def keyed_tail(y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +h: {Run.descsKeyed(y <> rest, grammar, cs) == True{} : Bool}) -> {Run.descsKeyed(rest, grammar, cs) == True{} : Bool}:
  match y:
    case Gll.Desc{+q, +d, +k, +i}:
      Lemma.and_true_right_side(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.descsKeyed(rest, grammar, cs), h)

law keyed_at:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.descsKeyed(ds, grammar, cs) == True{} : Bool}
  {Run.keyedDesc(x, grammar, cs) == True{} : Bool}

def keyed_at(ds, grammar, input, cs, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Run.keyedDesc(x, grammar, cs) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      kd_pick(x, y, rest, grammar, input, cs, keyed_head(y, rest, grammar, input, cs, h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => keyed_at(rest, grammar, input, cs, x, m2, keyed_tail(y, rest, grammar, input, cs, h)))

def keyed_cons(y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +hy: {Run.keyedDesc(y, grammar, cs) == True{} : Bool}, +hr: {Run.descsKeyed(rest, grammar, cs) == True{} : Bool}) -> {Run.descsKeyed(y <> rest, grammar, cs) == True{} : Bool}:
  match y:
    case Gll.Desc{+q, +d, +k, +i}:
      Lemma.and_true_intro(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.descsKeyed(rest, grammar, cs), hy, hr)

# ======== THE INVARIANT, PART BY PART ========

# ======== BOUNDS ========

def bd_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hy: {Run.descBound(y, grammar, input) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Run.descBound(x, grammar, input) == True{} : Bool}) -> {Run.descBound(x, grammar, input) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Run.descBound(_, grammar, input) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law bounded_at:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.descsBounded(ds, grammar, input) == True{} : Bool}
  {Run.descBound(x, grammar, input) == True{} : Bool}

def bounded_at(ds, grammar, input, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Run.descBound(x, grammar, input) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      bd_pick(x, y, rest, grammar, input, Lemma.and_true_left(Run.descBound(y, grammar, input), Run.descsBounded(rest, grammar, input), h),
        Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => bounded_at(rest, grammar, input, x, m2, Lemma.and_true_right_side(Run.descBound(y, grammar, input), Run.descsBounded(rest, grammar, input), h)))

def bn_step(+x: Gll.Desc, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +ho: {Run.descsBounded(old, grammar, input) == True{} : Bool},
  cases: Either<{Gll.descIn(x, old) == True{} : Bool}, {Run.descBound(x, grammar, input) == True{} : Bool}>) -> {Run.descBound(x, grammar, input) == True{} : Bool}:
  match cases:
    case Inl{m}:
      bounded_at(old, grammar, input, x, m, ho)
    case Inr{b}:
      b

law bounded_new:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +nb: {Run.newBounded(ds, old, grammar, input) == True{} : Bool}
  for +ho: {Run.descsBounded(old, grammar, input) == True{} : Bool}
  {Run.descsBounded(ds, grammar, input) == True{} : Bool}

def bounded_new(ds, old, grammar, input, nb, ho):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)) : Bool}
      Lemma.and_true_intro(Run.descBound(x, grammar, input), Run.descsBounded(rest, grammar, input),
        bn_step(x, old, grammar, input, ho, Lemma.or_true_cases(Gll.descIn(x, old), Run.descBound(x, grammar, input), Lemma.and_true_left(hx, Run.newBounded(rest, old, grammar, input), nb))),
        bounded_new(rest, old, grammar, input, Lemma.and_true_right_side(hx, Run.newBounded(rest, old, grammar, input), nb), ho))

def rets_bounded_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<Gll.Ret>, +b: +List<Gll.Ret>, +e: {a == b : +List<Gll.Ret>},
  +h: {Run.retsBounded(b, grammar, input) == True{} : Bool}) -> {Run.retsBounded(a, grammar, input) == True{} : Bool}:
  %Equal.sym(+List<Gll.Ret>, a, b, e) : {Run.retsBounded(_, grammar, input) == True{} : Bool}
  h

def pops_bounded_to(+input: +List<Nat>, +a: +List<Gll.Pop>, +b: +List<Gll.Pop>, +e: {a == b : +List<Gll.Pop>},
  +h: {Run.popsBounded(b, input) == True{} : Bool}) -> {Run.popsBounded(a, input) == True{} : Bool}:
  %Equal.sym(+List<Gll.Pop>, a, b, e) : {Run.popsBounded(_, input) == True{} : Bool}
  h

def Inv6(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Type:
  {Run.queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), grammar, input, s) == True{} : Bool} &
  {Check.allClusters(Check.clustersOf(s), pred, grammar, input, s) == True{} : Bool} &
  {Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s) == True{} : Bool} &
  {Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)) == True{} : Bool} &
  {Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool} &
  {Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)) == True{} : Bool} &
  {Run.subDescs(Run.todoOf(s), Check.seenOf(s)) == True{} : Bool} &
  {Run.descsBounded(Check.seenOf(s), grammar, input) == True{} : Bool} &
  {Run.retsBounded(Check.returnsOf(s), grammar, input) == True{} : Bool} &
  {Run.popsBounded(Check.popsOf(s), input) == True{} : Bool} &
  {Run.stepsBounded(Check.stepsOf(s), grammar, input) == True{} : Bool}

def inv_split(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState,
  +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}) -> Inv6(extra, pred, grammar, input, s):
  +r1 = Lemma.and_true_right_side(Run.queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))))), h)
  +r2 = Lemma.and_true_right_side(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))))), r1)
  +r3 = Lemma.and_true_right_side(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))), r2)
  +r4 = Lemma.and_true_right_side(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))), r3)
  +r5 = Lemma.and_true_right_side(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))), r4)
  +r6 = Lemma.and_true_right_side(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))), r5)
  +r7 = Lemma.and_true_right_side(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))), r6)
  +r8 = Lemma.and_true_right_side(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))), r7)
  +r9 = Lemma.and_true_right_side(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)), r8)
  (Lemma.and_true_left(Run.queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))))), h), (Lemma.and_true_left(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))))), r1), (Lemma.and_true_left(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))), r2), (Lemma.and_true_left(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))), r3), (Lemma.and_true_left(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))), r4), (Lemma.and_true_left(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))), r5), (Lemma.and_true_left(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))), r6), (Lemma.and_true_left(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))), r7), (Lemma.and_true_left(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)), r8), (Lemma.and_true_left(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input), r9), Lemma.and_true_right_side(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input), r9)))))))))))

def inv_join(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState,
  +h1: {Run.queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), grammar, input, s) == True{} : Bool},
  +h2: {Check.allClusters(Check.clustersOf(s), pred, grammar, input, s) == True{} : Bool},
  +h3: {Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s) == True{} : Bool},
  +h4: {Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)) == True{} : Bool},
  +h5: {Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool},
  +h6: {Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)) == True{} : Bool},
  +h7: {Run.subDescs(Run.todoOf(s), Check.seenOf(s)) == True{} : Bool},
  +h8: {Run.descsBounded(Check.seenOf(s), grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(Check.returnsOf(s), grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(Check.popsOf(s), input) == True{} : Bool},
  +h11: {Run.stepsBounded(Check.stepsOf(s), grammar, input) == True{} : Bool}) -> {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}:
  Lemma.and_true_intro(Run.queuedOk(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), grammar, input, s), Bool.and(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))))), h1, Lemma.and_true_intro(Check.allClusters(Check.clustersOf(s), pred, grammar, input, s), Bool.and(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))))), h2, Lemma.and_true_intro(Check.allReturns(Check.returnsOf(s), grammar, Check.popsOf(s), s), Bool.and(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))))), h3, Lemma.and_true_intro(Run.popsKeyed(Check.popsOf(s), Check.clustersOf(s)), Bool.and(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))))), h4, Lemma.and_true_intro(Run.descsKeyed(Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))))), h5, Lemma.and_true_intro(Run.retsKeyed(Check.returnsOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))))), h6, Lemma.and_true_intro(Run.subDescs(Run.todoOf(s), Check.seenOf(s)), Bool.and(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)))), h7, Lemma.and_true_intro(Run.descsBounded(Check.seenOf(s), grammar, input), Bool.and(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input))), h8, Lemma.and_true_intro(Run.retsBounded(Check.returnsOf(s), grammar, input), Bool.and(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input)), h9, Lemma.and_true_intro(Run.popsBounded(Check.popsOf(s), input), Run.stepsBounded(Check.stepsOf(s), grammar, input), h10, h11))))))))))

law todo_seen:
  for ts: +List<Gll.Desc>
  for +todoS: +List<Gll.Desc>
  for +seenS: +List<Gll.Desc>
  for +seenT: +List<Gll.Desc>
  for +nt: {Run.newQueued(ts, todoS, seenT) == True{} : Bool}
  for +h7: {Run.subDescs(todoS, seenS) == True{} : Bool}
  for +gs: {Run.subDescs(seenS, seenT) == True{} : Bool}
  {Run.subDescs(ts, seenT) == True{} : Bool}

def ts_pick(+x: Gll.Desc, +todoS: +List<Gll.Desc>, +seenS: +List<Gll.Desc>, +seenT: +List<Gll.Desc>,
  +h7: {Run.subDescs(todoS, seenS) == True{} : Bool}, +gs: {Run.subDescs(seenS, seenT) == True{} : Bool},
  cases: Either<{Gll.descIn(x, todoS) == True{} : Bool}, {Gll.descIn(x, seenT) == True{} : Bool}>) -> {Gll.descIn(x, seenT) == True{} : Bool}:
  match cases:
    case Inl{m}:
      C.desc_sub(seenS, x, seenT, C.desc_sub(todoS, x, seenS, m, h7), gs)
    case Inr{m}:
      m

def todo_seen(ts, todoS, seenS, seenT, nt, h7, gs):
  match ts:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, todoS), Gll.descIn(x, seenT)) : Bool}
      Lemma.and_true_intro(Gll.descIn(x, seenT), Run.subDescs(rest, seenT),
        ts_pick(x, todoS, seenS, seenT, h7, gs, Lemma.or_true_cases(Gll.descIn(x, todoS), Gll.descIn(x, seenT), Lemma.and_true_left(hx, Run.newQueued(rest, todoS, seenT), nt))),
        todo_seen(rest, todoS, seenS, seenT, Lemma.and_true_right_side(hx, Run.newQueued(rest, todoS, seenT), nt), h7, gs))

def AddsB4(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState) -> Type:
  {Run.grows(s, t) == True{} : Bool} &
  {Run.subDescs(Run.todoOf(s), Run.todoOf(t)) == True{} : Bool} &
  {Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)) == True{} : Bool} &
  {Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool} &
  {Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)) == True{} : Bool} &
  {Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input) == True{} : Bool} &
  {Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input) == True{} : Bool} &
  {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool}

def addsb_split(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState,
  +h: {Run.addsB(grammar, input, s, t) == True{} : Bool}) -> AddsB4(grammar, input, s, t):
  +r1 = Lemma.and_true_right_side(Run.grows(s, t), Bool.and(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))))), h)
  +r2 = Lemma.and_true_right_side(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))))), r1)
  +r3 = Lemma.and_true_right_side(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))), r2)
  +r4 = Lemma.and_true_right_side(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))), r3)
  +r5 = Lemma.and_true_right_side(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))), r4)
  +r6 = Lemma.and_true_right_side(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))), r5)
  (Lemma.and_true_left(Run.grows(s, t), Bool.and(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))))), h), (Lemma.and_true_left(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))))), r1), (Lemma.and_true_left(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))), r2), (Lemma.and_true_left(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))), r3), (Lemma.and_true_left(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))), r4), (Lemma.and_true_left(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))), r5), (Lemma.and_true_left(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)), r6), Lemma.and_true_right_side(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)), r6))))))))

def adds_make(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState,
  +g: {Run.grows(s, t) == True{} : Bool},
  +st: {Run.subDescs(Run.todoOf(s), Run.todoOf(t)) == True{} : Bool},
  +nq: {Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)) == True{} : Bool},
  +nk: {Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool},
  +nt: {Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)) == True{} : Bool},
  +nb: {Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input) == True{} : Bool},
  +ns: {Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input) == True{} : Bool},
  +ms: {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool},
  +ec: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>}) -> Adds(grammar, input, s, t):
  (Lemma.and_true_intro(Run.grows(s, t), Bool.and(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))))), g, Lemma.and_true_intro(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))))), st, Lemma.and_true_intro(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))), nq, Lemma.and_true_intro(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))))), nk, Lemma.and_true_intro(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))), nt, Lemma.and_true_intro(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s))), nb, Lemma.and_true_intro(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)), ns, ms))))))), (ec, (er, ep)))

law nb_sub:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Run.subDescs(ds, old) == True{} : Bool}
  {Run.newBounded(ds, old, grammar, input) == True{} : Bool}

def nb_sub(ds, old, grammar, input, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)), Run.newBounded(rest, old, grammar, input),
        Lemma.or_true_left_intro(Gll.descIn(x, old), Run.descBound(x, grammar, input), Lemma.and_true_left(Gll.descIn(x, old), Run.subDescs(rest, old), h)),
        nb_sub(rest, old, grammar, input, Lemma.and_true_right_side(Gll.descIn(x, old), Run.subDescs(rest, old), h)))

def nb_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hy: {Bool.or(Gll.descIn(y, old), Run.descBound(y, grammar, input)) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)) == True{} : Bool})
  -> {Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Bool.or(Gll.descIn(_, old), Run.descBound(_, grammar, input)) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law nb_at:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, ds) == True{} : Bool}
  for +h: {Run.newBounded(ds, old, grammar, input) == True{} : Bool}
  {Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)) == True{} : Bool}

def nb_at(ds, old, grammar, input, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Gll.descIn(x, old), Run.descBound(x, grammar, input)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Bool.or(Gll.descIn(y, old), Run.descBound(y, grammar, input)) : Bool}
      nb_pick(x, y, rest, old, grammar, input, Lemma.and_true_left(hy, Run.newBounded(rest, old, grammar, input), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => nb_at(rest, old, grammar, input, x, m2, Lemma.and_true_right_side(hy, Run.newBounded(rest, old, grammar, input), h)))

def nb_step(+x: Gll.Desc, +seenT: +List<Gll.Desc>, +seenS: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +nb1: {Run.newBounded(seenT, seenS, grammar, input) == True{} : Bool},
  cases: Either<{Gll.descIn(x, seenT) == True{} : Bool}, {Run.descBound(x, grammar, input) == True{} : Bool}>)
  -> {Bool.or(Gll.descIn(x, seenS), Run.descBound(x, grammar, input)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      nb_at(seenT, seenS, grammar, input, x, m, nb1)
    case Inr{k}:
      Lemma.or_true_right_intro(Gll.descIn(x, seenS), Run.descBound(x, grammar, input), k)

law nb_trans:
  for ds: +List<Gll.Desc>
  for +seenT: +List<Gll.Desc>
  for +seenS: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +nb2: {Run.newBounded(ds, seenT, grammar, input) == True{} : Bool}
  for +nb1: {Run.newBounded(seenT, seenS, grammar, input) == True{} : Bool}
  {Run.newBounded(ds, seenS, grammar, input) == True{} : Bool}

def nb_trans(ds, seenT, seenS, grammar, input, nb2, nb1):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, seenT), Run.descBound(x, grammar, input)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, seenS), Run.descBound(x, grammar, input)), Run.newBounded(rest, seenS, grammar, input),
        nb_step(x, seenT, seenS, grammar, input, nb1, Lemma.or_true_cases(Gll.descIn(x, seenT), Run.descBound(x, grammar, input), Lemma.and_true_left(hx, Run.newBounded(rest, seenT, grammar, input), nb2))),
        nb_trans(rest, seenT, seenS, grammar, input, Lemma.and_true_right_side(hx, Run.newBounded(rest, seenT, grammar, input), nb2), nb1))

# The same for steps.

def sb_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hy: {Run.stepBound(y, grammar, input) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Run.stepBound(x, grammar, input) == True{} : Bool}) -> {Run.stepBound(x, grammar, input) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Run.stepBound(_, grammar, input) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law step_bounded_at:
  for ds: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, ds) == True{} : Bool}
  for +h: {Run.stepsBounded(ds, grammar, input) == True{} : Bool}
  {Run.stepBound(x, grammar, input) == True{} : Bool}

def step_bounded_at(ds, grammar, input, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Run.stepBound(x, grammar, input) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      sb_pick(x, y, rest, grammar, input, Lemma.and_true_left(Run.stepBound(y, grammar, input), Run.stepsBounded(rest, grammar, input), h),
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        m2 => step_bounded_at(rest, grammar, input, x, m2, Lemma.and_true_right_side(Run.stepBound(y, grammar, input), Run.stepsBounded(rest, grammar, input), h)))

def sbn_step(+x: Core.Bsr, +old: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +ho: {Run.stepsBounded(old, grammar, input) == True{} : Bool},
  cases: Either<{Core.member(x, old) == True{} : Bool}, {Run.stepBound(x, grammar, input) == True{} : Bool}>) -> {Run.stepBound(x, grammar, input) == True{} : Bool}:
  match cases:
    case Inl{m}:
      step_bounded_at(old, grammar, input, x, m, ho)
    case Inr{b}:
      b

law steps_bounded_new:
  for ds: +List<Core.Bsr>
  for +old: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +nb: {Run.newStepsBounded(ds, old, grammar, input) == True{} : Bool}
  for +ho: {Run.stepsBounded(old, grammar, input) == True{} : Bool}
  {Run.stepsBounded(ds, grammar, input) == True{} : Bool}

def steps_bounded_new(ds, old, grammar, input, nb, ho):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)) : Bool}
      Lemma.and_true_intro(Run.stepBound(x, grammar, input), Run.stepsBounded(rest, grammar, input),
        sbn_step(x, old, grammar, input, ho, Lemma.or_true_cases(Core.member(x, old), Run.stepBound(x, grammar, input), Lemma.and_true_left(hx, Run.newStepsBounded(rest, old, grammar, input), nb))),
        steps_bounded_new(rest, old, grammar, input, Lemma.and_true_right_side(hx, Run.newStepsBounded(rest, old, grammar, input), nb), ho))

law ns_sub:
  for ds: +List<Core.Bsr>
  for +old: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Core.allIn(ds, old) == True{} : Bool}
  {Run.newStepsBounded(ds, old, grammar, input) == True{} : Bool}

def ns_sub(ds, old, grammar, input, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)), Run.newStepsBounded(rest, old, grammar, input),
        Lemma.or_true_left_intro(Core.member(x, old), Run.stepBound(x, grammar, input), Lemma.and_true_left(Core.member(x, old), Core.allIn(rest, old), h)),
        ns_sub(rest, old, grammar, input, Lemma.and_true_right_side(Core.member(x, old), Core.allIn(rest, old), h)))

def ns_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +old: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hy: {Bool.or(Core.member(y, old), Run.stepBound(y, grammar, input)) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)) == True{} : Bool})
  -> {Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Bool.or(Core.member(_, old), Run.stepBound(_, grammar, input)) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law ns_at:
  for ds: +List<Core.Bsr>
  for +old: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, ds) == True{} : Bool}
  for +h: {Run.newStepsBounded(ds, old, grammar, input) == True{} : Bool}
  {Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)) == True{} : Bool}

def ns_at(ds, old, grammar, input, x, m, h):
  match ds:
    case Nil{}:
      Empty.absurd({Bool.or(Core.member(x, old), Run.stepBound(x, grammar, input)) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {Bool.or(Core.member(y, old), Run.stepBound(y, grammar, input)) : Bool}
      ns_pick(x, y, rest, old, grammar, input, Lemma.and_true_left(hy, Run.newStepsBounded(rest, old, grammar, input), h), Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        m2 => ns_at(rest, old, grammar, input, x, m2, Lemma.and_true_right_side(hy, Run.newStepsBounded(rest, old, grammar, input), h)))

def ns_step(+x: Core.Bsr, +seenT: +List<Core.Bsr>, +seenS: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +nb1: {Run.newStepsBounded(seenT, seenS, grammar, input) == True{} : Bool},
  cases: Either<{Core.member(x, seenT) == True{} : Bool}, {Run.stepBound(x, grammar, input) == True{} : Bool}>)
  -> {Bool.or(Core.member(x, seenS), Run.stepBound(x, grammar, input)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      ns_at(seenT, seenS, grammar, input, x, m, nb1)
    case Inr{k}:
      Lemma.or_true_right_intro(Core.member(x, seenS), Run.stepBound(x, grammar, input), k)

law ns_trans:
  for ds: +List<Core.Bsr>
  for +seenT: +List<Core.Bsr>
  for +seenS: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +nb2: {Run.newStepsBounded(ds, seenT, grammar, input) == True{} : Bool}
  for +nb1: {Run.newStepsBounded(seenT, seenS, grammar, input) == True{} : Bool}
  {Run.newStepsBounded(ds, seenS, grammar, input) == True{} : Bool}

def ns_trans(ds, seenT, seenS, grammar, input, nb2, nb1):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Core.member(x, seenT), Run.stepBound(x, grammar, input)) : Bool}
      Lemma.and_true_intro(Bool.or(Core.member(x, seenS), Run.stepBound(x, grammar, input)), Run.newStepsBounded(rest, seenS, grammar, input),
        ns_step(x, seenT, seenS, grammar, input, nb1, Lemma.or_true_cases(Core.member(x, seenT), Run.stepBound(x, grammar, input), Lemma.and_true_left(hx, Run.newStepsBounded(rest, seenT, grammar, input), nb2))),
        ns_trans(rest, seenT, seenS, grammar, input, Lemma.and_true_right_side(hx, Run.newStepsBounded(rest, seenT, grammar, input), nb2), nb1))

law nq_sub:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +h: {Run.subDescs(ds, old) == True{} : Bool}
  {Run.newQueued(ds, old, todo) == True{} : Bool}

def nq_sub(ds, old, todo, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)), Run.newQueued(rest, old, todo),
        Lemma.or_true_left_intro(Gll.descIn(x, old), Gll.descIn(x, todo), Lemma.and_true_left(Gll.descIn(x, old), Run.subDescs(rest, old), h)),
        nq_sub(rest, old, todo, Lemma.and_true_right_side(Gll.descIn(x, old), Run.subDescs(rest, old), h)))

law nk_sub:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +h: {Run.subDescs(ds, old) == True{} : Bool}
  {Run.newKeyed(ds, old, grammar, cs) == True{} : Bool}

def nk_sub(ds, old, grammar, input, cs, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)), Run.newKeyed(rest, old, grammar, cs),
        Lemma.or_true_left_intro(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs), Lemma.and_true_left(Gll.descIn(x, old), Run.subDescs(rest, old), h)),
        nk_sub(rest, old, grammar, input, cs, Lemma.and_true_right_side(Gll.descIn(x, old), Run.subDescs(rest, old), h)))

def adds_refl(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState) -> Adds(grammar, input, s, s):
  adds_make(grammar, input, s, s, grows_refl(s), C.desc_refl(Run.todoOf(s)), nq_sub(Check.seenOf(s), Check.seenOf(s), Run.todoOf(s), C.desc_refl(Check.seenOf(s))),
    nk_sub(Check.seenOf(s), Check.seenOf(s), grammar, input, Check.clustersOf(s), C.desc_refl(Check.seenOf(s))),
    nq_sub(Run.todoOf(s), Run.todoOf(s), Check.seenOf(s), C.desc_refl(Run.todoOf(s))),
    nb_sub(Check.seenOf(s), Check.seenOf(s), grammar, input, C.desc_refl(Check.seenOf(s))), ns_sub(Check.stepsOf(s), Check.stepsOf(s), grammar, input, C.step_refl(Check.stepsOf(s))), Lemma.le_refl(Run.meas(grammar, input, s)), {==}, {==}, {==})

def nq_inner(+x: Gll.Desc, +seenS: +List<Gll.Desc>, +todoT: +List<Gll.Desc>, +todoU: +List<Gll.Desc>, +st: {Run.subDescs(todoT, todoU) == True{} : Bool},
  cases: Either<{Gll.descIn(x, seenS) == True{} : Bool}, {Gll.descIn(x, todoT) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, seenS), Gll.descIn(x, todoU)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      Lemma.or_true_left_intro(Gll.descIn(x, seenS), Gll.descIn(x, todoU), m)
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descIn(x, seenS), Gll.descIn(x, todoU), C.desc_sub(todoT, x, todoU, m, st))

def nq_step(+x: Gll.Desc, +seenT: +List<Gll.Desc>, +seenS: +List<Gll.Desc>, +todoT: +List<Gll.Desc>, +todoU: +List<Gll.Desc>,
  +nq1: {Run.newQueued(seenT, seenS, todoT) == True{} : Bool}, +st: {Run.subDescs(todoT, todoU) == True{} : Bool},
  cases: Either<{Gll.descIn(x, seenT) == True{} : Bool}, {Gll.descIn(x, todoU) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, seenS), Gll.descIn(x, todoU)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      nq_inner(x, seenS, todoT, todoU, st, Lemma.or_true_cases(Gll.descIn(x, seenS), Gll.descIn(x, todoT), nq_at(seenT, seenS, todoT, x, m, nq1)))
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descIn(x, seenS), Gll.descIn(x, todoU), m)

law nq_trans:
  for ds: +List<Gll.Desc>
  for +seenT: +List<Gll.Desc>
  for +seenS: +List<Gll.Desc>
  for +todoT: +List<Gll.Desc>
  for +todoU: +List<Gll.Desc>
  for +nq2: {Run.newQueued(ds, seenT, todoU) == True{} : Bool}
  for +nq1: {Run.newQueued(seenT, seenS, todoT) == True{} : Bool}
  for +st: {Run.subDescs(todoT, todoU) == True{} : Bool}
  {Run.newQueued(ds, seenS, todoU) == True{} : Bool}

def nq_trans(ds, seenT, seenS, todoT, todoU, nq2, nq1, st):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, seenT), Gll.descIn(x, todoU)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, seenS), Gll.descIn(x, todoU)), Run.newQueued(rest, seenS, todoU),
        nq_step(x, seenT, seenS, todoT, todoU, nq1, st, Lemma.or_true_cases(Gll.descIn(x, seenT), Gll.descIn(x, todoU), Lemma.and_true_left(hx, Run.newQueued(rest, seenT, todoU), nq2))),
        nq_trans(rest, seenT, seenS, todoT, todoU, Lemma.and_true_right_side(hx, Run.newQueued(rest, seenT, todoU), nq2), nq1, st))

def keyed_to(+x: Gll.Desc, +grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<Gll.CKey>, +b: +List<Gll.CKey>, +e: {a == b : +List<Gll.CKey>},
  +h: {Run.keyedDesc(x, grammar, a) == True{} : Bool}) -> {Run.keyedDesc(x, grammar, b) == True{} : Bool}:
  %e : {Run.keyedDesc(x, grammar, _) == True{} : Bool}
  h

def nk_step(+x: Gll.Desc, +seenT: +List<Gll.Desc>, +seenS: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +csT: +List<Gll.CKey>, +csS: +List<Gll.CKey>,
  +nk1: {Run.newKeyed(seenT, seenS, grammar, csS) == True{} : Bool}, +ec: {csT == csS : +List<Gll.CKey>},
  cases: Either<{Gll.descIn(x, seenT) == True{} : Bool}, {Run.keyedDesc(x, grammar, csT) == True{} : Bool}>)
  -> {Bool.or(Gll.descIn(x, seenS), Run.keyedDesc(x, grammar, csS)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      nk_at(seenT, seenS, grammar, input, csS, x, m, nk1)
    case Inr{k}:
      Lemma.or_true_right_intro(Gll.descIn(x, seenS), Run.keyedDesc(x, grammar, csS), keyed_to(x, grammar, input, csT, csS, ec, k))

law nk_trans:
  for ds: +List<Gll.Desc>
  for +seenT: +List<Gll.Desc>
  for +seenS: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +csT: +List<Gll.CKey>
  for +csS: +List<Gll.CKey>
  for +nk2: {Run.newKeyed(ds, seenT, grammar, csT) == True{} : Bool}
  for +nk1: {Run.newKeyed(seenT, seenS, grammar, csS) == True{} : Bool}
  for +ec: {csT == csS : +List<Gll.CKey>}
  {Run.newKeyed(ds, seenS, grammar, csS) == True{} : Bool}

def nk_trans(ds, seenT, seenS, grammar, input, csT, csS, nk2, nk1, ec):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, seenT), Run.keyedDesc(x, grammar, csT)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, seenS), Run.keyedDesc(x, grammar, csS)), Run.newKeyed(rest, seenS, grammar, csS),
        nk_step(x, seenT, seenS, grammar, input, csT, csS, nk1, ec, Lemma.or_true_cases(Gll.descIn(x, seenT), Run.keyedDesc(x, grammar, csT), Lemma.and_true_left(hx, Run.newKeyed(rest, seenT, grammar, csT), nk2))),
        nk_trans(rest, seenT, seenS, grammar, input, csT, csS, Lemma.and_true_right_side(hx, Run.newKeyed(rest, seenT, grammar, csT), nk2), nk1, ec))

law grows_seen:
  for s: Gll.GState
  for t: Gll.GState
  for +g: {Run.grows(s, t) == True{} : Bool}
  {Run.subDescs(Check.seenOf(s), Check.seenOf(t)) == True{} : Bool}

def grows_seen(s, t, g):
  match s t:
    case Gll.GState{+seen1, +todo1, +cs1, +rs1, +ps1, +ys1} Gll.GState{+seen2, +todo2, +cs2, +rs2, +ps2, +ys2}:
      Lemma.and_true_left(Run.subDescs(seen1, seen2), Bool.and(Run.subKeys(cs1, cs2), Bool.and(Run.subRets(rs1, rs2), Bool.and(Run.subPops(ps1, ps2), Core.allIn(ys1, ys2)))), g)

def adds_trans3(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +u: Gll.GState,
  +g1: {Run.grows(s, t) == True{} : Bool}, +st1: {Run.subDescs(Run.todoOf(s), Run.todoOf(t)) == True{} : Bool},
  +nq1: {Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)) == True{} : Bool},
  +nk1: {Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool},
  +nt1: {Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)) == True{} : Bool},
  +nb1: {Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input) == True{} : Bool},
  +ns1: {Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input) == True{} : Bool},
  +ms1: {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool},
  p2: AddsB4(grammar, input, t, u),
  +ec1: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>}, +er1: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>}, +ep1: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>},
  +ec2: {Check.clustersOf(u) == Check.clustersOf(t) : +List<Gll.CKey>}, +er2: {Check.returnsOf(u) == Check.returnsOf(t) : +List<Gll.Ret>}, +ep2: {Check.popsOf(u) == Check.popsOf(t) : +List<Gll.Pop>})
  -> Adds(grammar, input, s, u):
  match p2:
    case (+g2, (+st2, (+nq2, (+nk2, (+nt2, (+nb2, (+ns2, ms2))))))):
      adds_make(grammar, input, s, u, grows_trans(s, t, u, g1, g2), desc_trans(Run.todoOf(s), Run.todoOf(t), Run.todoOf(u), st1, st2),
        nq_trans(Check.seenOf(u), Check.seenOf(t), Check.seenOf(s), Run.todoOf(t), Run.todoOf(u), nq2, nq1, st2),
        nk_trans(Check.seenOf(u), Check.seenOf(t), Check.seenOf(s), grammar, input, Check.clustersOf(t), Check.clustersOf(s), nk2, nk1, ec1),
        nq_trans(Run.todoOf(u), Run.todoOf(t), Run.todoOf(s), Check.seenOf(t), Check.seenOf(u), nt2, nt1, grows_seen(t, u, g2)),
        nb_trans(Check.seenOf(u), Check.seenOf(t), Check.seenOf(s), grammar, input, nb2, nb1),
        ns_trans(Check.stepsOf(u), Check.stepsOf(t), Check.stepsOf(s), grammar, input, ns2, ns1),
        Lemma.le_trans(Run.meas(grammar, input, u), Run.meas(grammar, input, t), Run.meas(grammar, input, s), ms2, ms1),
        Equal.trans(+List<Gll.CKey>, Check.clustersOf(u), Check.clustersOf(t), Check.clustersOf(s), ec2, ec1),
        Equal.trans(+List<Gll.Ret>, Check.returnsOf(u), Check.returnsOf(t), Check.returnsOf(s), er2, er1),
        Equal.trans(+List<Gll.Pop>, Check.popsOf(u), Check.popsOf(t), Check.popsOf(s), ep2, ep1))

def adds_trans2(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +u: Gll.GState,
  p1: AddsB4(grammar, input, s, t), p2: AddsB4(grammar, input, t, u),
  +ec1: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>}, +er1: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>}, +ep1: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>},
  +ec2: {Check.clustersOf(u) == Check.clustersOf(t) : +List<Gll.CKey>}, +er2: {Check.returnsOf(u) == Check.returnsOf(t) : +List<Gll.Ret>}, +ep2: {Check.popsOf(u) == Check.popsOf(t) : +List<Gll.Pop>})
  -> Adds(grammar, input, s, u):
  match p1:
    case (+g1, (+st1, (+nq1, (+nk1, (+nt1, (+nb1, (+ns1, ms1))))))):
      adds_trans3(grammar, input, s, t, u, g1, st1, nq1, nk1, nt1, nb1, ns1, ms1, p2, ec1, er1, ep1, ec2, er2, ep2)

def adds_trans1(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +u: Gll.GState,
  +b1: {Run.addsB(grammar, input, s, t) == True{} : Bool},
  +ec1: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>}, +er1: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>}, +ep1: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>},
  a2: Adds(grammar, input, t, u)) -> Adds(grammar, input, s, u):
  match a2:
    case (+b2, (+ec2, (+er2, ep2))):
      adds_trans2(grammar, input, s, t, u, addsb_split(grammar, input, s, t, b1), addsb_split(grammar, input, t, u, b2), ec1, er1, ep1, ec2, er2, ep2)

law adds_trans:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +t: Gll.GState
  for +u: Gll.GState
  for a1: Adds(grammar, input, s, t)
  for a2: Adds(grammar, input, t, u)
  Adds(grammar, input, s, u)

def adds_trans(grammar, input, s, t, u, a1, a2):
  match a1:
    case (+b1, (+ec1, (+er1, ep1))):
      adds_trans1(grammar, input, s, t, u, b1, ec1, er1, ep1, a2)

# ======== AN ADDING OPERATION KEEPS THE INVARIANT ========

def qn_step(+x: Gll.Desc, +old: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState,
  +qo: {Run.queuedOk(old, todo, grammar, input, t) == True{} : Bool},
  cases: Either<{Gll.descIn(x, old) == True{} : Bool}, {Gll.descIn(x, todo) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      queued_at(old, todo, grammar, input, t, x, m, qo)
    case Inr{m}:
      Lemma.or_true_left_intro(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t), m)

law queued_new:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +t: Gll.GState
  for +nq: {Run.newQueued(ds, old, todo) == True{} : Bool}
  for +qo: {Run.queuedOk(old, todo, grammar, input, t) == True{} : Bool}
  {Run.queuedOk(ds, todo, grammar, input, t) == True{} : Bool}

def queued_new(ds, old, todo, grammar, input, t, nq, qo):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t)), Run.queuedOk(rest, todo, grammar, input, t),
        qn_step(x, old, todo, grammar, input, t, qo, Lemma.or_true_cases(Gll.descIn(x, old), Gll.descIn(x, todo), Lemma.and_true_left(hx, Run.newQueued(rest, old, todo), nq))),
        queued_new(rest, old, todo, grammar, input, t, Lemma.and_true_right_side(hx, Run.newQueued(rest, old, todo), nq), qo))

def kn_step(+x: Gll.Desc, +old: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +ko: {Run.descsKeyed(old, grammar, cs) == True{} : Bool},
  cases: Either<{Gll.descIn(x, old) == True{} : Bool}, {Run.keyedDesc(x, grammar, cs) == True{} : Bool}>) -> {Run.keyedDesc(x, grammar, cs) == True{} : Bool}:
  match cases:
    case Inl{m}:
      keyed_at(old, grammar, input, cs, x, m, ko)
    case Inr{k}:
      k

law keyed_new:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +cs: +List<Gll.CKey>
  for +nk: {Run.newKeyed(ds, old, grammar, cs) == True{} : Bool}
  for +ko: {Run.descsKeyed(old, grammar, cs) == True{} : Bool}
  {Run.descsKeyed(ds, grammar, cs) == True{} : Bool}

def keyed_new(ds, old, grammar, input, cs, nk, ko):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs)) : Bool}
      keyed_cons(x, rest, grammar, input, cs,
        kn_step(x, old, grammar, input, cs, ko, Lemma.or_true_cases(Gll.descIn(x, old), Run.keyedDesc(x, grammar, cs), Lemma.and_true_left(hx, Run.newKeyed(rest, old, grammar, cs), nk))),
        keyed_new(rest, old, grammar, input, cs, Lemma.and_true_right_side(hx, Run.newKeyed(rest, old, grammar, cs), nk), ko))

# Rewriting a list argument of a check.
def clusters_to(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState, +a: +List<Gll.CKey>, +b: +List<Gll.CKey>, +e: {a == b : +List<Gll.CKey>},
  +h: {Check.allClusters(b, pred, grammar, input, t) == True{} : Bool}) -> {Check.allClusters(a, pred, grammar, input, t) == True{} : Bool}:
  %Equal.sym(+List<Gll.CKey>, a, b, e) : {Check.allClusters(_, pred, grammar, input, t) == True{} : Bool}
  h

def returns_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState, +a: +List<Gll.Ret>, +b: +List<Gll.Ret>, +c: +List<Gll.Pop>, +d: +List<Gll.Pop>,
  +e1: {a == b : +List<Gll.Ret>}, +e2: {c == d : +List<Gll.Pop>},
  +h: {Check.allReturns(b, grammar, d, t) == True{} : Bool}) -> {Check.allReturns(a, grammar, c, t) == True{} : Bool}:
  %Equal.sym(+List<Gll.Ret>, a, b, e1) : {Check.allReturns(_, grammar, c, t) == True{} : Bool}
  %Equal.sym(+List<Gll.Pop>, c, d, e2) : {Check.allReturns(b, grammar, _, t) == True{} : Bool}
  h

def pops_keyed_to(+a: +List<Gll.Pop>, +b: +List<Gll.Pop>, +c: +List<Gll.CKey>, +d: +List<Gll.CKey>,
  +e1: {a == b : +List<Gll.Pop>}, +e2: {c == d : +List<Gll.CKey>},
  +h: {Run.popsKeyed(b, d) == True{} : Bool}) -> {Run.popsKeyed(a, c) == True{} : Bool}:
  %Equal.sym(+List<Gll.Pop>, a, b, e1) : {Run.popsKeyed(_, c) == True{} : Bool}
  %Equal.sym(+List<Gll.CKey>, c, d, e2) : {Run.popsKeyed(b, _) == True{} : Bool}
  h

def descs_keyed_to(+ds: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +c: +List<Gll.CKey>, +d: +List<Gll.CKey>, +e: {c == d : +List<Gll.CKey>},
  +h: {Run.descsKeyed(ds, grammar, d) == True{} : Bool}) -> {Run.descsKeyed(ds, grammar, c) == True{} : Bool}:
  %Equal.sym(+List<Gll.CKey>, c, d, e) : {Run.descsKeyed(ds, grammar, _) == True{} : Bool}
  h

def rets_keyed_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<Gll.Ret>, +b: +List<Gll.Ret>, +c: +List<Gll.CKey>, +d: +List<Gll.CKey>,
  +e1: {a == b : +List<Gll.Ret>}, +e2: {c == d : +List<Gll.CKey>},
  +h: {Run.retsKeyed(b, grammar, d) == True{} : Bool}) -> {Run.retsKeyed(a, grammar, c) == True{} : Bool}:
  %Equal.sym(+List<Gll.Ret>, a, b, e1) : {Run.retsKeyed(_, grammar, c) == True{} : Bool}
  %Equal.sym(+List<Gll.CKey>, c, d, e2) : {Run.retsKeyed(b, grammar, _) == True{} : Bool}
  h

law sub_map_left:
  for xs: +List<Gll.Desc>
  for +a: +List<Gll.Desc>
  for +c: +List<Gll.Desc>
  for +h: {Run.subDescs(xs, a) == True{} : Bool}
  {Run.subDescs(xs, List.append(&2, Gll.Desc, a, c)) == True{} : Bool}

def sub_map_left(xs, a, c, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, List.append(&2, Gll.Desc, a, c)), Run.subDescs(rest, List.append(&2, Gll.Desc, a, c)),
        C.desc_in_app_left(a, c, x, Lemma.and_true_left(Gll.descIn(x, a), Run.subDescs(rest, a), h)),
        sub_map_left(rest, a, c, Lemma.and_true_right_side(Gll.descIn(x, a), Run.subDescs(rest, a), h)))

law sub_map_right:
  for xs: +List<Gll.Desc>
  for +a: +List<Gll.Desc>
  for +c: +List<Gll.Desc>
  for +h: {Run.subDescs(xs, c) == True{} : Bool}
  {Run.subDescs(xs, List.append(&2, Gll.Desc, a, c)) == True{} : Bool}

def sub_map_right(xs, a, c, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, List.append(&2, Gll.Desc, a, c)), Run.subDescs(rest, List.append(&2, Gll.Desc, a, c)),
        C.desc_in_app_right(a, c, x, Lemma.and_true_left(Gll.descIn(x, c), Run.subDescs(rest, c), h)),
        sub_map_right(rest, a, c, Lemma.and_true_right_side(Gll.descIn(x, c), Run.subDescs(rest, c), h)))

law sub_app_parts:
  for a: +List<Gll.Desc>
  for +b: +List<Gll.Desc>
  for +zs: +List<Gll.Desc>
  for +ha: {Run.subDescs(a, zs) == True{} : Bool}
  for +hb: {Run.subDescs(b, zs) == True{} : Bool}
  {Run.subDescs(List.append(&2, Gll.Desc, a, b), zs) == True{} : Bool}

def sub_app_parts(a, b, zs, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, zs), Run.subDescs(List.append(&2, Gll.Desc, rest, b), zs), Lemma.and_true_left(Gll.descIn(x, zs), Run.subDescs(rest, zs), ha),
        sub_app_parts(rest, b, zs, Lemma.and_true_right_side(Gll.descIn(x, zs), Run.subDescs(rest, zs), ha), hb))

def sub_app(+extra: +List<Gll.Desc>, +b: +List<Gll.Desc>, +c: +List<Gll.Desc>, +h: {Run.subDescs(b, c) == True{} : Bool})
  -> {Run.subDescs(List.append(&2, Gll.Desc, extra, b), List.append(&2, Gll.Desc, extra, c)) == True{} : Bool}:
  sub_app_parts(extra, b, List.append(&2, Gll.Desc, extra, c), sub_map_left(extra, extra, c, C.desc_refl(extra)), sub_map_right(b, extra, c, h))

law nq_widen:
  for ds: +List<Gll.Desc>
  for +old: +List<Gll.Desc>
  for +extra: +List<Gll.Desc>
  for +todo: +List<Gll.Desc>
  for +h: {Run.newQueued(ds, old, todo) == True{} : Bool}
  {Run.newQueued(ds, old, List.append(&2, Gll.Desc, extra, todo)) == True{} : Bool}

def nq_widen_pick(+x: Gll.Desc, +old: +List<Gll.Desc>, +extra: +List<Gll.Desc>, +todo: +List<Gll.Desc>,
  cases: Either<{Gll.descIn(x, old) == True{} : Bool}, {Gll.descIn(x, todo) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, old), Gll.descIn(x, List.append(&2, Gll.Desc, extra, todo))) == True{} : Bool}:
  match cases:
    case Inl{m}:
      Lemma.or_true_left_intro(Gll.descIn(x, old), Gll.descIn(x, List.append(&2, Gll.Desc, extra, todo)), m)
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descIn(x, old), Gll.descIn(x, List.append(&2, Gll.Desc, extra, todo)), C.desc_in_app_right(extra, todo, x, m))

def nq_widen(ds, old, extra, todo, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, old), Gll.descIn(x, todo)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, old), Gll.descIn(x, List.append(&2, Gll.Desc, extra, todo))), Run.newQueued(rest, old, List.append(&2, Gll.Desc, extra, todo)),
        nq_widen_pick(x, old, extra, todo, Lemma.or_true_cases(Gll.descIn(x, old), Gll.descIn(x, todo), Lemma.and_true_left(hx, Run.newQueued(rest, old, todo), h))),
        nq_widen(rest, old, extra, todo, Lemma.and_true_right_side(hx, Run.newQueued(rest, old, todo), h)))

def adds_inv3(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState,
  +g: {Run.grows(s, t) == True{} : Bool}, +st: {Run.subDescs(Run.todoOf(s), Run.todoOf(t)) == True{} : Bool},
  +nq: {Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)) == True{} : Bool},
  +nk: {Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)) == True{} : Bool},
  +nt: {Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)) == True{} : Bool},
  +nb: {Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input) == True{} : Bool},
  +ns: {Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input) == True{} : Bool},
  +ec: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>},
  p: Inv6(extra, pred, grammar, input, s)) -> {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      +qt = List.append(&2, Gll.Desc, extra, Run.todoOf(t))
      inv_join(extra, pred, grammar, input, t,
        queued_new(Check.seenOf(t), Check.seenOf(s), qt, grammar, input, t, nq_widen(Check.seenOf(t), Check.seenOf(s), extra, Run.todoOf(t), nq),
          queued_grow(Check.seenOf(s), List.append(&2, Gll.Desc, extra, Run.todoOf(s)), qt, grammar, input, s, t, g, sub_app(extra, Run.todoOf(s), Run.todoOf(t), st), h1)),
        clusters_to(pred, grammar, input, t, Check.clustersOf(t), Check.clustersOf(s), ec, clusters_grow(Check.clustersOf(s), pred, grammar, input, s, t, g, h2)),
        returns_to(grammar, input, t, Check.returnsOf(t), Check.returnsOf(s), Check.popsOf(t), Check.popsOf(s), er, ep, returns_grow(Check.returnsOf(s), grammar, input, Check.popsOf(s), s, t, g, h3)),
        pops_keyed_to(Check.popsOf(t), Check.popsOf(s), Check.clustersOf(t), Check.clustersOf(s), ep, ec, h4),
        descs_keyed_to(Check.seenOf(t), grammar, input, Check.clustersOf(t), Check.clustersOf(s), ec, keyed_new(Check.seenOf(t), Check.seenOf(s), grammar, input, Check.clustersOf(s), nk, h5)),
        rets_keyed_to(grammar, input, Check.returnsOf(t), Check.returnsOf(s), Check.clustersOf(t), Check.clustersOf(s), er, ec, h6),
        todo_seen(Run.todoOf(t), Run.todoOf(s), Check.seenOf(s), Check.seenOf(t), nt, h7, grows_seen(s, t, g)),
        bounded_new(Check.seenOf(t), Check.seenOf(s), grammar, input, nb, h8), rets_bounded_to(grammar, input, Check.returnsOf(t), Check.returnsOf(s), er, h9),
        pops_bounded_to(input, Check.popsOf(t), Check.popsOf(s), ep, h10), steps_bounded_new(Check.stepsOf(t), Check.stepsOf(s), grammar, input, ns, h11))

def adds_inv2(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState,
  p4: AddsB4(grammar, input, s, t),
  +ec: {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == Check.returnsOf(s) : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == Check.popsOf(s) : +List<Gll.Pop>},
  +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}) -> {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool}:
  match p4:
    case (+g, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      adds_inv3(extra, pred, grammar, input, s, t, g, st, nq, nk, nt, nb, ns, ec, er, ep, inv_split(extra, pred, grammar, input, s, h))

# An adding operation keeps the invariant.
law adds_inv:
  for +extra: +List<Gll.Desc>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +t: Gll.GState
  for a: Adds(grammar, input, s, t)
  for +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}
  {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool}

def adds_inv(extra, pred, grammar, input, s, t, a, h):
  match a:
    case (+b, (+ec, (+er, ep))):
      adds_inv2(extra, pred, grammar, input, s, t, addsb_split(grammar, input, s, t, b), ec, er, ep, h)

# ======== THE ADDING OPERATIONS OF THE ENGINE ========

def adds_grows(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +b: {Run.addsB(grammar, input, s, t) == True{} : Bool}) -> {Run.grows(s, t) == True{} : Bool}:
  Lemma.and_true_left(Run.grows(s, t), Bool.and(Run.subDescs(Run.todoOf(s), Run.todoOf(t)), Bool.and(Run.newQueued(Check.seenOf(t), Check.seenOf(s), Run.todoOf(t)), Bool.and(Run.newKeyed(Check.seenOf(t), Check.seenOf(s), grammar, Check.clustersOf(s)), Bool.and(Run.newQueued(Run.todoOf(t), Run.todoOf(s), Check.seenOf(t)), Bool.and(Run.newBounded(Check.seenOf(t), Check.seenOf(s), grammar, input), Bool.and(Run.newStepsBounded(Check.stepsOf(t), Check.stepsOf(s), grammar, input), Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)))))))), b)

def meas_part(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, p: AddsB4(grammar, input, s, t)) -> {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool}:
  match p:
    case (+g, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      ms

def adds_meas(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +b: {Run.addsB(grammar, input, s, t) == True{} : Bool}) -> {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool}:
  meas_part(grammar, input, s, t, addsb_split(grammar, input, s, t, b))

def same_grows(+seen: +List<Gll.Desc>, +seen2: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +todo2: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>, +ys2: +List<Core.Bsr>,
  +hd: {Run.subDescs(seen, seen2) == True{} : Bool}, +hy: {Core.allIn(ys, ys2) == True{} : Bool})
  -> {Run.grows(Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.GState{seen2, todo2, cs, rs, ps, ys2}) == True{} : Bool}:
  Lemma.and_true_intro(Run.subDescs(seen, seen2), Bool.and(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys2)))), hd,
    Lemma.and_true_intro(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys2))), key_refl(cs),
      Lemma.and_true_intro(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys2)), ret_refl(rs),
        Lemma.and_true_intro(Run.subPops(ps, ps), Core.allIn(ys, ys2), pop_refl(ps), hy))))

# A new descriptor within bounds: one fewer unseen, one more to do.
def meas_new(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>,
  +out: {Gll.descIn(d, seen) == False{} : Bool}, +bd: {Run.descBound(d, grammar, input) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Run.countNot(Run.univ(grammar, input), d <> seen), 1n+List.length(&2, Gll.Desc, todo)), Nat.add(Run.countNot(Run.univ(grammar, input), seen), List.length(&2, Gll.Desc, todo))) == True{} : Bool}:
  +U = Run.univ(grammar, input)
  +c2 = Run.countNot(U, d <> seen)
  +T = List.length(&2, Gll.Desc, todo)
  %Equal.sym(Nat, Nat.add(c2, 1n+T), 1n+Nat.add(c2, T), Lemma.add_succ_right(c2, T)) : {Nat.is_le(_, Nat.add(Run.countNot(U, seen), T)) == True{} : Bool}
  C.le_add_l(1n+c2, Run.countNot(U, seen), T, C.count_drop(U, seen, d, C.bound_mem(d, grammar, input, bd), out))

def add_desc_pick(known: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +ek: {Gll.descIn(d, seen) == known : Bool},
  +kd: {Run.keyedDesc(d, grammar, cs) == True{} : Bool},
  +bd: {Run.descBound(d, grammar, input) == True{} : Bool})
  -> Adds(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.descPick(known, d, Gll.GState{seen, todo, cs, rs, ps, ys})) & {Check.seenIn(d, Gll.descPick(known, d, Gll.GState{seen, todo, cs, rs, ps, ys})) == True{} : Bool}:
  match known:
    case True{}:
      (adds_refl(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}), ek)
    case False{}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +t = {Gll.GState{d <> seen, d <> todo, cs, rs, ps, ys} : Gll.GState}
      +inD = Lemma.or_true_left_intro(Gll.descEq(d, d), Gll.descIn(d, seen), C.desc_eq_refl(d))
      +inT = Lemma.or_true_left_intro(Gll.descEq(d, d), Gll.descIn(d, todo), C.desc_eq_refl(d))
      +nq = Lemma.and_true_intro(Bool.or(Gll.descIn(d, seen), Gll.descIn(d, d <> todo)), Run.newQueued(seen, seen, d <> todo),
        Lemma.or_true_right_intro(Gll.descIn(d, seen), Gll.descIn(d, d <> todo), inT), nq_sub(seen, seen, d <> todo, C.desc_refl(seen)))
      +nk = Lemma.and_true_intro(Bool.or(Gll.descIn(d, seen), Run.keyedDesc(d, grammar, cs)), Run.newKeyed(seen, seen, grammar, cs),
        Lemma.or_true_right_intro(Gll.descIn(d, seen), Run.keyedDesc(d, grammar, cs), kd), nk_sub(seen, seen, grammar, input, cs, C.desc_refl(seen)))
      +nt = Lemma.and_true_intro(Bool.or(Gll.descIn(d, todo), Gll.descIn(d, d <> seen)), Run.newQueued(todo, todo, d <> seen),
        Lemma.or_true_right_intro(Gll.descIn(d, todo), Gll.descIn(d, d <> seen), inD), nq_sub(todo, todo, d <> seen, C.desc_refl(todo)))
      (adds_make(grammar, input, s, t, same_grows(seen, d <> seen, todo, d <> todo, cs, rs, ps, ys, ys, C.desc_weaken(seen, d, seen, C.desc_refl(seen)), C.step_refl(ys)),
        C.desc_weaken(todo, d, todo, C.desc_refl(todo)), nq, nk, nt,
        Lemma.and_true_intro(Bool.or(Gll.descIn(d, seen), Run.descBound(d, grammar, input)), Run.newBounded(seen, seen, grammar, input),
          Lemma.or_true_right_intro(Gll.descIn(d, seen), Run.descBound(d, grammar, input), bd), nb_sub(seen, seen, grammar, input, C.desc_refl(seen))), ns_sub(ys, ys, grammar, input, C.step_refl(ys)),
        meas_new(grammar, input, d, seen, todo, ek, bd), {==}, {==}, {==}), inD)

law with_desc:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +d: Gll.Desc
  for s: Gll.GState
  for +kd: {Run.keyedDesc(d, grammar, Check.clustersOf(s)) == True{} : Bool}
  for +bd: {Run.descBound(d, grammar, input) == True{} : Bool}
  Adds(grammar, input, s, Gll.withDesc(d, s)) & {Check.seenIn(d, Gll.withDesc(d, s)) == True{} : Bool}

def with_desc(grammar, input, d, s, kd, bd):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      add_desc_pick(Gll.descIn(d, seen), grammar, input, d, seen, todo, cs, rs, ps, ys, {==}, kd, bd)

def add_step_pick(known: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +y: Core.Bsr, +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +ek: {Core.member(y, ys) == known : Bool},
  +bs: {Run.stepBound(y, grammar, input) == True{} : Bool})
  -> Adds(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.stepPick(known, y, Gll.GState{seen, todo, cs, rs, ps, ys})) & {Check.stepIn(y, Gll.stepPick(known, y, Gll.GState{seen, todo, cs, rs, ps, ys})) == True{} : Bool}:
  match known:
    case True{}:
      (adds_refl(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}), ek)
    case False{}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +t = {Gll.GState{seen, todo, cs, rs, ps, y <> ys} : Gll.GState}
      (adds_make(grammar, input, s, t, same_grows(seen, seen, todo, todo, cs, rs, ps, ys, y <> ys, C.desc_refl(seen), C.step_weaken(ys, y, ys, C.step_refl(ys))),
        C.desc_refl(todo), nq_sub(seen, seen, todo, C.desc_refl(seen)), nk_sub(seen, seen, grammar, input, cs, C.desc_refl(seen)), nq_sub(todo, todo, seen, C.desc_refl(todo)),
        nb_sub(seen, seen, grammar, input, C.desc_refl(seen)), Lemma.and_true_intro(Bool.or(Core.member(y, ys), Run.stepBound(y, grammar, input)), Run.newStepsBounded(ys, ys, grammar, input), Lemma.or_true_right_intro(Core.member(y, ys), Run.stepBound(y, grammar, input), bs), ns_sub(ys, ys, grammar, input, C.step_refl(ys))), Lemma.le_refl(Run.meas(grammar, input, s)), {==}, {==}, {==}),
       Lemma.or_true_left_intro(Core.bsrEq(y, y), Core.member(y, ys), C.bsr_eq_refl(y)))

law with_step:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +y: Core.Bsr
  for s: Gll.GState
  for +bs: {Run.stepBound(y, grammar, input) == True{} : Bool}
  Adds(grammar, input, s, Gll.withStep(y, s)) & {Check.stepIn(y, Gll.withStep(y, s)) == True{} : Bool}

def with_step(grammar, input, y, s, bs):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      add_step_pick(Core.member(y, ys), grammar, input, y, seen, todo, cs, rs, ps, ys, {==}, bs)

# Two adding operations in a row; the second's growth carries the first's posts along.
def adds_seq2(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState, a1: Adds(grammar, input, s, s1),
  +b2: {Run.addsB(grammar, input, s1, t) == True{} : Bool}, +ec2: {Check.clustersOf(t) == Check.clustersOf(s1) : +List<Gll.CKey>},
  +er2: {Check.returnsOf(t) == Check.returnsOf(s1) : +List<Gll.Ret>}, ep2: {Check.popsOf(t) == Check.popsOf(s1) : +List<Gll.Pop>})
  -> Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool}:
  (adds_trans(grammar, input, s, s1, t, a1, (b2, (ec2, (er2, ep2)))), adds_grows(grammar, input, s1, t, b2))

def adds_seq(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState, a1: Adds(grammar, input, s, s1), a2: Adds(grammar, input, s1, t))
  -> Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool}:
  match a2:
    case (+b2, (+ec2, (+er2, ep2))):
      adds_seq2(grammar, input, s, s1, t, a1, b2, ec2, er2, ep2)

def adds_clusters(+grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, a: Adds(grammar, input, s, t))
  -> Adds(grammar, input, s, t) & {Check.clustersOf(t) == Check.clustersOf(s) : +List<Gll.CKey>}:
  match a:
    case (+b, (+ec, (+er, ep))):
      ((b, (ec, (er, ep))), ec)

def descs_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +rest: +List<Gll.Desc>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +seen1: {Check.seenIn(d, s1) == True{} : Bool},
  pa: Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool},
  +all2: {Check.allSeen(rest, t) == True{} : Bool}) -> Adds(grammar, input, s, t) & {Check.allSeen(d <> rest, t) == True{} : Bool}:
  match pa:
    case (a, +g):
      (a, Lemma.and_true_intro(Check.seenIn(d, t), Check.allSeen(rest, t), seen_grow(s1, t, d, g, seen1), all2))

def descs_rest(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +rest: +List<Gll.Desc>, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  a1: Adds(grammar, input, s, s1), +seen1: {Check.seenIn(d, s1) == True{} : Bool},
  p2: Adds(grammar, input, s1, t) & {Check.allSeen(rest, t) == True{} : Bool}) -> Adds(grammar, input, s, t) & {Check.allSeen(d <> rest, t) == True{} : Bool}:
  match p2:
    case (a2, +all2):
      descs_join(grammar, input, d, rest, s, s1, t, seen1, adds_seq(grammar, input, s, s1, t, a1, a2), all2)

def descs_first2(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +rest: +List<Gll.Desc>, +s: Gll.GState,
  +kr: {Run.descsKeyed(rest, grammar, Check.clustersOf(s)) == True{} : Bool},
  +seen1: {Check.seenIn(d, Gll.withDesc(d, s)) == True{} : Bool},
  pc: Adds(grammar, input, s, Gll.withDesc(d, s)) & {Check.clustersOf(Gll.withDesc(d, s)) == Check.clustersOf(s) : +List<Gll.CKey>},
  later: {Run.descsKeyed(rest, grammar, Check.clustersOf(Gll.withDesc(d, s))) == True{} : Bool} -> Adds(grammar, input, Gll.withDesc(d, s), Gll.withDescs(rest, Gll.withDesc(d, s))) & {Check.allSeen(rest, Gll.withDescs(rest, Gll.withDesc(d, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.withDescs(rest, Gll.withDesc(d, s))) & {Check.allSeen(d <> rest, Gll.withDescs(rest, Gll.withDesc(d, s))) == True{} : Bool}:
  match pc:
    case (a1, +ec):
      +s1 = Gll.withDesc(d, s)
      descs_rest(grammar, input, d, rest, s, s1, Gll.withDescs(rest, s1), a1, seen1,
        later(descs_keyed_to(rest, grammar, input, Check.clustersOf(s1), Check.clustersOf(s), ec, kr)))

def descs_first(+grammar: +List<Core.Production>, +input: +List<Nat>, +d: Gll.Desc, +rest: +List<Gll.Desc>, +s: Gll.GState,
  +kr: {Run.descsKeyed(rest, grammar, Check.clustersOf(s)) == True{} : Bool},
  p1: Adds(grammar, input, s, Gll.withDesc(d, s)) & {Check.seenIn(d, Gll.withDesc(d, s)) == True{} : Bool},
  later: {Run.descsKeyed(rest, grammar, Check.clustersOf(Gll.withDesc(d, s))) == True{} : Bool} -> Adds(grammar, input, Gll.withDesc(d, s), Gll.withDescs(rest, Gll.withDesc(d, s))) & {Check.allSeen(rest, Gll.withDescs(rest, Gll.withDesc(d, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.withDescs(rest, Gll.withDesc(d, s))) & {Check.allSeen(d <> rest, Gll.withDescs(rest, Gll.withDesc(d, s))) == True{} : Bool}:
  match p1:
    case (a1, +seen1):
      +s1 = Gll.withDesc(d, s)
      descs_first2(grammar, input, d, rest, s, kr, seen1, adds_clusters(grammar, input, s, s1, a1), later)

law with_descs:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +kd: {Run.descsKeyed(ds, grammar, Check.clustersOf(s)) == True{} : Bool}
  for +bds: {Run.descsBounded(ds, grammar, input) == True{} : Bool}
  Adds(grammar, input, s, Gll.withDescs(ds, s)) & {Check.allSeen(ds, Gll.withDescs(ds, s)) == True{} : Bool}

def with_descs(ds, grammar, input, s, kd, bds):
  match ds:
    case Nil{}:
      (adds_refl(grammar, input, s), {==})
    case Con{+d, +rest}:
      +bh = Lemma.and_true_left(Run.descBound(d, grammar, input), Run.descsBounded(rest, grammar, input), bds)
      +bt = Lemma.and_true_right_side(Run.descBound(d, grammar, input), Run.descsBounded(rest, grammar, input), bds)
      descs_first(grammar, input, d, rest, s, keyed_tail(d, rest, grammar, input, Check.clustersOf(s), kd),
        with_desc(grammar, input, d, s, keyed_head(d, rest, grammar, input, Check.clustersOf(s), kd), bh),
        k => with_descs(rest, grammar, input, Gll.withDesc(d, s), k, bt))

# ======== RESUMING ========

def resume_four(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +seen1: {Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, s1) == True{} : Bool}, +st2: {Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, t) == True{} : Bool},
  pa: Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool})
  -> Adds(grammar, input, s, t) & {Bool.and(Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, t), Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, t)) == True{} : Bool}:
  match pa:
    case (a, +g):
      (a, Lemma.and_true_intro(Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, t), Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, t), seen_grow(s1, t, Gll.Desc{q, 1n+dot, k, j}, g, seen1), st2))

def resume_three(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState, +s1: Gll.GState,
  a1: Adds(grammar, input, s, s1), +seen1: {Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, s1) == True{} : Bool},
  p2: Adds(grammar, input, s1, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1)) & {Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1)) & {Bool.and(Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1)), Check.stepIn(Core.Bsr{q, 1n+dot, k, kc, j}, Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1))) == True{} : Bool}:
  match p2:
    case (a2, +st2):
      +t = Gll.withStep(Core.Bsr{q, 1n+dot, k, kc, j}, s1)
      resume_four(grammar, input, q, dot, k, kc, j, s, s1, t, seen1, st2, adds_seq(grammar, input, s, s1, t, a1, a2))

def resume_two(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState,
  +bs: {Run.stepBound(Core.Bsr{q, 1n+dot, k, kc, j}, grammar, input) == True{} : Bool},
  p1: Adds(grammar, input, s, Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, s)) & {Check.seenIn(Gll.Desc{q, 1n+dot, k, j}, Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, s)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumePick(True{}, q, dot, k, kc, j, s)) & {Check.resumeOk(True{}, q, dot, k, kc, j, Gll.resumePick(True{}, q, dot, k, kc, j, s)) == True{} : Bool}:
  match p1:
    case (a1, +seen1):
      +s1 = Gll.withDesc(Gll.Desc{q, 1n+dot, k, j}, s)
      resume_three(grammar, input, q, dot, k, kc, j, s, s1, a1, seen1, with_step(grammar, input, Core.Bsr{q, 1n+dot, k, kc, j}, s1, bs))

def resume_pick(ok: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, +s: Gll.GState,
  +kq: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool},
  +bq: {Run.descBound(Gll.Desc{q, 1n+dot, k, j}, grammar, input) == True{} : Bool},
  +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumePick(ok, q, dot, k, kc, j, s)) & {Check.resumeOk(ok, q, dot, k, kc, j, Gll.resumePick(ok, q, dot, k, kc, j, s)) == True{} : Bool}:
  match ok:
    case True{}:
      resume_two(grammar, input, q, dot, k, kc, j, s, Lemma.and_true_intro(Run.descBound(Gll.Desc{q, 1n+dot, k, j}, grammar, input), Nat.is_le(kc, List.length(&2, Nat, input)), bq, bk), with_desc(grammar, input, Gll.Desc{q, 1n+dot, k, j}, s, kq, bq))
    case False{}:
      (adds_refl(grammar, input, s), {==})

def edge_desc_bound(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +j: Nat,
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool}, +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool})
  -> {Run.descBound(Gll.Desc{q, 1n+dot, k, j}, grammar, input) == True{} : Bool}:
  +a = {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) : Bool}
  +b = {Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +c = {Nat.is_le(k, List.length(&2, Nat, input)) : Bool}
  +r1 = Lemma.and_true_right_side(a, Bool.and(b, c), be)
  Lemma.and_true_intro(a, Bool.and(b, Bool.and(c, Nat.is_le(j, List.length(&2, Nat, input)))), Lemma.and_true_left(a, Bool.and(b, c), be),
    Lemma.and_true_intro(b, Bool.and(c, Nat.is_le(j, List.length(&2, Nat, input))), Lemma.and_true_left(b, c, r1),
      Lemma.and_true_intro(c, Nat.is_le(j, List.length(&2, Nat, input)), Lemma.and_true_right_side(b, c, r1), bj)))

def resume_spec(edge: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +kc: Nat, +j: Nat, +s: Gll.GState,
  +ke: {Run.keyedEdge(edge, grammar, Check.clustersOf(s)) == True{} : Bool},
  +be: {Run.edgeBound(edge, grammar, input) == True{} : Bool}, +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool}, +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resume(grammar, edge, kc, j, s)) & {Check.edgeOk(edge, grammar, kc, j, Gll.resume(grammar, edge, kc, j, s)) == True{} : Bool}:
  match edge:
    case Gll.Edge{+q, +dot, +k}:
      resume_pick(Gll.needHolds(Gll.needAt(grammar, q, dot), kc, j), grammar, input, q, dot, k, kc, j, s, ke, edge_desc_bound(grammar, input, q, dot, k, j, be, bj), bk)

def resume_if(hit: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +edge: Gll.Edge, +kc: Nat, +j: Nat, +s: Gll.GState,
  +ke: {Run.keyedEdge(edge, grammar, Check.clustersOf(s)) == True{} : Bool},
  +be: {Run.edgeBound(edge, grammar, input) == True{} : Bool}, +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool}, +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumeIf(hit, grammar, edge, kc, j, s)) & {Check.hitOk(hit, edge, grammar, kc, j, Gll.resumeIf(hit, grammar, edge, kc, j, s)) == True{} : Bool}:
  match hit:
    case True{}:
      resume_spec(edge, grammar, input, kc, j, s, ke, be, bj, bk)
    case False{}:
      (adds_refl(grammar, input, s), {==})

def rk_head(e: Gll.Edge, +k2: Gll.CKey, +rest: +List<Gll.Ret>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +h: {Run.retsKeyed(Gll.Ret{k2, e} <> rest, grammar, cs) == True{} : Bool}) -> {Run.keyedEdge(e, grammar, cs) == True{} : Bool}:
  match e:
    case Gll.Edge{+q, +d, +k}:
      Lemma.and_true_left(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.retsKeyed(rest, grammar, cs), h)

def rk_tail(e: Gll.Edge, +k2: Gll.CKey, +rest: +List<Gll.Ret>, +grammar: +List<Core.Production>, +input: +List<Nat>, +cs: +List<Gll.CKey>,
  +h: {Run.retsKeyed(Gll.Ret{k2, e} <> rest, grammar, cs) == True{} : Bool}) -> {Run.retsKeyed(rest, grammar, cs) == True{} : Bool}:
  match e:
    case Gll.Edge{+q, +d, +k}:
      Lemma.and_true_right_side(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.retsKeyed(rest, grammar, cs), h)

def edge_keyed_to(+e: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +c: +List<Gll.CKey>, +d: +List<Gll.CKey>, +eq: {c == d : +List<Gll.CKey>},
  +h: {Run.keyedEdge(e, grammar, d) == True{} : Bool}) -> {Run.keyedEdge(e, grammar, c) == True{} : Bool}:
  %Equal.sym(+List<Gll.CKey>, c, d, eq) : {Run.keyedEdge(e, grammar, _) == True{} : Bool}
  h

# A later state keeps an earlier hit.
def hits_join(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +j: Nat, +s1: Gll.GState, +t: Gll.GState,
  +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, s1) == True{} : Bool},
  +g: {Run.grows(s1, t) == True{} : Bool},
  +h2: {Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool}) -> {Run.retsHit(Gll.Ret{k2, e2} <> rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool}:
  Lemma.and_true_intro(Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, t), Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t),
    hit_grow(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, input, kc, j, s1, t, g, h1), h2)

def all_after2(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +j: Nat, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, s1) == True{} : Bool},
  +h2: {Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool},
  pa: Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool})
  -> Adds(grammar, input, s, t) & {Run.retsHit(Gll.Ret{k2, e2} <> rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool}:
  match pa:
    case (a, +g):
      (a, hits_join(grammar, input, x, kc, k2, e2, rest, j, s1, t, h1, g, h2))

def all_after(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +j: Nat, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  a1: Adds(grammar, input, s, s1), +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, s1) == True{} : Bool},
  p2: Adds(grammar, input, s1, t) & {Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool})
  -> Adds(grammar, input, s, t) & {Run.retsHit(Gll.Ret{k2, e2} <> rest, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool}:
  match p2:
    case (a2, +h2):
      all_after2(grammar, input, x, kc, k2, e2, rest, j, s, s1, t, h1, h2, adds_seq(grammar, input, s, s1, t, a1, a2))

def all_first2(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +j: Nat, +s: Gll.GState,
  +rr: {Run.retsKeyed(rest, grammar, Check.clustersOf(s)) == True{} : Bool},
  +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)) == True{} : Bool},
  pc: Adds(grammar, input, s, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)) & {Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)) == Check.clustersOf(s) : +List<Gll.CKey>},
  later: {Run.retsKeyed(rest, grammar, Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool} ->
    Adds(grammar, input, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s), Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) &
    {Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) &
     {Run.retsHit(Gll.Ret{k2, e2} <> rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool}:
  match pc:
    case (a1, +ec):
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)
      all_after(grammar, input, x, kc, k2, e2, rest, j, s, s1, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, s1), a1, h1,
        later(rets_keyed_to(grammar, input, rest, rest, Check.clustersOf(s1), Check.clustersOf(s), {==}, ec, rr)))

law resume_all:
  for rets: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +j: Nat
  for +s: Gll.GState
  for +rk: {Run.retsKeyed(rets, grammar, Check.clustersOf(s)) == True{} : Bool}
  for +rb: {Run.retsBounded(rets, grammar, input) == True{} : Bool}
  for +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool}
  for +bk: {Run.keyBound(key, input) == True{} : Bool}
  Adds(grammar, input, s, Gll.resumeAll(rets, grammar, key, j, s)) & {Run.retsHit(rets, grammar, key, j, Gll.resumeAll(rets, grammar, key, j, s)) == True{} : Bool}

def all_first(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +e2: Gll.Edge, +rest: +List<Gll.Ret>, +j: Nat, +s: Gll.GState,
  +rr: {Run.retsKeyed(rest, grammar, Check.clustersOf(s)) == True{} : Bool},
  p1: Adds(grammar, input, s, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)) & {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), e2, grammar, kc, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)) == True{} : Bool},
  later: {Run.retsKeyed(rest, grammar, Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool} ->
    Adds(grammar, input, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s), Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) &
    {Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) &
     {Run.retsHit(Gll.Ret{k2, e2} <> rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeAll(rest, grammar, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s))) == True{} : Bool}:
  match p1:
    case (a1, +h1):
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s)
      all_first2(grammar, input, x, kc, k2, e2, rest, j, s, rr, h1, adds_clusters(grammar, input, s, s1, a1), later)

def resume_all(rets, grammar, input, key, j, s, rk, rb, bj, bk):
  match rets key:
    case Nil{} +key0:
      (adds_refl(grammar, input, s), {==})
    case Con{Gll.Ret{+k2, +e2}, +rest} Gll.CKey{+x, +kc}:
      +bh = Lemma.and_true_left(Run.edgeBound(e2, grammar, input), Run.retsBounded(rest, grammar, input), rb)
      +bt = Lemma.and_true_right_side(Run.edgeBound(e2, grammar, input), Run.retsBounded(rest, grammar, input), rb)
      all_first(grammar, input, x, kc, k2, e2, rest, j, s, rk_tail(e2, k2, rest, grammar, input, Check.clustersOf(s), rk),
        resume_if(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, input, e2, kc, j, s, rk_head(e2, k2, rest, grammar, input, Check.clustersOf(s), rk), bh, bj, bk),
        r2 => resume_all(rest, grammar, input, Gll.CKey{x, kc}, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, e2, kc, j, s), r2, bt, bj, bk))

def pops_after2(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +j: Nat, +rest: +List<Gll.Pop>, +edge: Gll.Edge, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, s1) == True{} : Bool},
  +h2: {Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, t) == True{} : Bool},
  pa: Adds(grammar, input, s, t) & {Run.grows(s1, t) == True{} : Bool})
  -> Adds(grammar, input, s, t) & {Check.edgePops(Gll.Pop{k2, j} <> rest, grammar, Gll.CKey{x, kc}, edge, t) == True{} : Bool}:
  match pa:
    case (a, +g):
      (a, Lemma.and_true_intro(Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, t), Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, t),
        hit_grow(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, input, kc, j, s1, t, g, h1), h2))

def pops_after(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +j: Nat, +rest: +List<Gll.Pop>, +edge: Gll.Edge, +s: Gll.GState, +s1: Gll.GState, +t: Gll.GState,
  a1: Adds(grammar, input, s, s1), +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, s1) == True{} : Bool},
  p2: Adds(grammar, input, s1, t) & {Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, t) == True{} : Bool})
  -> Adds(grammar, input, s, t) & {Check.edgePops(Gll.Pop{k2, j} <> rest, grammar, Gll.CKey{x, kc}, edge, t) == True{} : Bool}:
  match p2:
    case (a2, +h2):
      pops_after2(grammar, input, x, kc, k2, j, rest, edge, s, s1, t, h1, h2, adds_seq(grammar, input, s, s1, t, a1, a2))

def pops_first2(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +j: Nat, +rest: +List<Gll.Pop>, +edge: Gll.Edge, +s: Gll.GState,
  +ke: {Run.keyedEdge(edge, grammar, Check.clustersOf(s)) == True{} : Bool},
  +h1: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)) == True{} : Bool},
  pc: Adds(grammar, input, s, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)) & {Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)) == Check.clustersOf(s) : +List<Gll.CKey>},
  later: {Run.keyedEdge(edge, grammar, Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool} ->
    Adds(grammar, input, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s), Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) &
    {Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) &
     {Check.edgePops(Gll.Pop{k2, j} <> rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool}:
  match pc:
    case (a1, +ec):
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)
      pops_after(grammar, input, x, kc, k2, j, rest, edge, s, s1, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, s1), a1, h1,
        later(edge_keyed_to(edge, grammar, input, Check.clustersOf(s1), Check.clustersOf(s), ec, ke)))

def pops_first(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +kc: Nat, +k2: Gll.CKey, +j: Nat, +rest: +List<Gll.Pop>, +edge: Gll.Edge, +s: Gll.GState,
  +ke: {Run.keyedEdge(edge, grammar, Check.clustersOf(s)) == True{} : Bool},
  p1: Adds(grammar, input, s, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)) & {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)) == True{} : Bool},
  later: {Run.keyedEdge(edge, grammar, Check.clustersOf(Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool} ->
    Adds(grammar, input, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s), Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) &
    {Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) &
     {Check.edgePops(Gll.Pop{k2, j} <> rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumePops(rest, grammar, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s))) == True{} : Bool}:
  match p1:
    case (a1, +h1):
      +s1 = Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s)
      pops_first2(grammar, input, x, kc, k2, j, rest, edge, s, ke, h1, adds_clusters(grammar, input, s, s1, a1), later)

law resume_pops:
  for pops: +List<Gll.Pop>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +edge: Gll.Edge
  for +s: Gll.GState
  for +ke: {Run.keyedEdge(edge, grammar, Check.clustersOf(s)) == True{} : Bool}
  for +be: {Run.edgeBound(edge, grammar, input) == True{} : Bool}
  for +pb: {Run.popsBounded(pops, input) == True{} : Bool}
  for +bk: {Run.keyBound(key, input) == True{} : Bool}
  Adds(grammar, input, s, Gll.resumePops(pops, grammar, key, edge, s)) & {Check.edgePops(pops, grammar, key, edge, Gll.resumePops(pops, grammar, key, edge, s)) == True{} : Bool}

def resume_pops(pops, grammar, input, key, edge, s, ke, be, pb, bk):
  match pops key:
    case Nil{} +key0:
      (adds_refl(grammar, input, s), {==})
    case Con{Gll.Pop{+k2, +j}, +rest} Gll.CKey{+x, +kc}:
      +bh = Lemma.and_true_left(Nat.is_le(j, List.length(&2, Nat, input)), Run.popsBounded(rest, input), pb)
      +bt = Lemma.and_true_right_side(Nat.is_le(j, List.length(&2, Nat, input)), Run.popsBounded(rest, input), pb)
      pops_first(grammar, input, x, kc, k2, j, rest, edge, s, ke,
        resume_if(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, input, edge, kc, j, s, ke, be, bh, bk),
        k => resume_pops(rest, grammar, input, Gll.CKey{x, kc}, edge, Gll.resumeIf(Gll.keyEq(Gll.CKey{x, kc}, k2), grammar, edge, kc, j, s), k, be, bt, bk))

# ======== LEAVING A CLUSTER ========

def key_eq_flip(+x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat,
  +h: {Gll.keyEq(Gll.CKey{x2, kc2}, Gll.CKey{x, kc}) == True{} : Bool}) -> {Gll.keyEq(Gll.CKey{x, kc}, Gll.CKey{x2, kc2}) == True{} : Bool}:
  +a = Equal.trans(Bool, Nat.is_eq(x, x2), Nat.is_eq(x2, x), True{}, Lemma.nat_eq_symm(x, x2), Lemma.and_true_left(Nat.is_eq(x2, x), Nat.is_eq(kc2, kc), h))
  +b = Equal.trans(Bool, Nat.is_eq(kc, kc2), Nat.is_eq(kc2, kc), True{}, Lemma.nat_eq_symm(kc, kc2), Lemma.and_true_right_side(Nat.is_eq(x2, x), Nat.is_eq(kc2, kc), h))
  Lemma.and_true_intro(Nat.is_eq(x, x2), Nat.is_eq(kc, kc2), a, b)

def edge_at(+e: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +a: Nat, +b: Nat, +j: Nat, +t: Gll.GState, +eq: {a == b : Nat},
  +h: {Check.edgeOk(e, grammar, a, j, t) == True{} : Bool}) -> {Check.edgeOk(e, grammar, b, j, t) == True{} : Bool}:
  %eq : {Check.edgeOk(e, grammar, _, j, t) == True{} : Bool}
  h

def flip_pick(b: Bool, +x: Nat, +kc: Nat, +x2: Nat, +kc2: Nat, +e: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +j: Nat, +t: Gll.GState,
  +eb: {Gll.keyEq(Gll.CKey{x2, kc2}, Gll.CKey{x, kc}) == b : Bool},
  +h: {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, Gll.CKey{x2, kc2}), e, grammar, kc, j, t) == True{} : Bool}) -> {Check.hitOk(b, e, grammar, kc2, j, t) == True{} : Bool}:
  match b:
    case True{}:
      +eok = G.hit_true(Gll.keyEq(Gll.CKey{x, kc}, Gll.CKey{x2, kc2}), e, grammar, kc, j, t, key_eq_flip(x, kc, x2, kc2, eb), h)
      +ek = Lemma.nat_eq_sound(kc, kc2, Equal.trans(Bool, Nat.is_eq(kc, kc2), Nat.is_eq(kc2, kc), True{}, Lemma.nat_eq_symm(kc, kc2), Lemma.and_true_right_side(Nat.is_eq(x2, x), Nat.is_eq(kc2, kc), eb)))
      edge_at(e, grammar, input, kc, kc2, j, t, ek, eok)
    case False{}:
      {==}

law rets_after_pop:
  for rs: +List<Gll.Ret>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ps: +List<Gll.Pop>
  for +x: Nat
  for +kc: Nat
  for +j: Nat
  for +t: Gll.GState
  for +hit: {Run.retsHit(rs, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool}
  for +old: {Check.allReturns(rs, grammar, ps, t) == True{} : Bool}
  {Check.allReturns(rs, grammar, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, t) == True{} : Bool}

def rets_after_pop(rs, grammar, input, ps, x, kc, j, t, hit, old):
  match rs:
    case Nil{}:
      {==}
    case Con{Gll.Ret{Gll.CKey{+x2, +kc2}, +e}, +rest}:
      +h1 = {Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, Gll.CKey{x2, kc2}), e, grammar, kc, j, t) : Bool}
      +o1 = {Check.edgePops(ps, grammar, Gll.CKey{x2, kc2}, e, t) : Bool}
      +hp = {Check.hitOk(Gll.keyEq(Gll.CKey{x2, kc2}, Gll.CKey{x, kc}), e, grammar, kc2, j, t) : Bool}
      Lemma.and_true_intro(Bool.and(hp, o1), Check.allReturns(rest, grammar, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, t),
        Lemma.and_true_intro(hp, o1,
          flip_pick(Gll.keyEq(Gll.CKey{x2, kc2}, Gll.CKey{x, kc}), x, kc, x2, kc2, e, grammar, input, j, t, {==}, Lemma.and_true_left(h1, Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t), hit)),
          Lemma.and_true_left(o1, Check.allReturns(rest, grammar, ps, t), old)),
        rets_after_pop(rest, grammar, input, ps, x, kc, j, t, Lemma.and_true_right_side(h1, Run.retsHit(rest, grammar, Gll.CKey{x, kc}, j, t), hit), Lemma.and_true_right_side(o1, Check.allReturns(rest, grammar, ps, t), old)))

def pop_moved(+key: Gll.CKey, +j: Nat, +a: +List<Gll.Pop>, +b: +List<Gll.Pop>, +e: {a == b : +List<Gll.Pop>},
  +h: {Gll.popIn(key, j, b) == True{} : Bool}) -> {Gll.popIn(key, j, a) == True{} : Bool}:
  %Equal.sym(+List<Gll.Pop>, a, b, e) : {Gll.popIn(key, j, _) == True{} : Bool}
  h

def leave_new3(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +j: Nat, +t: Gll.GState,
  +kk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == True{} : Bool},
  +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool},
  +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  +hit: {Run.retsHit(rs, grammar, Gll.CKey{x, kc}, j, t) == True{} : Bool},
  p4: AddsB4(grammar, input, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys}, t),
  +ec: {Check.clustersOf(t) == cs : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == rs : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == Gll.Pop{Gll.CKey{x, kc}, j} <> ps : +List<Gll.Pop>})
  -> {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool} & {Gll.popIn(Gll.CKey{x, kc}, j, Check.popsOf(t)) == True{} : Bool} & {Run.grows(Gll.GState{seen, todo, cs, rs, ps, ys}, t) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys})) == True{} : Bool}:
  match p4:
    case (+g0, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +key = {Gll.CKey{x, kc} : Gll.CKey}
      +ps2 = {Gll.Pop{key, j} <> ps : +List<Gll.Pop>}
      +s0 = {Gll.GState{seen, todo, cs, rs, ps2, ys} : Gll.GState}
      +gs0 = Lemma.and_true_intro(Run.subDescs(seen, seen), Bool.and(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps2), Core.allIn(ys, ys)))), C.desc_refl(seen),
        Lemma.and_true_intro(Run.subKeys(cs, cs), Bool.and(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps2), Core.allIn(ys, ys))), key_refl(cs),
          Lemma.and_true_intro(Run.subRets(rs, rs), Bool.and(Run.subPops(ps, ps2), Core.allIn(ys, ys)), ret_refl(rs),
            Lemma.and_true_intro(Run.subPops(ps, ps2), Core.allIn(ys, ys), pop_weaken(ps, key, j, ps, pop_refl(ps)), C.step_refl(ys)))))
      +g = grows_trans(s, s0, t, gs0, g0)
      +qt = List.append(&2, Gll.Desc, extra, Run.todoOf(t))
      +inv = inv_join(extra, pred, grammar, input, t,
        queued_new(Check.seenOf(t), seen, qt, grammar, input, t, nq_widen(Check.seenOf(t), seen, extra, Run.todoOf(t), nq),
          queued_grow(seen, List.append(&2, Gll.Desc, extra, todo), qt, grammar, input, s, t, g, sub_app(extra, todo, Run.todoOf(t), st), h1)),
        clusters_to(pred, grammar, input, t, Check.clustersOf(t), cs, ec, clusters_grow(cs, pred, grammar, input, s, t, g, h2)),
        returns_to(grammar, input, t, Check.returnsOf(t), rs, Check.popsOf(t), ps2, er, ep, rets_after_pop(rs, grammar, input, ps, x, kc, j, t, hit, returns_grow(rs, grammar, input, ps, s, t, g, h3))),
        pops_keyed_to(Check.popsOf(t), ps2, Check.clustersOf(t), cs, ep, ec, Lemma.and_true_intro(Gll.keyIn(key, cs), Run.popsKeyed(ps, cs), kk, h4)),
        descs_keyed_to(Check.seenOf(t), grammar, input, Check.clustersOf(t), cs, ec, keyed_new(Check.seenOf(t), seen, grammar, input, cs, nk, h5)),
        rets_keyed_to(grammar, input, Check.returnsOf(t), rs, Check.clustersOf(t), cs, er, ec, h6),
        todo_seen(Run.todoOf(t), todo, seen, Check.seenOf(t), nt, h7, grows_seen(s, t, g)),
        bounded_new(Check.seenOf(t), seen, grammar, input, nb, h8), rets_bounded_to(grammar, input, Check.returnsOf(t), rs, er, h9),
        pops_bounded_to(input, Check.popsOf(t), ps2, ep, Lemma.and_true_intro(Nat.is_le(j, List.length(&2, Nat, input)), Run.popsBounded(ps, input), bj, h10)), steps_bounded_new(Check.stepsOf(t), ys, grammar, input, ns, h11))
      +inPop = Lemma.or_true_left_intro(Bool.and(Gll.keyEq(key, key), Nat.is_eq(j, j)), Gll.popIn(key, j, ps), Lemma.and_true_intro(Gll.keyEq(key, key), Nat.is_eq(j, j), key_eq_refl(key), Lemma.nat_eq_refl(j)))
      (inv, (pop_moved(key, j, Check.popsOf(t), ps2, ep, inPop), (g, ms)))

def Out(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +post: Bool) -> Type:
  {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool} & {post == True{} : Bool} & {Run.grows(s, t) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, s)) == True{} : Bool}

def leave_new2(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +j: Nat,
  +kk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == True{} : Bool},
  +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool},
  +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  p: Adds(grammar, input, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys}, Gll.resumeAll(rs, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys})) &
    {Run.retsHit(rs, grammar, Gll.CKey{x, kc}, j, Gll.resumeAll(rs, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys})) == True{} : Bool})
  -> Out(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.resumeAll(rs, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys}),
       Gll.popIn(Gll.CKey{x, kc}, j, Check.popsOf(Gll.resumeAll(rs, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys})))):
  match p:
    case ((+b, (+ec, (+er, ep))), +hit):
      +s0 = {Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys} : Gll.GState}
      +t = Gll.resumeAll(rs, grammar, Gll.CKey{x, kc}, j, s0)
      leave_new3(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, kc, j, t, kk, bj, bk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hit, addsb_split(grammar, input, s0, t, b), ec, er, ep)

def leave_pick(known: Bool, +extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +j: Nat,
  +ek: {Gll.popIn(Gll.CKey{x, kc}, j, ps) == known : Bool},
  +kk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == True{} : Bool},
  +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool},
  +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool})
  -> Out(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.leavePick(known, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, ps, ys}),
       Gll.popIn(Gll.CKey{x, kc}, j, Check.popsOf(Gll.leavePick(known, grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, ps, ys})))):
  match known:
    case True{}:
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      (inv_join(extra, pred, grammar, input, s, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11), (ek, (grows_refl(s), Lemma.le_refl(Run.meas(grammar, input, s)))))
    case False{}:
      +s0 = {Gll.GState{seen, todo, cs, rs, Gll.Pop{Gll.CKey{x, kc}, j} <> ps, ys} : Gll.GState}
      leave_new2(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, kc, j, kk, bj, bk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        resume_all(rs, grammar, input, Gll.CKey{x, kc}, j, s0, h6, h9, bj, bk))

def leave_parts(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>, +x: Nat, +kc: Nat, +j: Nat,
  +kk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == True{} : Bool},
  +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool},
  +bk: {Nat.is_le(kc, List.length(&2, Nat, input)) == True{} : Bool},
  p: Inv6(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}))
  -> Out(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.leave(grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, ps, ys}),
       Gll.popIn(Gll.CKey{x, kc}, j, Check.popsOf(Gll.leave(grammar, Gll.CKey{x, kc}, j, Gll.GState{seen, todo, cs, rs, ps, ys})))):
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      leave_pick(Gll.popIn(Gll.CKey{x, kc}, j, ps), extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, kc, j, {==}, kk, bj, bk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11)

# Leaving a known cluster keeps the invariant and records the pop.
law leave_spec:
  for +extra: +List<Gll.Desc>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for key: Gll.CKey
  for +j: Nat
  for s: Gll.GState
  for +kk: {Gll.keyIn(key, Check.clustersOf(s)) == True{} : Bool}
  for +bj: {Nat.is_le(j, List.length(&2, Nat, input)) == True{} : Bool}
  for +bk: {Run.keyBound(key, input) == True{} : Bool}
  for +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}
  Out(extra, pred, grammar, input, s, Gll.leave(grammar, key, j, s), Gll.popIn(key, j, Check.popsOf(Gll.leave(grammar, key, j, s))))

def leave_spec(extra, pred, grammar, input, key, j, s, kk, bj, bk, h):
  match key s:
    case Gll.CKey{+x, +kc} Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      leave_parts(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, kc, j, kk, bj, bk, inv_split(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, h))

def match_token(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState,
  +kq: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool},
  +hI: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  hb: {b == True{} : Bool} -> {Run.descBound(Gll.Desc{q, 1n+dot, k, 1n+i}, grammar, input) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.matchToken(b, q, dot, k, i, s)) & {Check.tokenOk(b, q, dot, k, i, Gll.matchToken(b, q, dot, k, i, s)) == True{} : Bool}:
  match b:
    case True{}:
      resume_pick(True{}, grammar, input, q, dot, k, i, 1n+i, s, kq, hb({==}), hI)
    case False{}:
      (adds_refl(grammar, input, s), {==})

def empty_if(dot: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +k: Nat, +i: Nat, +s: Gll.GState,
  +bd: {Run.descBound(Gll.Desc{q, dot, k, i}, grammar, input) == True{} : Bool}, +hI: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool})
  -> Adds(grammar, input, s, Gll.emptyIf(dot, q, k, i, s)) & {Check.emptyOk(dot, q, k, i, Gll.emptyIf(dot, q, k, i, s)) == True{} : Bool}:
  match dot:
    case 0n:
      with_step(grammar, input, Core.Bsr{q, 0n, k, i, i}, s, Lemma.and_true_intro(Run.descBound(Gll.Desc{q, 0n, k, i}, grammar, input), Nat.is_le(i, List.length(&2, Nat, input)), bd, hI))
    case 1n+(+e):
      (adds_refl(grammar, input, s), {==})

# ======== BOUNDS OF NEW FACTS ========

def isSome(m: Maybe<&2, Core.Sym>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

law nth_lt:
  for items: +List<Core.Sym>
  for d: Nat
  for +y: Core.Sym
  for +h: {Gll.nthSym(items, d) == Some{y} : Maybe<&2, Core.Sym>}
  {Nat.is_le(1n+d, List.length(&2, Core.Sym, items)) == True{} : Bool}

def nth_lt(items, d, y, h):
  match items d:
    case Nil{} +d0:
      Empty.absurd({Nat.is_le(1n+d0, 0n) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Core.Sym>, Bool, v => isSome(v), None{}, Some{y}, h)))
    case Con{+x, +rest} 0n:
      Lemma.zero_le(List.length(&2, Core.Sym, rest))
    case Con{+x, +rest} 1n+(+m):
      nth_lt(rest, m, y, h)

law tok_lt:
  for input: +List<Nat>
  for i: Nat
  for +t: Nat
  for +h: {Core.tokIs(Core.tokAt(input, i), t) == True{} : Bool}
  {Nat.is_le(1n+i, List.length(&2, Nat, input)) == True{} : Bool}

def tok_lt(input, i, t, h):
  match input i:
    case Nil{} +i0:
      Empty.absurd({Nat.is_le(1n+i0, 0n) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+x, +rest} 0n:
      Lemma.zero_le(List.length(&2, Nat, rest))
    case Con{+x, +rest} 1n+(+m):
      tok_lt(rest, m, t, h)

def token_bound(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +tk: Nat,
  +hA: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hd: {Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool},
  +hK: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hb: {Core.tokIs(Core.tokAt(input, i), tk) == True{} : Bool}) -> {Run.descBound(Gll.Desc{q, 1n+dot, k, 1n+i}, grammar, input) == True{} : Bool}:
  +n = List.length(&2, Nat, input)
  Lemma.and_true_intro(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(k, n), Nat.is_le(1n+i, n))), hA,
    Lemma.and_true_intro(Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Bool.and(Nat.is_le(k, n), Nat.is_le(1n+i, n)), hd,
      Lemma.and_true_intro(Nat.is_le(k, n), Nat.is_le(1n+i, n), hK, tok_lt(input, i, tk, hb))))

law lhs_bound:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  {Nat.is_le(1n+q, List.length(&2, Core.Production, g)) == True{} : Bool}

def lhs_bound(g, q, x, h):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Nat.is_le(1n+q0, 0n) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+l, +r}, +rest} 0n:
      Lemma.zero_le(List.length(&2, Core.Production, rest))
    case Con{Core.Production{+l, +r}, +rest} 1n+(+m):
      lhs_bound(rest, m, x, h)

def keep_bounded(a: Bool, b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +base: Nat, +x: Nat, +i: Nat, +more: +List<Gll.Desc>,
  hbOf: {b == True{} : Bool} -> {Core.lhsIs(grammar, base, x) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +later: {Run.descsBounded(more, grammar, input) == True{} : Bool}) -> {Run.descsBounded(Gll.keepDesc(Bool.and(a, b), Gll.Desc{base, 0n, i, i}, more), grammar, input) == True{} : Bool}:
  match a b:
    case True{} True{}:
      +n = List.length(&2, Nat, input)
      +len = List.length(&2, Core.Sym, Core.rhsOf(grammar, base))
      +sb = Lemma.and_true_intro(Nat.is_le(1n+base, List.length(&2, Core.Production, grammar)), Bool.and(Nat.is_le(0n, len), Bool.and(Nat.is_le(i, n), Nat.is_le(i, n))),
        lhs_bound(grammar, base, x, hbOf({==})),
        Lemma.and_true_intro(Nat.is_le(0n, len), Bool.and(Nat.is_le(i, n), Nat.is_le(i, n)), Lemma.zero_le(len), Lemma.and_true_intro(Nat.is_le(i, n), Nat.is_le(i, n), bi, bi)))
      Lemma.and_true_intro(Run.descBound(Gll.Desc{base, 0n, i, i}, grammar, input), Run.descsBounded(more, grammar, input), sb, later)
    case True{} False{}:
      later
    case False{} True{}:
      later
    case False{} False{}:
      later

# The seeds of x at i lie within bounds.
law seeds_bounded:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +pred: Gll.Pred
  for +tok: Maybe<&2, Nat>
  for +x: Nat
  for +i: Nat
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  {Run.descsBounded(Gll.productionsOf(g, pred, tok, x, base, i), grammar, input) == True{} : Bool}

def seeds_bounded(g, base, grammar, input, pred, tok, x, i, hg, bi):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      keep_bounded(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x), grammar, input, base, x, i, Gll.productionsOf(rest, pred, tok, x, 1n+base, i),
        hb => G.head_lhs(grammar, base, x, lhs, rhs, rest, hg, hb), bi,
        seeds_bounded(rest, 1n+base, grammar, input, pred, tok, x, i, G.drop_step(base, grammar, lhs, rhs, rest, hg), bi))

# ======== CALLING A NONTERMINAL ========

def key_lhs(+grammar: +List<Core.Production>, +input: +List<Nat>, +base: Nat, +x: Nat, +i: Nat, +cs: +List<Gll.CKey>,
  +hl: {Core.lhsIs(grammar, base, x) == True{} : Bool}, +hk: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool})
  -> {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, base), i}, cs) == True{} : Bool}:
  %Equal.sym(Nat, Gll.lhsOf(grammar, base), x, G.lhs_of(grammar, base, x, hl)) : {Gll.keyIn(Gll.CKey{_, i}, cs) == True{} : Bool}
  hk

def keep_keyed(a: Bool, b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +base: Nat, +x: Nat, +i: Nat, +cs: +List<Gll.CKey>, +more: +List<Gll.Desc>,
  hbOf: {b == True{} : Bool} -> {Core.lhsIs(grammar, base, x) == True{} : Bool},
  +hk: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool},
  +later: {Run.descsKeyed(more, grammar, cs) == True{} : Bool}) -> {Run.descsKeyed(Gll.keepDesc(Bool.and(a, b), Gll.Desc{base, 0n, i, i}, more), grammar, cs) == True{} : Bool}:
  match a b:
    case True{} True{}:
      keyed_cons(Gll.Desc{base, 0n, i, i}, more, grammar, input, cs, key_lhs(grammar, input, base, x, i, cs, hbOf({==}), hk), later)
    case True{} False{}:
      later
    case False{} True{}:
      later
    case False{} False{}:
      later

# The seeds of x at i all belong to the cluster of x at i.
law seeds_keyed:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +pred: Gll.Pred
  for +tok: Maybe<&2, Nat>
  for +x: Nat
  for +i: Nat
  for +cs: +List<Gll.CKey>
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hk: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool}
  {Run.descsKeyed(Gll.productionsOf(g, pred, tok, x, base, i), grammar, cs) == True{} : Bool}

def seeds_keyed(g, base, grammar, input, pred, tok, x, i, cs, hg, hk):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      keep_keyed(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x), grammar, input, base, x, i, cs, Gll.productionsOf(rest, pred, tok, x, 1n+base, i),
        hb => G.head_lhs(grammar, base, x, lhs, rhs, rest, hg, hb), hk,
        seeds_keyed(rest, 1n+base, grammar, input, pred, tok, x, i, cs, G.drop_step(base, grammar, lhs, rhs, rest, hg), hk))

# A return edge of a new cluster meets no pop: every pop belongs to a known cluster.
def miss_pick(b: Bool, +x: Nat, +kc: Nat, +k2: Gll.CKey, +edge: Gll.Edge, +grammar: +List<Core.Production>, +input: +List<Nat>, +j: Nat, +t: Gll.GState, +cs: +List<Gll.CKey>,
  +eb: {Gll.keyEq(Gll.CKey{x, kc}, k2) == b : Bool},
  +hk2: {Gll.keyIn(k2, cs) == True{} : Bool},
  +nk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == False{} : Bool}) -> {Check.hitOk(b, edge, grammar, kc, j, t) == True{} : Bool}:
  match b:
    case True{}:
      +e = G.key_eq_sound(Gll.CKey{x, kc}, k2, eb)
      +k1 = {(%Equal.sym(Gll.CKey, Gll.CKey{x, kc}, k2, e) : {Gll.keyIn(_, cs) == True{} : Bool}
        hk2) : {Gll.keyIn(Gll.CKey{x, kc}, cs) == True{} : Bool}}
      Empty.absurd({Check.edgeOk(edge, grammar, kc, j, t) == True{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Gll.keyIn(Gll.CKey{x, kc}, cs), False{}, Equal.sym(Bool, Gll.keyIn(Gll.CKey{x, kc}, cs), True{}, k1), nk)))
    case False{}:
      {==}

law pops_miss:
  for ps: +List<Gll.Pop>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Nat
  for +kc: Nat
  for +edge: Gll.Edge
  for +t: Gll.GState
  for +cs: +List<Gll.CKey>
  for +pk: {Run.popsKeyed(ps, cs) == True{} : Bool}
  for +nk: {Gll.keyIn(Gll.CKey{x, kc}, cs) == False{} : Bool}
  {Check.edgePops(ps, grammar, Gll.CKey{x, kc}, edge, t) == True{} : Bool}

def pops_miss(ps, grammar, input, x, kc, edge, t, cs, pk, nk):
  match ps:
    case Nil{}:
      {==}
    case Con{Gll.Pop{+k2, +j}, +rest}:
      Lemma.and_true_intro(Check.hitOk(Gll.keyEq(Gll.CKey{x, kc}, k2), edge, grammar, kc, j, t), Check.edgePops(rest, grammar, Gll.CKey{x, kc}, edge, t),
        miss_pick(Gll.keyEq(Gll.CKey{x, kc}, k2), x, kc, k2, edge, grammar, input, j, t, cs, {==}, Lemma.and_true_left(Gll.keyIn(k2, cs), Run.popsKeyed(rest, cs), pk), nk),
        pops_miss(rest, grammar, input, x, kc, edge, t, cs, Lemma.and_true_right_side(Gll.keyIn(k2, cs), Run.popsKeyed(rest, cs), pk), nk))

def call_post(+t: Gll.GState, +key: Gll.CKey, +edge: Gll.Edge, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>,
  +ec: {Check.clustersOf(t) == cs : +List<Gll.CKey>}, +er: {Check.returnsOf(t) == rs : +List<Gll.Ret>},
  +hk: {Gll.keyIn(key, cs) == True{} : Bool}, +hr: {Check.retIn(key, edge, rs) == True{} : Bool})
  -> {Bool.and(Gll.keyIn(key, Check.clustersOf(t)), Check.retIn(key, edge, Check.returnsOf(t))) == True{} : Bool}:
  %Equal.sym(+List<Gll.CKey>, Check.clustersOf(t), cs, ec) : {Bool.and(Gll.keyIn(key, _), Check.retIn(key, edge, Check.returnsOf(t))) == True{} : Bool}
  %Equal.sym(+List<Gll.Ret>, Check.returnsOf(t), rs, er) : {Bool.and(Gll.keyIn(key, cs), Check.retIn(key, edge, _)) == True{} : Bool}
  Lemma.and_true_intro(Gll.keyIn(key, cs), Check.retIn(key, edge, rs), hk, hr)

def ret_here(+key: Gll.CKey, +edge: Gll.Edge, +rs: +List<Gll.Ret>) -> {Check.retIn(key, edge, Gll.Ret{key, edge} <> rs) == True{} : Bool}:
  Lemma.or_true_left_intro(Bool.and(Gll.keyEq(key, key), Check.edgeEq(edge, edge)), Check.retIn(key, edge, rs), Lemma.and_true_intro(Gll.keyEq(key, key), Check.edgeEq(edge, edge), key_eq_refl(key), edge_eq_refl(edge)))

def grows_parts(+seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +cs2: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +rs2: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +hc: {Run.subKeys(cs, cs2) == True{} : Bool}, +hr: {Run.subRets(rs, rs2) == True{} : Bool})
  -> {Run.grows(Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.GState{seen, todo, cs2, rs2, ps, ys}) == True{} : Bool}:
  Lemma.and_true_intro(Run.subDescs(seen, seen), Bool.and(Run.subKeys(cs, cs2), Bool.and(Run.subRets(rs, rs2), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys)))), C.desc_refl(seen),
    Lemma.and_true_intro(Run.subKeys(cs, cs2), Bool.and(Run.subRets(rs, rs2), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys))), hc,
      Lemma.and_true_intro(Run.subRets(rs, rs2), Bool.and(Run.subPops(ps, ps), Core.allIn(ys, ys)), hr,
        Lemma.and_true_intro(Run.subPops(ps, ps), Core.allIn(ys, ys), pop_refl(ps), C.step_refl(ys)))))

# The known cluster: the new return edge meets every pop of it.
def call_known3(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat, +t: Gll.GState,
  +kk: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool},
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  +hp: {Check.edgePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, t) == True{} : Bool},
  p4: AddsB4(grammar, input, Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}, t),
  +ec: {Check.clustersOf(t) == cs : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == ps : +List<Gll.Pop>})
  -> Out(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, t, Bool.and(Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(t)), Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Check.returnsOf(t)))):
  match p4:
    case (+g0, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      +key = {Gll.CKey{x, i} : Gll.CKey}
      +edge = {Gll.Edge{q, dot, k} : Gll.Edge}
      +rs2 = {Gll.Ret{key, edge} <> rs : +List<Gll.Ret>}
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +s0 = {Gll.GState{seen, todo, cs, rs2, ps, ys} : Gll.GState}
      +g = grows_trans(s, s0, t, grows_parts(seen, todo, cs, cs, rs, rs2, ps, ys, key_refl(cs), ret_weaken(rs, key, edge, rs, ret_refl(rs))), g0)
      +qt = List.append(&2, Gll.Desc, extra, Run.todoOf(t))
      +inv = inv_join(extra, pred, grammar, input, t,
        queued_new(Check.seenOf(t), seen, qt, grammar, input, t, nq_widen(Check.seenOf(t), seen, extra, Run.todoOf(t), nq),
          queued_grow(seen, List.append(&2, Gll.Desc, extra, todo), qt, grammar, input, s, t, g, sub_app(extra, todo, Run.todoOf(t), st), h1)),
        clusters_to(pred, grammar, input, t, Check.clustersOf(t), cs, ec, clusters_grow(cs, pred, grammar, input, s, t, g, h2)),
        returns_to(grammar, input, t, Check.returnsOf(t), rs2, Check.popsOf(t), ps, er, ep,
          Lemma.and_true_intro(Check.edgePops(ps, grammar, key, edge, t), Check.allReturns(rs, grammar, ps, t), hp, returns_grow(rs, grammar, input, ps, s, t, g, h3))),
        pops_keyed_to(Check.popsOf(t), ps, Check.clustersOf(t), cs, ep, ec, h4),
        descs_keyed_to(Check.seenOf(t), grammar, input, Check.clustersOf(t), cs, ec, keyed_new(Check.seenOf(t), seen, grammar, input, cs, nk, h5)),
        rets_keyed_to(grammar, input, Check.returnsOf(t), rs2, Check.clustersOf(t), cs, er, ec, Lemma.and_true_intro(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), Run.retsKeyed(rs, grammar, cs), ke, h6)),
        todo_seen(Run.todoOf(t), todo, seen, Check.seenOf(t), nt, h7, grows_seen(s, t, g)),
        bounded_new(Check.seenOf(t), seen, grammar, input, nb, h8),
        rets_bounded_to(grammar, input, Check.returnsOf(t), rs2, er, Lemma.and_true_intro(Run.edgeBound(edge, grammar, input), Run.retsBounded(rs, grammar, input), be, h9)),
        pops_bounded_to(input, Check.popsOf(t), ps, ep, h10), steps_bounded_new(Check.stepsOf(t), ys, grammar, input, ns, h11))
      (inv, (call_post(t, key, edge, cs, rs2, ec, er, kk, ret_here(key, edge, rs)), (g, ms)))

def key_here(+key: Gll.CKey, +cs: +List<Gll.CKey>) -> {Gll.keyIn(key, key <> cs) == True{} : Bool}:
  Lemma.or_true_left_intro(Gll.keyEq(key, key), Gll.keyIn(key, cs), key_eq_refl(key))

# A new cluster: its seeds are started, and its return edge meets no pop yet.
def call_new3(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat, +t: Gll.GState,
  +nkk: {Gll.keyIn(Gll.CKey{x, i}, cs) == False{} : Bool},
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  +hs: {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), t) == True{} : Bool},
  p4: AddsB4(grammar, input, Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}, t),
  +ec: {Check.clustersOf(t) == Gll.CKey{x, i} <> cs : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == ps : +List<Gll.Pop>})
  -> Out(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, t, Bool.and(Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(t)), Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Check.returnsOf(t)))):
  match p4:
    case (+g0, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      +key = {Gll.CKey{x, i} : Gll.CKey}
      +edge = {Gll.Edge{q, dot, k} : Gll.Edge}
      +cs2 = {key <> cs : +List<Gll.CKey>}
      +rs2 = {Gll.Ret{key, edge} <> rs : +List<Gll.Ret>}
      +wk = key_weaken(cs, key, cs, key_refl(cs))
      +s = {Gll.GState{seen, todo, cs, rs, ps, ys} : Gll.GState}
      +s0 = {Gll.GState{seen, todo, cs2, rs2, ps, ys} : Gll.GState}
      +g = grows_trans(s, s0, t, grows_parts(seen, todo, cs, cs2, rs, rs2, ps, ys, wk, ret_weaken(rs, key, edge, rs, ret_refl(rs))), g0)
      +qt = List.append(&2, Gll.Desc, extra, Run.todoOf(t))
      +sd = Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i)
      +inv = inv_join(extra, pred, grammar, input, t,
        queued_new(Check.seenOf(t), seen, qt, grammar, input, t, nq_widen(Check.seenOf(t), seen, extra, Run.todoOf(t), nq),
          queued_grow(seen, List.append(&2, Gll.Desc, extra, todo), qt, grammar, input, s, t, g, sub_app(extra, todo, Run.todoOf(t), st), h1)),
        clusters_to(pred, grammar, input, t, Check.clustersOf(t), cs2, ec,
          Lemma.and_true_intro(Check.allSeen(sd, t), Check.allClusters(cs, pred, grammar, input, t), hs, clusters_grow(cs, pred, grammar, input, s, t, g, h2))),
        returns_to(grammar, input, t, Check.returnsOf(t), rs2, Check.popsOf(t), ps, er, ep,
          Lemma.and_true_intro(Check.edgePops(ps, grammar, key, edge, t), Check.allReturns(rs, grammar, ps, t), pops_miss(ps, grammar, input, x, i, edge, t, cs, h4, nkk), returns_grow(rs, grammar, input, ps, s, t, g, h3))),
        pops_keyed_to(Check.popsOf(t), ps, Check.clustersOf(t), cs2, ep, ec, pops_keyed_grow(ps, cs, cs2, wk, h4)),
        descs_keyed_to(Check.seenOf(t), grammar, input, Check.clustersOf(t), cs2, ec, keyed_new(Check.seenOf(t), seen, grammar, input, cs2, nk, descs_keyed_grow(seen, grammar, input, cs, cs2, wk, h5))),
        rets_keyed_to(grammar, input, Check.returnsOf(t), rs2, Check.clustersOf(t), cs2, er, ec,
          Lemma.and_true_intro(Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs2), Run.retsKeyed(rs, grammar, cs2),
            Lemma.or_true_right_intro(Gll.keyEq(Gll.CKey{Gll.lhsOf(grammar, q), k}, key), Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs), ke),
            rets_keyed_grow(rs, grammar, input, cs, cs2, wk, h6))),
        todo_seen(Run.todoOf(t), todo, seen, Check.seenOf(t), nt, h7, grows_seen(s, t, g)),
        bounded_new(Check.seenOf(t), seen, grammar, input, nb, h8),
        rets_bounded_to(grammar, input, Check.returnsOf(t), rs2, er, Lemma.and_true_intro(Run.edgeBound(edge, grammar, input), Run.retsBounded(rs, grammar, input), be, h9)),
        pops_bounded_to(input, Check.popsOf(t), ps, ep, h10), steps_bounded_new(Check.stepsOf(t), ys, grammar, input, ns, h11))
      (inv, (call_post(t, key, edge, cs2, rs2, ec, er, key_here(key, cs), ret_here(key, edge, rs)), (g, ms)))

def CallOut(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat) -> Type:
  Out(extra, pred, grammar, input, s, t, Bool.and(Gll.keyIn(Gll.CKey{x, i}, Check.clustersOf(t)), Check.retIn(Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Check.returnsOf(t))))

def call_known2(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat,
  +kk: {Gll.keyIn(Gll.CKey{x, i}, cs) == True{} : Bool},
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  p: Adds(grammar, input, Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}, Gll.resumePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys})) &
    {Check.edgePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Gll.resumePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys})) == True{} : Bool})
  -> CallOut(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.resumePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}), x, i, q, dot, k):
  match p:
    case ((+b, (+ec, (+er, ep))), +hp):
      +s0 = {Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys} : Gll.GState}
      +t = Gll.resumePops(ps, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, s0)
      call_known3(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, t, kk, ke, be, bi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hp, addsb_split(grammar, input, s0, t, b), ec, er, ep)

def call_new2(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat,
  +nkk: {Gll.keyIn(Gll.CKey{x, i}, cs) == False{} : Bool},
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool},
  p: Adds(grammar, input, Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}, Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys})) &
    {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys})) == True{} : Bool})
  -> CallOut(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys}), x, i, q, dot, k):
  match p:
    case ((+b, (+ec, (+er, ep))), +hs):
      +s0 = {Gll.GState{seen, todo, Gll.CKey{x, i} <> cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys} : Gll.GState}
      +t = Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), s0)
      call_new3(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, t, nkk, ke, be, bi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hs, addsb_split(grammar, input, s0, t, b), ec, er, ep)

def call_pick(known: Bool, +extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat,
  +ek: {Gll.keyIn(Gll.CKey{x, i}, cs) == known : Bool},
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +h1: {Run.queuedOk(seen, List.append(&2, Gll.Desc, extra, todo), grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, todo, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(todo, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool})
  -> CallOut(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys},
       Gll.callPick(known, grammar, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), Gll.GState{seen, todo, cs, rs, ps, ys}), x, i, q, dot, k):
  match known:
    case True{}:
      +s0 = {Gll.GState{seen, todo, cs, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys} : Gll.GState}
      call_known2(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, ek, ke, be, bi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        resume_pops(ps, grammar, input, Gll.CKey{x, i}, Gll.Edge{q, dot, k}, s0, ke, be, h10, bi))
    case False{}:
      +cs2 = {Gll.CKey{x, i} <> cs : +List<Gll.CKey>}
      +s0 = {Gll.GState{seen, todo, cs2, Gll.Ret{Gll.CKey{x, i}, Gll.Edge{q, dot, k}} <> rs, ps, ys} : Gll.GState}
      call_new2(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, ek, ke, be, bi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        with_descs(Gll.productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), grammar, input, s0,
          seeds_keyed(grammar, 0n, grammar, input, pred, Core.tokAt(input, i), x, i, cs2, {==}, key_here(Gll.CKey{x, i}, cs)),
          seeds_bounded(grammar, 0n, grammar, input, pred, Core.tokAt(input, i), x, i, {==}, bi)))

def call_parts(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +todo: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +x: Nat, +i: Nat, +q: Nat, +dot: Nat, +k: Nat,
  +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, cs) == True{} : Bool},
  +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool},
  +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  p: Inv6(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}))
  -> CallOut(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, Gll.call(pred, grammar, input, x, i, Gll.Edge{q, dot, k}, Gll.GState{seen, todo, cs, rs, ps, ys}), x, i, q, dot, k):
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      call_pick(Gll.keyIn(Gll.CKey{x, i}, cs), extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, {==}, ke, be, bi, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11)

# Calling x at i keeps the invariant, and gives the cluster and the return edge.
law call_spec:
  for +extra: +List<Gll.Desc>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +dot: Nat
  for +k: Nat
  for s: Gll.GState
  for +ke: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool}
  for +be: {Run.edgeBound(Gll.Edge{q, dot, k}, grammar, input) == True{} : Bool}
  for +bi: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool}
  for +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}
  CallOut(extra, pred, grammar, input, s, Gll.call(pred, grammar, input, x, i, Gll.Edge{q, dot, k}, s), x, i, q, dot, k)

def call_spec(extra, pred, grammar, input, x, i, q, dot, k, s, ke, be, bi, h):
  match s:
    case Gll.GState{+seen, +todo, +cs, +rs, +ps, +ys}:
      call_parts(extra, pred, grammar, input, seen, todo, cs, rs, ps, ys, x, i, q, dot, k, ke, be, bi, inv_split(extra, pred, grammar, input, Gll.GState{seen, todo, cs, rs, ps, ys}, h))

# ======== ONE STEP OF THE LOOP ========

def adds_out(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s: Gll.GState, +t: Gll.GState, +post: Bool,
  +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool},
  p: Adds(grammar, input, s, t) & {post == True{} : Bool}) -> Out(extra, pred, grammar, input, s, t, post):
  match p:
    case ((+b, (+ec, (+er, ep))), +hp):
      (adds_inv(extra, pred, grammar, input, s, t, (b, (ec, (er, ep))), h), (hp, (adds_grows(grammar, input, s, t, b), adds_meas(grammar, input, s, t, b))))

def key_moved(+key: Gll.CKey, +a: +List<Gll.CKey>, +b: +List<Gll.CKey>, +e: {a == b : +List<Gll.CKey>},
  +h: {Gll.keyIn(key, b) == True{} : Bool}) -> {Gll.keyIn(key, a) == True{} : Bool}:
  %Equal.sym(+List<Gll.CKey>, a, b, e) : {Gll.keyIn(key, _) == True{} : Bool}
  h

def end_three(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +t1: Gll.GState, +t: Gll.GState,
  +g1: {Run.grows(s, t1) == True{} : Bool}, +eok1: {Check.emptyOk(dot, q, k, i, t1) == True{} : Bool},
  +inv: {Run.invWith(extra, pred, grammar, input, t) == True{} : Bool},
  +hp: {Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(t)) == True{} : Bool},
  +g2: {Run.grows(t1, t) == True{} : Bool},
  +m1: {Nat.is_le(Run.meas(grammar, input, t1), Run.meas(grammar, input, s)) == True{} : Bool}, +m2: {Nat.is_le(Run.meas(grammar, input, t), Run.meas(grammar, input, t1)) == True{} : Bool})
  -> Out(extra, pred, grammar, input, s, t, Bool.and(Check.emptyOk(dot, q, k, i, t), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(t)))):
  (inv, (Lemma.and_true_intro(Check.emptyOk(dot, q, k, i, t), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(t)), empty_grow(dot, q, k, i, t1, t, g2, eok1), hp),
    (grows_trans(s, t1, t, g1, g2), Lemma.le_trans(Run.meas(grammar, input, t), Run.meas(grammar, input, t1), Run.meas(grammar, input, s), m2, m1))))

def end_two(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState, +t1: Gll.GState,
  +g1: {Run.grows(s, t1) == True{} : Bool}, +eok1: {Check.emptyOk(dot, q, k, i, t1) == True{} : Bool}, +m1: {Nat.is_le(Run.meas(grammar, input, t1), Run.meas(grammar, input, s)) == True{} : Bool},
  o: Out(extra, pred, grammar, input, t1, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1)))))
  -> Out(extra, pred, grammar, input, s, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1),
       Bool.and(Check.emptyOk(dot, q, k, i, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1)), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1))))):
  match o:
    case (+inv, (+hp, (+g2, m2))):
      end_three(extra, pred, grammar, input, q, dot, k, i, s, t1, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, t1), g1, eok1, inv, hp, g2, m1, m2)

def end_one(+extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState,
  +kq: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool},
  +bj: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +bk: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool},
  p: Adds(grammar, input, s, Gll.emptyIf(dot, q, k, i, s)) & {Check.emptyOk(dot, q, k, i, Gll.emptyIf(dot, q, k, i, s)) == True{} : Bool})
  -> Out(extra, pred, grammar, input, s, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Gll.emptyIf(dot, q, k, i, s)),
       Bool.and(Check.emptyOk(dot, q, k, i, Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Gll.emptyIf(dot, q, k, i, s))), Gll.popIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Check.popsOf(Gll.leave(grammar, Gll.CKey{Gll.lhsOf(grammar, q), k}, i, Gll.emptyIf(dot, q, k, i, s)))))):
  match p:
    case ((+b, (+ec, (+er, ep))), +eok):
      +t1 = Gll.emptyIf(dot, q, k, i, s)
      +key = {Gll.CKey{Gll.lhsOf(grammar, q), k} : Gll.CKey}
      end_two(extra, pred, grammar, input, q, dot, k, i, s, t1, adds_grows(grammar, input, s, t1, b), eok, adds_meas(grammar, input, s, t1, b),
        leave_spec(extra, pred, grammar, input, key, i, t1, key_moved(key, Check.clustersOf(t1), Check.clustersOf(s), ec, kq), bj, bk,
          adds_inv(extra, pred, grammar, input, s, t1, (b, (ec, (er, ep))), h)))

def item_case(item: Maybe<&2, Core.Sym>, +extra: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +dot: Nat, +k: Nat, +i: Nat, +s: Gll.GState,
  +kq: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool},
  +bd: {Run.descBound(Gll.Desc{q, dot, k, i}, grammar, input) == True{} : Bool},
  +hA: {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) == True{} : Bool},
  +hK: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool},
  +hI: {Nat.is_le(i, List.length(&2, Nat, input)) == True{} : Bool},
  +ie: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == item : Maybe<&2, Core.Sym>},
  +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool})
  -> Out(extra, pred, grammar, input, s, Gll.stepItem(item, pred, grammar, input, q, dot, k, i, s), Check.itemOk(item, grammar, input, q, dot, k, i, Gll.stepItem(item, pred, grammar, input, q, dot, k, i, s))):
  match item:
    case Some{Core.Terminal{+tk}}:
      +b = Core.tokIs(Core.tokAt(input, i), tk)
      +hd = nth_lt(Core.rhsOf(grammar, q), dot, Core.Terminal{tk}, ie)
      adds_out(extra, pred, grammar, input, s, Gll.matchToken(b, q, dot, k, i, s), Check.tokenOk(b, q, dot, k, i, Gll.matchToken(b, q, dot, k, i, s)), h,
        match_token(b, grammar, input, q, dot, k, i, s, kq, hI, hb => token_bound(grammar, input, q, dot, k, i, tk, hA, hd, hK, hb)))
    case Some{Core.Nonterminal{+x, +need}}:
      +hd = nth_lt(Core.rhsOf(grammar, q), dot, Core.Nonterminal{x, need}, ie)
      +a = {Nat.is_le(1n+dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
      call_spec(extra, pred, grammar, input, x, i, q, dot, k, s, kq,
        Lemma.and_true_intro(Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)), Bool.and(a, Nat.is_le(k, List.length(&2, Nat, input))), hA, Lemma.and_true_intro(a, Nat.is_le(k, List.length(&2, Nat, input)), hd, hK)),
        hI, h)
    case None{}:
      end_one(extra, pred, grammar, input, q, dot, k, i, s, kq, hI, hK, h, empty_if(dot, grammar, input, q, k, i, s, bd, hI))

law item_spec:
  for item: Maybe<&2, Core.Sym>
  for +extra: +List<Gll.Desc>
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +s: Gll.GState
  for +kq: {Gll.keyIn(Gll.CKey{Gll.lhsOf(grammar, q), k}, Check.clustersOf(s)) == True{} : Bool}
  for +bd: {Run.descBound(Gll.Desc{q, dot, k, i}, grammar, input) == True{} : Bool}
  for +ie: {Gll.nthSym(Core.rhsOf(grammar, q), dot) == item : Maybe<&2, Core.Sym>}
  for +h: {Run.invWith(extra, pred, grammar, input, s) == True{} : Bool}
  Out(extra, pred, grammar, input, s, Gll.stepItem(item, pred, grammar, input, q, dot, k, i, s), Check.itemOk(item, grammar, input, q, dot, k, i, Gll.stepItem(item, pred, grammar, input, q, dot, k, i, s)))

def item_spec(item, extra, pred, grammar, input, q, dot, k, i, s, kq, bd, ie, h):
  +n = List.length(&2, Nat, input)
  +A = {Nat.is_le(1n+q, List.length(&2, Core.Production, grammar)) : Bool}
  +Bd = {Nat.is_le(dot, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +K = {Nat.is_le(k, n) : Bool}
  +I = {Nat.is_le(i, n) : Bool}
  +r1 = Lemma.and_true_right_side(A, Bool.and(Bd, Bool.and(K, I)), bd)
  +r2 = Lemma.and_true_right_side(Bd, Bool.and(K, I), r1)
  +hA = Lemma.and_true_left(A, Bool.and(Bd, Bool.and(K, I)), bd)
  +hK = Lemma.and_true_left(K, I, r2)
  +hI = Lemma.and_true_right_side(K, I, r2)
  item_case(item, extra, pred, grammar, input, q, dot, k, i, s, kq, bd, hA, hK, hI, ie, h)

# ======== THE LOOP ========

def done_pick(+x: Gll.Desc, +d: Gll.Desc, +todo: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState,
  +hd: {Check.descOk(d, grammar, input, t) == True{} : Bool},
  cases: Either<{Gll.descEq(x, d) == True{} : Bool}, {Gll.descIn(x, todo) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, d, G.desc_eq_sound(x, d, e)) : {Bool.or(Gll.descIn(_, todo), Check.descOk(_, grammar, input, t)) == True{} : Bool}
      Lemma.or_true_right_intro(Gll.descIn(d, todo), Check.descOk(d, grammar, input, t), hd)
    case Inr{m}:
      Lemma.or_true_left_intro(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t), m)

def done_or(+x: Gll.Desc, +d: Gll.Desc, +todo: +List<Gll.Desc>, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState,
  +hd: {Check.descOk(d, grammar, input, t) == True{} : Bool},
  cases: Either<{Gll.descIn(x, d <> todo) == True{} : Bool}, {Check.descOk(x, grammar, input, t) == True{} : Bool}>) -> {Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t)) == True{} : Bool}:
  match cases:
    case Inl{m}:
      done_pick(x, d, todo, grammar, input, t, hd, Lemma.or_true_cases(Gll.descEq(x, d), Gll.descIn(x, todo), m))
    case Inr{h}:
      Lemma.or_true_right_intro(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t), h)

# The processed descriptor's work is done: it need not stay pending.
law pop_done:
  for ds: +List<Gll.Desc>
  for +d: Gll.Desc
  for +todo: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +t: Gll.GState
  for +h: {Run.queuedOk(ds, d <> todo, grammar, input, t) == True{} : Bool}
  for +hd: {Check.descOk(d, grammar, input, t) == True{} : Bool}
  {Run.queuedOk(ds, todo, grammar, input, t) == True{} : Bool}

def pop_done(ds, d, todo, grammar, input, t, h, hd):
  match ds:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = {Bool.or(Gll.descIn(x, d <> todo), Check.descOk(x, grammar, input, t)) : Bool}
      Lemma.and_true_intro(Bool.or(Gll.descIn(x, todo), Check.descOk(x, grammar, input, t)), Run.queuedOk(rest, todo, grammar, input, t),
        done_or(x, d, todo, grammar, input, t, hd, Lemma.or_true_cases(Gll.descIn(x, d <> todo), Check.descOk(x, grammar, input, t), Lemma.and_true_left(hx, Run.queuedOk(rest, d <> todo, grammar, input, t), h))),
        pop_done(rest, d, todo, grammar, input, t, Lemma.and_true_right_side(hx, Run.queuedOk(rest, d <> todo, grammar, input, t), h), hd))

def finish_parts(+d: Gll.Desc, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState,
  +hd: {Check.descOk(d, grammar, input, t) == True{} : Bool},
  p: Inv6([d], pred, grammar, input, t)) -> {Run.inv(pred, grammar, input, t) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      inv_join([], pred, grammar, input, t, pop_done(Check.seenOf(t), d, Run.todoOf(t), grammar, input, t, h1, hd), h2, h3, h4, h5, h6, h7, h8, h9, h10, h11)

def finish(+q: Nat, +dot: Nat, +k: Nat, +i: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s0: Gll.GState,
  o: Out([Gll.Desc{q, dot, k, i}], pred, grammar, input, s0, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0),
    Check.itemOk(Gll.nthSym(Core.rhsOf(grammar, q), dot), grammar, input, q, dot, k, i, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0))))
  -> {Run.inv(pred, grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0)) == True{} : Bool} & {Run.grows(s0, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0)) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0)), Run.meas(grammar, input, s0)) == True{} : Bool}:
  match o:
    case (+inv, (+hd, (+g, m))):
      +t = Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, s0)
      (finish_parts(Gll.Desc{q, dot, k, i}, pred, grammar, input, t, hd, inv_split([Gll.Desc{q, dot, k, i}], pred, grammar, input, t, inv)), (g, m))

def start_core(+q: Nat, +dot: Nat, +k: Nat, +i: Nat, +rest: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +h1: {Run.queuedOk(seen, Gll.Desc{q, dot, k, i} <> rest, grammar, input, Gll.GState{seen, Gll.Desc{q, dot, k, i} <> rest, cs, rs, ps, ys}) == True{} : Bool},
  +h2: {Check.allClusters(cs, pred, grammar, input, Gll.GState{seen, Gll.Desc{q, dot, k, i} <> rest, cs, rs, ps, ys}) == True{} : Bool},
  +h3: {Check.allReturns(rs, grammar, ps, Gll.GState{seen, Gll.Desc{q, dot, k, i} <> rest, cs, rs, ps, ys}) == True{} : Bool},
  +h4: {Run.popsKeyed(ps, cs) == True{} : Bool},
  +h5: {Run.descsKeyed(seen, grammar, cs) == True{} : Bool},
  +h6: {Run.retsKeyed(rs, grammar, cs) == True{} : Bool},
  +h7: {Run.subDescs(Gll.Desc{q, dot, k, i} <> rest, seen) == True{} : Bool},
  +h8: {Run.descsBounded(seen, grammar, input) == True{} : Bool},
  +h9: {Run.retsBounded(rs, grammar, input) == True{} : Bool},
  +h10: {Run.popsBounded(ps, input) == True{} : Bool},
  +h11: {Run.stepsBounded(ys, grammar, input) == True{} : Bool})
  -> {Run.inv(pred, grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Run.grows(Gll.GState{seen, rest, cs, rs, ps, ys}, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})), Run.meas(grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool}:
    +dd = {Gll.Desc{q, dot, k, i} : Gll.Desc}
    +s = {Gll.GState{seen, dd <> rest, cs, rs, ps, ys} : Gll.GState}
    +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
    +g = same_grows(seen, seen, dd <> rest, rest, cs, rs, ps, ys, ys, C.desc_refl(seen), C.step_refl(ys))
    +inD = Lemma.and_true_left(Gll.descIn(dd, seen), Run.subDescs(rest, seen), h7)
    +kq = keyed_at(seen, grammar, input, cs, dd, inD, h5)
    +inv0 = inv_join([dd], pred, grammar, input, s0, queued_grow(seen, dd <> rest, dd <> rest, grammar, input, s, s0, g, C.desc_refl(dd <> rest), h1),
      clusters_grow(cs, pred, grammar, input, s, s0, g, h2), returns_grow(rs, grammar, input, ps, s, s0, g, h3), h4, h5, h6,
      Lemma.and_true_right_side(Gll.descIn(dd, seen), Run.subDescs(rest, seen), h7), h8, h9, h10, h11)
    finish(q, dot, k, i, pred, grammar, input, s0,
      item_spec(Gll.nthSym(Core.rhsOf(grammar, q), dot), [dd], pred, grammar, input, q, dot, k, i, s0, kq, bounded_at(seen, grammar, input, dd, inD, h8), {==}, inv0))

def start_parts(+q: Nat, +dot: Nat, +k: Nat, +i: Nat, +rest: +List<Gll.Desc>, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +seen: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  p: Inv6([], pred, grammar, input, Gll.GState{seen, Gll.Desc{q, dot, k, i} <> rest, cs, rs, ps, ys}))
  -> {Run.inv(pred, grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Run.grows(Gll.GState{seen, rest, cs, rs, ps, ys}, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(Gll.Desc{q, dot, k, i}, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})), Run.meas(grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      start_core(q, dot, k, i, rest, pred, grammar, input, seen, cs, rs, ps, ys, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11)

# One iteration of the loop keeps the invariant.
law step_inv:
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
  for +h: {Run.inv(pred, grammar, input, Gll.GState{seen, d <> rest, cs, rs, ps, ys}) == True{} : Bool}
  {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Run.grows(Gll.GState{seen, rest, cs, rs, ps, ys}, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(d, pred, grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})), Run.meas(grammar, input, Gll.GState{seen, rest, cs, rs, ps, ys})) == True{} : Bool}

def step_inv(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h):
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      start_parts(q, dot, k, i, rest, pred, grammar, input, seen, cs, rs, ps, ys, inv_split([], pred, grammar, input, Gll.GState{seen, Gll.Desc{q, dot, k, i} <> rest, cs, rs, ps, ys}, h))

def runState(r: Gll.GRun) -> Gll.GState:
  match r:
    case Gll.GDone{+s}:
      s
    case Gll.OutOfFuel{+s}:
      s

def isDone(r: Gll.GRun) -> Bool:
  match r:
    case Gll.GDone{s}:
      True{}
    case Gll.OutOfFuel{s}:
      False{}

law queued_nil:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +h: {Run.queuedOk(ds, [], grammar, input, s) == True{} : Bool}
  {Check.allDescs(ds, grammar, input, s) == True{} : Bool}

def queued_nil(ds, grammar, input, s, h):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +hd = Lemma.and_true_left(Bool.or(False{}, Check.descOk(d, grammar, input, s)), Run.queuedOk(rest, [], grammar, input, s), h)
      Lemma.and_true_intro(Check.descOk(d, grammar, input, s), Check.allDescs(rest, grammar, input, s), hd,
        queued_nil(rest, grammar, input, s, Lemma.and_true_right_side(Bool.or(False{}, Check.descOk(d, grammar, input, s)), Run.queuedOk(rest, [], grammar, input, s), h)))

def end_closed(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +seen: +List<Gll.Desc>, +cs: +List<Gll.CKey>, +rs: +List<Gll.Ret>, +ps: +List<Gll.Pop>, +ys: +List<Core.Bsr>,
  +root: {Gll.keyIn(key, cs) == True{} : Bool},
  p: Inv6([], pred, grammar, input, Gll.GState{seen, [], cs, rs, ps, ys}))
  -> {Bool.and(Check.closedWith(pred, grammar, input, Gll.GState{seen, [], cs, rs, ps, ys}), Gll.keyIn(key, cs)) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      +s = {Gll.GState{seen, [], cs, rs, ps, ys} : Gll.GState}
      Lemma.and_true_intro(Check.closedWith(pred, grammar, input, s), Gll.keyIn(key, cs),
        Lemma.and_true_intro(Check.allDescs(seen, grammar, input, s), Bool.and(Check.allClusters(cs, pred, grammar, input, s), Check.allReturns(rs, grammar, ps, s)),
          queued_nil(seen, grammar, input, s, h1), Lemma.and_true_intro(Check.allClusters(cs, pred, grammar, input, s), Check.allReturns(rs, grammar, ps, s), h2, h3)), root)

def ends_at(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +a: Gll.GState, +b: Gll.GState, +e: {a == b : Gll.GState},
  +h: {Bool.and(Check.closedWith(pred, grammar, input, a), Gll.keyIn(key, Check.clustersOf(a))) == True{} : Bool})
  -> {Bool.and(Check.closedWith(pred, grammar, input, b), Gll.keyIn(key, Check.clustersOf(b))) == True{} : Bool}:
  %e : {Bool.and(Check.closedWith(pred, grammar, input, _), Gll.keyIn(key, Check.clustersOf(_))) == True{} : Bool}
  h

def run_next(+d: Gll.Desc, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +s0: Gll.GState, +t: Gll.GState,
  +root: {Gll.keyIn(key, Check.clustersOf(s0)) == True{} : Bool},
  p: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Run.grows(s0, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(d, pred, grammar, input, s0)), Run.meas(grammar, input, s0)) == True{} : Bool},
  later: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Gll.keyIn(key, Check.clustersOf(Gll.step(d, pred, grammar, input, s0))) == True{} : Bool} ->
    {Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(key, Check.clustersOf(t))) == True{} : Bool})
  -> {Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(key, Check.clustersOf(t))) == True{} : Bool}:
  match p:
    case (+inv, (+g, m)):
      later(inv, key_grow(s0, Gll.step(d, pred, grammar, input, s0), key, g, root))

# A run that finishes ends in a closed state that keeps the root cluster.
law run_ends:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +key: Gll.CKey
  for s: Gll.GState
  for +t: Gll.GState
  for +h: {Run.inv(pred, grammar, input, s) == True{} : Bool}
  for +root: {Gll.keyIn(key, Check.clustersOf(s)) == True{} : Bool}
  for +e: {Gll.run(fuel, pred, grammar, input, s) == Gll.GDone{t} : Gll.GRun}
  {Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(key, Check.clustersOf(t))) == True{} : Bool}

def run_ends(fuel, pred, grammar, input, key, s, t, h, root, e):
  match fuel s:
    case 0n +st:
      Empty.absurd({Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(key, Check.clustersOf(t))) == True{} : Bool},
        Lemma.false_is_not_true(Equal.cong(Gll.GRun, Bool, v => isDone(v), Gll.OutOfFuel{st}, Gll.GDone{t}, e)))
    case 1n+(+f) Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      +st = {Gll.GState{seen, [], cs, rs, ps, ys} : Gll.GState}
      ends_at(pred, grammar, input, key, st, t, Equal.cong(Gll.GRun, Gll.GState, v => runState(v), Gll.GDone{st}, Gll.GDone{t}, e),
        end_closed(pred, grammar, input, key, seen, cs, rs, ps, ys, root, inv_split([], pred, grammar, input, st, h)))
    case 1n+(+f) Gll.GState{+seen, Con{+d, +rest}, +cs, +rs, +ps, +ys}:
      +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      run_next(d, pred, grammar, input, key, s0, t, root, step_inv(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h),
        inv2 => r2 => run_ends(f, pred, grammar, input, key, Gll.step(d, pred, grammar, input, s0), t, inv2, r2, e))

# ======== THE START AND THE LAW ========

def initial4(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +key: Gll.CKey, +t: Gll.GState,
  +hs: {Check.allClusters([key], pred, grammar, input, t) == True{} : Bool},
  p4: AddsB4(grammar, input, Gll.GState{[], [], [key], [], [], []}, t),
  +ec: {Check.clustersOf(t) == [key] : +List<Gll.CKey>},
  +er: {Check.returnsOf(t) == [] : +List<Gll.Ret>},
  +ep: {Check.popsOf(t) == [] : +List<Gll.Pop>})
  -> {Run.inv(pred, grammar, input, t) == True{} : Bool} & {Gll.keyIn(key, Check.clustersOf(t)) == True{} : Bool}:
  match p4:
    case (+g, (+st, (+nq, (+nk, (+nt, (+nb, (+ns, ms))))))):
      (inv_join([], pred, grammar, input, t,
         queued_new(Check.seenOf(t), [], Run.todoOf(t), grammar, input, t, nq, {==}),
         clusters_to(pred, grammar, input, t, Check.clustersOf(t), [key], ec, hs),
         returns_to(grammar, input, t, Check.returnsOf(t), [], Check.popsOf(t), [], er, ep, {==}),
         pops_keyed_to(Check.popsOf(t), [], Check.clustersOf(t), [key], ep, ec, {==}),
         descs_keyed_to(Check.seenOf(t), grammar, input, Check.clustersOf(t), [key], ec, keyed_new(Check.seenOf(t), [], grammar, input, [key], nk, {==})),
         rets_keyed_to(grammar, input, Check.returnsOf(t), [], Check.clustersOf(t), [key], er, ec, {==}),
         todo_seen(Run.todoOf(t), [], [], Check.seenOf(t), nt, {==}, {==}),
         bounded_new(Check.seenOf(t), [], grammar, input, nb, {==}), rets_bounded_to(grammar, input, Check.returnsOf(t), [], er, {==}), pops_bounded_to(input, Check.popsOf(t), [], ep, {==}), steps_bounded_new(Check.stepsOf(t), [], grammar, input, ns, {==})),
       key_moved(key, Check.clustersOf(t), [key], ec, key_here(key, [])))

def initial3(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  p: Adds(grammar, input, Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []}, Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []})) &
    {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []})) == True{} : Bool})
  -> {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool}:
  match p:
    case ((+b, (+ec, (+er, ep))), +hs):
      +s0 = {Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []} : Gll.GState}
      +t = Run.initial(pred, grammar, start, input)
      initial4(pred, grammar, input, Gll.CKey{start, 0n}, t,
        Lemma.and_true_intro(Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), t), True{}, hs, {==}),
        addsb_split(grammar, input, s0, t, b), ec, er, ep)

# The engine's first state keeps the invariant and has the root cluster.
law initial_inv:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool}

def initial_inv(pred, grammar, start, input):
  +key = {Gll.CKey{start, 0n} : Gll.CKey}
  initial3(pred, grammar, start, input,
    with_descs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), grammar, input, Gll.GState{[], [], [key], [], [], []},
      seeds_keyed(grammar, 0n, grammar, input, pred, Core.tokAt(input, 0n), start, 0n, [key], {==}, key_here(key, [])),
      seeds_bounded(grammar, 0n, grammar, input, pred, Core.tokAt(input, 0n), start, 0n, {==}, Lemma.zero_le(List.length(&2, Nat, input)))))

def parse_from(+fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +t: Gll.GState,
  +e: {Gll.parseWith(fuel, pred, grammar, start, input) == Gll.GDone{t} : Gll.GRun},
  p: {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool})
  -> {Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(t))) == True{} : Bool}:
  match p:
    case (+h, root):
      run_ends(fuel, pred, grammar, input, Gll.CKey{start, 0n}, Run.initial(pred, grammar, start, input), t, h, root, e)

# THE ENGINE ENDS CLOSED: whenever the GLL engine finishes its work (with or without a
# predictor), its final state is closed for what the predictor admits and has the start
# symbol's cluster at 0. So the checked parsers hand out their sets whenever the engine
# finishes (`checked_answers`).
law engine_closed:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for +e: {Gll.parseWith(fuel, pred, grammar, start, input) == Gll.GDone{t} : Gll.GRun}
  {Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(t))) == True{} : Bool}

def engine_closed(fuel, pred, grammar, start, input, t, e):
  parse_from(fuel, pred, grammar, start, input, t, e, initial_inv(pred, grammar, start, input))

def answer_pick(b: Bool, +t: Gll.GState, +h: {b == True{} : Bool}) -> {Check.checkPick(b, t) == Some{Check.stepsOf(t)} : Maybe<&2, +List<Core.Bsr>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({None{} == Some{Check.stepsOf(t)} : Maybe<&2, +List<Core.Bsr>>}, Lemma.false_is_not_true(h))

# Whenever the engine finishes, the checked parser (with that predictor) answers with its steps.
law checked_answers:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for +e: {Gll.parseWith(fuel, pred, grammar, start, input) == Gll.GDone{t} : Gll.GRun}
  {Check.runCheckedWith(pred, Gll.GDone{t}, grammar, start, input) == Some{Check.stepsOf(t)} : Maybe<&2, +List<Core.Bsr>>}

def checked_answers(fuel, pred, grammar, start, input, t, e):
  answer_pick(Bool.and(Check.closedWith(pred, grammar, input, t), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(t))), t, engine_closed(fuel, pred, grammar, start, input, t, e))

# ======== THE ENGINE FINISHES ========
#
# The measure: descriptors within bounds not yet seen, plus the to-do list. Taking a
# descriptor off the list lowers it by one, and an iteration never raises it (each new
# descriptor is within bounds and unseen, so it leaves the first part as it joins the
# second). So 1 + the measure is enough fuel, and the measure starts at most at the size
# of the universe.

def run_more(+d: Gll.Desc, +f: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s0: Gll.GState,
  p: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Run.grows(s0, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(d, pred, grammar, input, s0)), Run.meas(grammar, input, s0)) == True{} : Bool},
  +hf: {Nat.is_le(1n+Run.meas(grammar, input, s0), f) == True{} : Bool},
  later: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Nat.is_le(1n+Run.meas(grammar, input, Gll.step(d, pred, grammar, input, s0)), f) == True{} : Bool} -> {isDone(Gll.run(f, pred, grammar, input, Gll.step(d, pred, grammar, input, s0))) == True{} : Bool})
  -> {isDone(Gll.run(f, pred, grammar, input, Gll.step(d, pred, grammar, input, s0))) == True{} : Bool}:
  match p:
    case (+inv, (+g, m)):
      +t = Gll.step(d, pred, grammar, input, s0)
      later(inv, Lemma.le_trans(1n+Run.meas(grammar, input, t), 1n+Run.meas(grammar, input, s0), f, m, hf))

def pop_meas(+grammar: +List<Core.Production>, +input: +List<Nat>, +seen: +List<Gll.Desc>, +rest: +List<Gll.Desc>, +f: Nat,
  +hf: {Nat.is_le(Nat.add(Run.countNot(Run.univ(grammar, input), seen), 1n+List.length(&2, Gll.Desc, rest)), f) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.add(Run.countNot(Run.univ(grammar, input), seen), List.length(&2, Gll.Desc, rest)), f) == True{} : Bool}:
  %Lemma.add_succ_right(Run.countNot(Run.univ(grammar, input), seen), List.length(&2, Gll.Desc, rest)) : {Nat.is_le(_, f) == True{} : Bool}
  hf

# With more fuel than the measure, a run that keeps the invariant finishes.
law run_done:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for s: Gll.GState
  for +h: {Run.inv(pred, grammar, input, s) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Run.meas(grammar, input, s), fuel) == True{} : Bool}
  {isDone(Gll.run(fuel, pred, grammar, input, s)) == True{} : Bool}

def run_done(fuel, pred, grammar, input, s, h, hf):
  match fuel s:
    case 0n +st:
      Empty.absurd({isDone(Gll.run(0n, pred, grammar, input, st)) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f) Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      {==}
    case 1n+(+f) Gll.GState{+seen, Con{+d, +rest}, +cs, +rs, +ps, +ys}:
      +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      run_more(d, f, pred, grammar, input, s0, step_inv(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h), pop_meas(grammar, input, seen, rest, f, hf),
        inv2 => hf2 => run_done(f, pred, grammar, input, Gll.step(d, pred, grammar, input, s0), inv2, hf2))

def initial_meas2(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  p: Adds(grammar, input, Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []}, Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []})) &
    {Check.allSeen(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.withDescs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []})) == True{} : Bool})
  -> {Nat.is_le(Run.meas(grammar, input, Run.initial(pred, grammar, start, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) == True{} : Bool}:
  match p:
    case ((+b, (+ec, (+er, ep))), +hs):
      +s0 = {Gll.GState{[], [], [Gll.CKey{start, 0n}], [], [], []} : Gll.GState}
      +t = Run.initial(pred, grammar, start, input)
      +U = Run.univ(grammar, input)
      Lemma.le_trans(Run.meas(grammar, input, t), Run.meas(grammar, input, s0), List.length(&2, Gll.Desc, U), adds_meas(grammar, input, s0, t, b), C.count_start(U))

# The engine's first state is measured at most by the size of the universe.
law initial_meas:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {Nat.is_le(Run.meas(grammar, input, Run.initial(pred, grammar, start, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) == True{} : Bool}

def initial_meas(pred, grammar, start, input):
  +key = {Gll.CKey{start, 0n} : Gll.CKey}
  initial_meas2(pred, grammar, start, input,
    with_descs(Gll.productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), grammar, input, Gll.GState{[], [], [key], [], [], []},
      seeds_keyed(grammar, 0n, grammar, input, pred, Core.tokAt(input, 0n), start, 0n, [key], {==}, key_here(key, [])),
      seeds_bounded(grammar, 0n, grammar, input, pred, Core.tokAt(input, 0n), start, 0n, {==}, Lemma.zero_le(List.length(&2, Nat, input)))))

def finish_from(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  p: {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool})
  -> {isDone(Gll.parseWith(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), pred, grammar, start, input)) == True{} : Bool}:
  match p:
    case (+h, root):
      run_done(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), pred, grammar, input, Run.initial(pred, grammar, start, input), h, initial_meas(pred, grammar, start, input))

# THE ENGINE FINISHES: with one more unit of fuel than there are descriptors within bounds
# (productions, dots, and two input positions), the GLL engine always finishes.
law gll_finishes:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {isDone(Gll.parseWith(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), pred, grammar, start, input)) == True{} : Bool}

def gll_finishes(pred, grammar, start, input):
  finish_from(pred, grammar, start, input, initial_inv(pred, grammar, start, input))

def isAnswer(m: Maybe<&2, +List<Core.Bsr>>) -> Bool:
  match m:
    case Some{ys}:
      True{}
    case None{}:
      False{}

def done_answers(r: Gll.GRun, +fuel: Nat, +pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  +er: {Gll.parseWith(fuel, pred, grammar, start, input) == r : Gll.GRun},
  +hd: {isDone(r) == True{} : Bool})
  -> {isAnswer(Check.runCheckedWith(pred, r, grammar, start, input)) == True{} : Bool}:
  match r:
    case Gll.GDone{+t}:
      %Equal.sym(Maybe<&2, +List<Core.Bsr>>, Check.runCheckedWith(pred, Gll.GDone{t}, grammar, start, input), Some{Check.stepsOf(t)}, checked_answers(fuel, pred, grammar, start, input, t, er)) : {isAnswer(_) == True{} : Bool}
      {==}
    case Gll.OutOfFuel{+st}:
      Empty.absurd({isAnswer(Check.runCheckedWith(pred, Gll.OutOfFuel{st}, grammar, start, input)) == True{} : Bool}, Lemma.false_is_not_true(hd))

# THE CHECKED PARSER ALWAYS ANSWERS: with that fuel, the checked parser (with any
# predictor) hands out its steps; together with gll_every_parse_step, it never fails.
law checked_always_answers:
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  {isAnswer(Check.runCheckedWith(pred, Gll.parseWith(1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)), pred, grammar, start, input), grammar, start, input)) == True{} : Bool}

def checked_always_answers(pred, grammar, start, input):
  +F = {1n+List.length(&2, Gll.Desc, Run.univ(grammar, input)) : Nat}
  done_answers(Gll.parseWith(F, pred, grammar, start, input), F, pred, grammar, start, input, {==}, gll_finishes(pred, grammar, start, input))

# ======== WHAT A FINISHED RUN KEEPS ========

def keep_next(+d: Gll.Desc, +pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +s0: Gll.GState, +t: Gll.GState,
  p: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Run.grows(s0, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} & {Nat.is_le(Run.meas(grammar, input, Gll.step(d, pred, grammar, input, s0)), Run.meas(grammar, input, s0)) == True{} : Bool},
  later: {Run.inv(pred, grammar, input, Gll.step(d, pred, grammar, input, s0)) == True{} : Bool} -> {Run.inv(pred, grammar, input, t) == True{} : Bool}) -> {Run.inv(pred, grammar, input, t) == True{} : Bool}:
  match p:
    case (+inv, (+g, m)):
      later(inv)

# A run that finishes ends in a state that keeps the invariant.
law run_keeps:
  for fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for s: Gll.GState
  for +t: Gll.GState
  for +h: {Run.inv(pred, grammar, input, s) == True{} : Bool}
  for +e: {Gll.run(fuel, pred, grammar, input, s) == Gll.GDone{t} : Gll.GRun}
  {Run.inv(pred, grammar, input, t) == True{} : Bool}

def run_keeps(fuel, pred, grammar, input, s, t, h, e):
  match fuel s:
    case 0n +st:
      Empty.absurd({Run.inv(pred, grammar, input, t) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Gll.GRun, Bool, v => isDone(v), Gll.OutOfFuel{st}, Gll.GDone{t}, e)))
    case 1n+(+f) Gll.GState{+seen, Nil{}, +cs, +rs, +ps, +ys}:
      +st = {Gll.GState{seen, [], cs, rs, ps, ys} : Gll.GState}
      %Equal.cong(Gll.GRun, Gll.GState, v => runState(v), Gll.GDone{st}, Gll.GDone{t}, e) : {Run.inv(pred, grammar, input, _) == True{} : Bool}
      h
    case 1n+(+f) Gll.GState{+seen, Con{+d, +rest}, +cs, +rs, +ps, +ys}:
      +s0 = {Gll.GState{seen, rest, cs, rs, ps, ys} : Gll.GState}
      keep_next(d, pred, grammar, input, s0, t, step_inv(d, rest, pred, grammar, input, seen, cs, rs, ps, ys, h),
        inv2 => run_keeps(f, pred, grammar, input, Gll.step(d, pred, grammar, input, s0), t, inv2, e))

def inv_first(+pred: Gll.Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  p: {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool} & {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(Run.initial(pred, grammar, start, input))) == True{} : Bool})
  -> {Run.inv(pred, grammar, input, Run.initial(pred, grammar, start, input)) == True{} : Bool}:
  match p:
    case (+h, root):
      h

def steps_part(+pred: Gll.Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +t: Gll.GState, p: Inv6([], pred, grammar, input, t))
  -> {Run.stepsBounded(Check.stepsOf(t), grammar, input) == True{} : Bool}:
  match p:
    case (+h1, (+h2, (+h3, (+h4, (+h5, (+h6, (+h7, (+h8, (+h9, (+h10, h11)))))))))):
      h11

# The steps of a finished run lie within the grammar and the input.
law final_steps_bounded:
  for +fuel: Nat
  for +pred: Gll.Pred
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for +e: {Gll.parseWith(fuel, pred, grammar, start, input) == Gll.GDone{t} : Gll.GRun}
  {Run.stepsBounded(Check.stepsOf(t), grammar, input) == True{} : Bool}

def final_steps_bounded(fuel, pred, grammar, start, input, t, e):
  steps_part(pred, grammar, input, t, inv_split([], pred, grammar, input, t,
    run_keeps(fuel, pred, grammar, input, Run.initial(pred, grammar, start, input), t, inv_first(pred, grammar, start, input, initial_inv(pred, grammar, start, input)), e)))

