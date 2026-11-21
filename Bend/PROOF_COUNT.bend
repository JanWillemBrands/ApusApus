import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G

# THE DESCRIPTORS THERE CAN BE: every descriptor within bounds is in the universe (RUN.bend),
# and the count of unseen ones drops when one of them is seen. Also small facts about
# descriptor lists and about adding up bounds.

def desc_eq_refl(d: Gll.Desc) -> {Gll.descEq(d, d) == True{} : Bool}:
  match d:
    case Gll.Desc{+q, +dt, +k, +i}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(k, k), Nat.is_eq(i, i)), Lemma.nat_eq_refl(dt),
          Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(i, i), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(i))))

def desc_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +ys: +List<Gll.Desc>,
  +hy: {Gll.descIn(y, ys) == True{} : Bool},
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Gll.descIn(x, ys) == True{} : Bool}) -> {Gll.descIn(x, ys) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e)) : {Gll.descIn(_, ys) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law desc_sub:
  for xs: +List<Gll.Desc>
  for +x: Gll.Desc
  for +ys: +List<Gll.Desc>
  for +m: {Gll.descIn(x, xs) == True{} : Bool}
  for +h: {Run.subDescs(xs, ys) == True{} : Bool}
  {Gll.descIn(x, ys) == True{} : Bool}

def desc_sub(xs, x, ys, m, h):
  match xs:
    case Nil{}:
      Empty.absurd({Gll.descIn(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      desc_pick(x, y, rest, ys, Lemma.and_true_left(Gll.descIn(y, ys), Run.subDescs(rest, ys), h), Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m),
        m2 => desc_sub(rest, x, ys, m2, Lemma.and_true_right_side(Gll.descIn(y, ys), Run.subDescs(rest, ys), h)))

def app_left_pick(+x: Gll.Desc, +y: Gll.Desc, +rest: +List<Gll.Desc>, +c: +List<Gll.Desc>,
  cases: Either<{Gll.descEq(x, y) == True{} : Bool}, {Gll.descIn(x, rest) == True{} : Bool}>,
  later: {Gll.descIn(x, rest) == True{} : Bool} -> {Gll.descIn(x, List.append(&2, Gll.Desc, rest, c)) == True{} : Bool})
  -> {Gll.descIn(x, y <> List.append(&2, Gll.Desc, rest, c)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Gll.descEq(x, y), Gll.descIn(x, List.append(&2, Gll.Desc, rest, c)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descEq(x, y), Gll.descIn(x, List.append(&2, Gll.Desc, rest, c)), later(m))

law desc_in_app_left:
  for a: +List<Gll.Desc>
  for +c: +List<Gll.Desc>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, a) == True{} : Bool}
  {Gll.descIn(x, List.append(&2, Gll.Desc, a, c)) == True{} : Bool}

def desc_in_app_left(a, c, x, m):
  match a:
    case Nil{}:
      Empty.absurd({Gll.descIn(x, c) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      app_left_pick(x, y, rest, c, Lemma.or_true_cases(Gll.descEq(x, y), Gll.descIn(x, rest), m), m2 => desc_in_app_left(rest, c, x, m2))

law desc_in_app_right:
  for a: +List<Gll.Desc>
  for +c: +List<Gll.Desc>
  for +x: Gll.Desc
  for +m: {Gll.descIn(x, c) == True{} : Bool}
  {Gll.descIn(x, List.append(&2, Gll.Desc, a, c)) == True{} : Bool}

def desc_in_app_right(a, c, x, m):
  match a:
    case Nil{}:
      m
    case Con{+y, +rest}:
      Lemma.or_true_right_intro(Gll.descEq(x, y), Gll.descIn(x, List.append(&2, Gll.Desc, rest, c)), desc_in_app_right(rest, c, x, m))

law desc_weaken:
  for xs: +List<Gll.Desc>
  for +y: Gll.Desc
  for +ys: +List<Gll.Desc>
  for +h: {Run.subDescs(xs, ys) == True{} : Bool}
  {Run.subDescs(xs, y <> ys) == True{} : Bool}

def desc_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, y <> ys), Run.subDescs(rest, y <> ys),
        Lemma.or_true_right_intro(Gll.descEq(x, y), Gll.descIn(x, ys), Lemma.and_true_left(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)),
        desc_weaken(rest, y, ys, Lemma.and_true_right_side(Gll.descIn(x, ys), Run.subDescs(rest, ys), h)))

law desc_refl:
  for xs: +List<Gll.Desc>
  {Run.subDescs(xs, xs) == True{} : Bool}

def desc_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Gll.descIn(x, x <> rest), Run.subDescs(rest, x <> rest), Lemma.or_true_left_intro(Gll.descEq(x, x), Gll.descIn(x, rest), desc_eq_refl(x)),
        desc_weaken(rest, x, rest, desc_refl(rest)))

# ======== ADDING UP BOUNDS ========

law le_zero_eq:
  for i: Nat
  for +h: {Nat.is_le(i, 0n) == True{} : Bool}
  {i == 0n : Nat}

def le_zero_eq(i, h):
  match i:
    case 0n:
      {==}
    case 1n+(+a):
      Empty.absurd({1n+a == 0n : Nat}, Lemma.false_is_not_true(h))

law le_pred_ne:
  for i: Nat
  for p: Nat
  for +h: {Nat.is_le(i, 1n+p) == True{} : Bool}
  for +ne: {Nat.is_eq(i, 1n+p) == False{} : Bool}
  {Nat.is_le(i, p) == True{} : Bool}

def le_pred_ne(i, p, h, ne):
  match i p:
    case 0n +p0:
      Lemma.zero_le(p0)
    case 1n+(+a) 0n:
      +ea = le_zero_eq(a, h)
      +ne2 = {(%ea : {Nat.is_eq(_, 0n) == False{} : Bool}
        ne) : {Nat.is_eq(0n, 0n) == False{} : Bool}}
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, Lemma.true_is_not_false(ne2))
    case 1n+(+a) 1n+(+b):
      le_pred_ne(a, b, h, ne)

law le_add_l:
  for a: Nat
  for c: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, c) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(c, b)) == True{} : Bool}

def le_add_l(a, c, b, h):
  match a c:
    case 0n +c0:
      Lemma.le_add_left(c0, b)
    case 1n+(+a2) 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+a2, b), Nat.add(0n, b)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case 1n+(+a2) 1n+(+c2):
      le_add_l(a2, c2, b, h)

law le_add_r:
  for a: Nat
  for +b: Nat
  for +d: Nat
  for +h: {Nat.is_le(b, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(a, d)) == True{} : Bool}

def le_add_r(a, b, d, h):
  match a:
    case 0n:
      h
    case 1n+(+a2):
      le_add_r(a2, b, d, h)

def le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, d) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  Lemma.le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), le_add_l(a, c, b, h1), le_add_r(c, b, d, h2))

# ======== THE UNIVERSE ========

def desc_head(+q: Nat, +d: Nat, +k: Nat, +i: Nat, +rest: +List<Gll.Desc>) -> {Gll.descIn(Gll.Desc{q, d, k, i}, Gll.Desc{q, d, k, i} <> rest) == True{} : Bool}:
  Lemma.or_true_left_intro(Gll.descEq(Gll.Desc{q, d, k, i}, Gll.Desc{q, d, k, i}), Gll.descIn(Gll.Desc{q, d, k, i}, rest), desc_eq_refl(Gll.Desc{q, d, k, i}))

def ui_pick(b: Bool, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +p: Nat,
  +eb: {Nat.is_eq(i, 1n+p) == b : Bool}, +h: {Nat.is_le(i, 1n+p) == True{} : Bool},
  later: {Nat.is_le(i, p) == True{} : Bool} -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uI(q, d, k, p)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uI(q, d, k, 1n+p)) == True{} : Bool}:
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(i, 1n+p, eb)
      %Equal.sym(Nat, i, 1n+p, e) : {Gll.descIn(Gll.Desc{q, d, k, _}, Run.uI(q, d, k, 1n+p)) == True{} : Bool}
      desc_head(q, d, k, 1n+p, Run.uI(q, d, k, p))
    case False{}:
      Lemma.or_true_right_intro(Gll.descEq(Gll.Desc{q, d, k, i}, Gll.Desc{q, d, k, 1n+p}), Gll.descIn(Gll.Desc{q, d, k, i}, Run.uI(q, d, k, p)), later(le_pred_ne(i, p, h, eb)))

law ui_mem:
  for m: Nat
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +h: {Nat.is_le(i, m) == True{} : Bool}
  {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uI(q, d, k, m)) == True{} : Bool}

def ui_mem(m, q, d, k, i, h):
  match m:
    case 0n:
      +e = le_zero_eq(i, h)
      %Equal.sym(Nat, i, 0n, e) : {Gll.descIn(Gll.Desc{q, d, k, _}, Run.uI(q, d, k, 0n)) == True{} : Bool}
      desc_head(q, d, k, 0n, [])
    case 1n+(+p):
      ui_pick(Nat.is_eq(i, 1n+p), q, d, k, i, p, {==}, h, h2 => ui_mem(p, q, d, k, i, h2))

def uk_pick(b: Bool, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +p: Nat, +n: Nat,
  +eb: {Nat.is_eq(k, 1n+p) == b : Bool}, +hk: {Nat.is_le(k, 1n+p) == True{} : Bool}, +hi: {Nat.is_le(i, n) == True{} : Bool},
  later: {Nat.is_le(k, p) == True{} : Bool} -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uK(q, d, p, n)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uK(q, d, 1n+p, n)) == True{} : Bool}:
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(k, 1n+p, eb)
      %Equal.sym(Nat, k, 1n+p, e) : {Gll.descIn(Gll.Desc{q, d, _, i}, Run.uK(q, d, 1n+p, n)) == True{} : Bool}
      desc_in_app_left(Run.uI(q, d, 1n+p, n), Run.uK(q, d, p, n), Gll.Desc{q, d, 1n+p, i}, ui_mem(n, q, d, 1n+p, i, hi))
    case False{}:
      desc_in_app_right(Run.uI(q, d, 1n+p, n), Run.uK(q, d, p, n), Gll.Desc{q, d, k, i}, later(le_pred_ne(k, p, hk, eb)))

law uk_mem:
  for m: Nat
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +n: Nat
  for +hk: {Nat.is_le(k, m) == True{} : Bool}
  for +hi: {Nat.is_le(i, n) == True{} : Bool}
  {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uK(q, d, m, n)) == True{} : Bool}

def uk_mem(m, q, d, k, i, n, hk, hi):
  match m:
    case 0n:
      %Equal.sym(Nat, k, 0n, le_zero_eq(k, hk)) : {Gll.descIn(Gll.Desc{q, d, _, i}, Run.uK(q, d, 0n, n)) == True{} : Bool}
      ui_mem(n, q, d, 0n, i, hi)
    case 1n+(+p):
      uk_pick(Nat.is_eq(k, 1n+p), q, d, k, i, p, n, {==}, hk, hi, h2 => uk_mem(p, q, d, k, i, n, h2, hi))

def ud_pick(b: Bool, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +p: Nat, +n: Nat,
  +eb: {Nat.is_eq(d, 1n+p) == b : Bool}, +hd: {Nat.is_le(d, 1n+p) == True{} : Bool}, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hi: {Nat.is_le(i, n) == True{} : Bool},
  later: {Nat.is_le(d, p) == True{} : Bool} -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uD(q, p, n)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uD(q, 1n+p, n)) == True{} : Bool}:
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(d, 1n+p, eb)
      %Equal.sym(Nat, d, 1n+p, e) : {Gll.descIn(Gll.Desc{q, _, k, i}, Run.uD(q, 1n+p, n)) == True{} : Bool}
      desc_in_app_left(Run.uK(q, 1n+p, n, n), Run.uD(q, p, n), Gll.Desc{q, 1n+p, k, i}, uk_mem(n, q, 1n+p, k, i, n, hk, hi))
    case False{}:
      desc_in_app_right(Run.uK(q, 1n+p, n, n), Run.uD(q, p, n), Gll.Desc{q, d, k, i}, later(le_pred_ne(d, p, hd, eb)))

law ud_mem:
  for m: Nat
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +n: Nat
  for +hd: {Nat.is_le(d, m) == True{} : Bool}
  for +hk: {Nat.is_le(k, n) == True{} : Bool}
  for +hi: {Nat.is_le(i, n) == True{} : Bool}
  {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uD(q, m, n)) == True{} : Bool}

def ud_mem(m, q, d, k, i, n, hd, hk, hi):
  match m:
    case 0n:
      %Equal.sym(Nat, d, 0n, le_zero_eq(d, hd)) : {Gll.descIn(Gll.Desc{q, _, k, i}, Run.uD(q, 0n, n)) == True{} : Bool}
      uk_mem(n, q, 0n, k, i, n, hk, hi)
    case 1n+(+p):
      ud_pick(Nat.is_eq(d, 1n+p), q, d, k, i, p, n, {==}, hd, hk, hi, h2 => ud_mem(p, q, d, k, i, n, h2, hk, hi))

def uq_pick(b: Bool, +grammar: +List<Core.Production>, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +p: Nat, +n: Nat,
  +eb: {Nat.is_eq(q, p) == b : Bool}, +hq: {Nat.is_le(1n+q, 1n+p) == True{} : Bool},
  +hd: {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hi: {Nat.is_le(i, n) == True{} : Bool},
  later: {Nat.is_le(1n+q, p) == True{} : Bool} -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uQ(grammar, p, n)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uQ(grammar, 1n+p, n)) == True{} : Bool}:
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(q, p, eb)
      +hdp = {(%e : {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, _))) == True{} : Bool}
        hd) : {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))) == True{} : Bool}}
      %Equal.sym(Nat, q, p, e) : {Gll.descIn(Gll.Desc{_, d, k, i}, Run.uQ(grammar, 1n+p, n)) == True{} : Bool}
      desc_in_app_left(Run.uD(p, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), n), Run.uQ(grammar, p, n), Gll.Desc{p, d, k, i},
        ud_mem(List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), p, d, k, i, n, hdp, hk, hi))
    case False{}:
      +ne = Equal.trans(Bool, Nat.is_eq(p, q), Nat.is_eq(q, p), False{}, Lemma.nat_eq_symm(p, q), eb)
      desc_in_app_right(Run.uD(p, List.length(&2, Core.Sym, Core.rhsOf(grammar, p)), n), Run.uQ(grammar, p, n), Gll.Desc{q, d, k, i}, later(Lemma.le_succ_ne(q, p, hq, ne)))

law uq_mem:
  for c: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +n: Nat
  for +hq: {Nat.is_le(1n+q, c) == True{} : Bool}
  for +hd: {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) == True{} : Bool}
  for +hk: {Nat.is_le(k, n) == True{} : Bool}
  for +hi: {Nat.is_le(i, n) == True{} : Bool}
  {Gll.descIn(Gll.Desc{q, d, k, i}, Run.uQ(grammar, c, n)) == True{} : Bool}

def uq_mem(c, grammar, q, d, k, i, n, hq, hd, hk, hi):
  match c:
    case 0n:
      Empty.absurd({Gll.descIn(Gll.Desc{q, d, k, i}, Run.uQ(grammar, 0n, n)) == True{} : Bool}, Lemma.false_is_not_true(hq))
    case 1n+(+p):
      uq_pick(Nat.is_eq(q, p), grammar, q, d, k, i, p, n, {==}, hq, hd, hk, hi, h2 => uq_mem(p, grammar, q, d, k, i, n, h2, hd, hk, hi))

# Every descriptor within bounds is in the universe.
law bound_mem:
  for dd: Gll.Desc
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +h: {Run.descBound(dd, grammar, input) == True{} : Bool}
  {Gll.descIn(dd, Run.univ(grammar, input)) == True{} : Bool}

def bound_mem(dd, grammar, input, h):
  match dd:
    case Gll.Desc{+q, +d, +k, +i}:
      +G = List.length(&2, Core.Production, grammar)
      +n = List.length(&2, Nat, input)
      +a = {Nat.is_le(1n+q, G) : Bool}
      +b = {Nat.is_le(d, List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
      +c = {Nat.is_le(k, n) : Bool}
      +e = {Nat.is_le(i, n) : Bool}
      +r1 = Lemma.and_true_right_side(a, Bool.and(b, Bool.and(c, e)), h)
      +r2 = Lemma.and_true_right_side(b, Bool.and(c, e), r1)
      uq_mem(G, grammar, q, d, k, i, n, Lemma.and_true_left(a, Bool.and(b, Bool.and(c, e)), h), Lemma.and_true_left(b, Bool.and(c, e), r1),
        Lemma.and_true_left(c, e, r2), Lemma.and_true_right_side(c, e, r2))

# ======== COUNTING THE UNSEEN ========

def pick_le_one(b: Bool) -> {Nat.is_le(Run.notPick(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_true(+u: Gll.Desc, +s2: +List<Gll.Desc>, +e: {Gll.descIn(u, s2) == True{} : Bool}) -> {Nat.is_le(Run.notPick(Gll.descIn(u, s2)), 0n) == True{} : Bool}:
  %Equal.sym(Bool, Gll.descIn(u, s2), True{}, e) : {Nat.is_le(Run.notPick(_), 0n) == True{} : Bool}
  {==}

def mono_pick(b: Bool, +u: Gll.Desc, +s1: +List<Gll.Desc>, +s2: +List<Gll.Desc>,
  +eb: {Gll.descIn(u, s1) == b : Bool}, +sub: {Run.subDescs(s1, s2) == True{} : Bool})
  -> {Nat.is_le(Run.notPick(Gll.descIn(u, s2)), Run.notPick(b)) == True{} : Bool}:
  match b:
    case True{}:
      pick_true(u, s2, desc_sub(s1, u, s2, eb, sub))
    case False{}:
      pick_le_one(Gll.descIn(u, s2))

# Seeing more leaves no more unseen.
law count_mono:
  for us: +List<Gll.Desc>
  for +s1: +List<Gll.Desc>
  for +s2: +List<Gll.Desc>
  for +sub: {Run.subDescs(s1, s2) == True{} : Bool}
  {Nat.is_le(Run.countNot(us, s2), Run.countNot(us, s1)) == True{} : Bool}

def count_mono(us, s1, s2, sub):
  match us:
    case Nil{}:
      {==}
    case Con{+u, +rest}:
      le_add2(Run.notPick(Gll.descIn(u, s2)), Run.countNot(rest, s2), Run.notPick(Gll.descIn(u, s1)), Run.countNot(rest, s1),
        mono_pick(Gll.descIn(u, s1), u, s1, s2, {==}, sub), count_mono(rest, s1, s2, sub))

def one_le_one(+x: Nat, +y: Nat, +ex: {x == 0n : Nat}, +ey: {y == 1n : Nat}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  %Equal.sym(Nat, x, 0n, ex) : {Nat.is_le(1n+_, y) == True{} : Bool}
  %Equal.sym(Nat, y, 1n, ey) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def drop_here(+d: Gll.Desc, +rest: +List<Gll.Desc>, +seen: +List<Gll.Desc>,
  +out: {Gll.descIn(d, seen) == False{} : Bool})
  -> {Nat.is_le(1n+Run.countNot(d <> rest, d <> seen), Run.countNot(d <> rest, seen)) == True{} : Bool}:
  +x = Run.notPick(Gll.descIn(d, d <> seen))
  +y = Run.notPick(Gll.descIn(d, seen))
  +inD = Lemma.or_true_left_intro(Gll.descEq(d, d), Gll.descIn(d, seen), desc_eq_refl(d))
  +ex = Equal.cong(Bool, Nat, v => Run.notPick(v), Gll.descIn(d, d <> seen), True{}, inD)
  +ey = Equal.cong(Bool, Nat, v => Run.notPick(v), Gll.descIn(d, seen), False{}, out)
  le_add2(1n+x, Run.countNot(rest, d <> seen), y, Run.countNot(rest, seen), one_le_one(x, y, ex, ey),
    count_mono(rest, seen, d <> seen, desc_weaken(seen, d, seen, desc_refl(seen))))

def drop_pick(+d: Gll.Desc, +u: Gll.Desc, +rest: +List<Gll.Desc>, +seen: +List<Gll.Desc>,
  +out: {Gll.descIn(d, seen) == False{} : Bool},
  cases: Either<{Gll.descEq(d, u) == True{} : Bool}, {Gll.descIn(d, rest) == True{} : Bool}>,
  later: {Gll.descIn(d, rest) == True{} : Bool} -> {Nat.is_le(1n+Run.countNot(rest, d <> seen), Run.countNot(rest, seen)) == True{} : Bool})
  -> {Nat.is_le(1n+Run.countNot(u <> rest, d <> seen), Run.countNot(u <> rest, seen)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %G.desc_eq_sound(d, u, e) : {Nat.is_le(1n+Run.countNot(_ <> rest, d <> seen), Run.countNot(_ <> rest, seen)) == True{} : Bool}
      drop_here(d, rest, seen, out)
    case Inr{m}:
      +xt = Run.notPick(Gll.descIn(u, d <> seen))
      +xs = Run.notPick(Gll.descIn(u, seen))
      +c2 = Run.countNot(rest, d <> seen)
      %Lemma.add_succ_right(xt, c2) : {Nat.is_le(_, Nat.add(xs, Run.countNot(rest, seen))) == True{} : Bool}
      le_add2(xt, 1n+c2, xs, Run.countNot(rest, seen),
        mono_pick(Gll.descIn(u, seen), u, seen, d <> seen, {==}, desc_weaken(seen, d, seen, desc_refl(seen))), later(m))

# Seeing a new descriptor of the universe leaves one fewer unseen.
law count_drop:
  for us: +List<Gll.Desc>
  for +seen: +List<Gll.Desc>
  for +d: Gll.Desc
  for +inU: {Gll.descIn(d, us) == True{} : Bool}
  for +out: {Gll.descIn(d, seen) == False{} : Bool}
  {Nat.is_le(1n+Run.countNot(us, d <> seen), Run.countNot(us, seen)) == True{} : Bool}

def count_drop(us, seen, d, inU, out):
  match us:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n+0n, 0n) == True{} : Bool}, Lemma.false_is_not_true(inU))
    case Con{+u, +rest}:
      drop_pick(d, u, rest, seen, out, Lemma.or_true_cases(Gll.descEq(d, u), Gll.descIn(d, rest), inU), m => count_drop(rest, seen, d, m, out))

# ======== STEP LISTS AND THE EMPTY COUNT ========

def bsr_eq_refl(b: Core.Bsr) -> {Core.bsrEq(b, b) == True{} : Bool}:
  match b:
    case Core.Bsr{+q, +dt, +i, +k, +j}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(dt, dt), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), Lemma.nat_eq_refl(dt),
          Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
            Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j)))))

law step_weaken:
  for xs: +List<Core.Bsr>
  for +y: Core.Bsr
  for +ys: +List<Core.Bsr>
  for +h: {Core.allIn(xs, ys) == True{} : Bool}
  {Core.allIn(xs, y <> ys) == True{} : Bool}

def step_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, y <> ys), Core.allIn(rest, y <> ys),
        Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, ys), Lemma.and_true_left(Core.member(x, ys), Core.allIn(rest, ys), h)),
        step_weaken(rest, y, ys, Lemma.and_true_right_side(Core.member(x, ys), Core.allIn(rest, ys), h)))

law step_refl:
  for xs: +List<Core.Bsr>
  {Core.allIn(xs, xs) == True{} : Bool}

def step_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Core.member(x, x <> rest), Core.allIn(rest, x <> rest), Lemma.or_true_left_intro(Core.bsrEq(x, x), Core.member(x, rest), bsr_eq_refl(x)),
        step_weaken(rest, x, rest, step_refl(rest)))

law count_empty:
  for us: +List<Gll.Desc>
  {Run.countNot(us, []) == List.length(&2, Gll.Desc, us) : Nat}

def count_empty(us):
  match us:
    case Nil{}:
      {==}
    case Con{+u, +rest}:
      %count_empty(rest) : {1n+Run.countNot(rest, []) == 1n+_ : Nat}
      {==}

law count_start:
  for +us: +List<Gll.Desc>
  {Nat.is_le(Nat.add(Run.countNot(us, []), 0n), List.length(&2, Gll.Desc, us)) == True{} : Bool}

def count_start(us):
  +c = Run.countNot(us, [])
  %Equal.sym(Nat, Nat.add(c, 0n), c, Lemma.add_zero_right(c)) : {Nat.is_le(_, List.length(&2, Gll.Desc, us)) == True{} : Bool}
  %Equal.sym(Nat, c, List.length(&2, Gll.Desc, us), count_empty(us)) : {Nat.is_le(_, List.length(&2, Gll.Desc, us)) == True{} : Bool}
  Lemma.le_refl(List.length(&2, Gll.Desc, us))
