import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./SETS.bend as Sets
import ./TABLES.bend as T
import ./PREDICT.bend as P
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C
import ./PROOF_WITNESS.bend as WC

# THE TABLES CLOSE (SETS.bend, TABLES.bend): with enough rounds, the grown nullable, FIRST
# and FOLLOW tables are closed under their rules. A round either adds a fact from a finite
# universe (one fewer unseen) or changes nothing, and then the table is closed. Facts are
# counted as descriptors (RUN.bend's counting): a nullable x as Desc{x, 0, 0, 0}.

# ======== NULLABLE ========

def lhsList(prods: +List<Core.Production>) -> +List<Nat>:
  match prods:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, +rhs}, rest}:
      lhs <> lhsList(rest)

def nullDescs(xs: +List<Nat>) -> +List<Gll.Desc>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      Gll.Desc{x, 0n, 0n, 0n} <> nullDescs(rest)

def nMeas(+grammar: +List<Core.Production>, +acc: +List<Nat>) -> Nat:
  Run.countNot(nullDescs(lhsList(grammar)), nullDescs(acc))

def eq_is_n(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

def descQ(d: Gll.Desc) -> Nat:
  match d:
    case Gll.Desc{+q, +dd, +k, +i}:
      q

def desc_eq_at(+x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}) == True{} : Bool}:
  %e : {Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{_, 0n, 0n, 0n}) == True{} : Bool}
  C.desc_eq_refl(Gll.Desc{x, 0n, 0n, 0n})

def nd_pick(+x: Nat, +y: Nat, +rest: +List<Nat>,
  cases: Either<{Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}) == True{} : Bool}, {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)) == True{} : Bool}>,
  later: {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)) == True{} : Bool} -> {Sets.natIn(x, rest) == True{} : Bool})
  -> {Sets.natIn(x, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +ex = Equal.cong(Gll.Desc, Nat, v => descQ(v), Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}, G.desc_eq_sound(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}, e))
      Lemma.or_true_left_intro(Nat.is_eq(x, y), Sets.natIn(x, rest), eq_is_n(x, y, ex))
    case Inr{m}:
      Lemma.or_true_right_intro(Nat.is_eq(x, y), Sets.natIn(x, rest), later(m))

# A nullable x counted is a nullable x.
law nd_back:
  for xs: +List<Nat>
  for +x: Nat
  for +h: {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(xs)) == True{} : Bool}
  {Sets.natIn(x, xs) == True{} : Bool}

def nd_back(xs, x, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      nd_pick(x, y, rest, Lemma.or_true_cases(Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}), Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)), h),
        m => nd_back(rest, x, m))

def nd_pick2(+x: Nat, +y: Nat, +rest: +List<Nat>,
  cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Sets.natIn(x, rest) == True{} : Bool}>,
  later: {Sets.natIn(x, rest) == True{} : Bool} -> {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(y <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +ex = Lemma.nat_eq_sound(x, y, e)
      Lemma.or_true_left_intro(Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}), Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)), desc_eq_at(x, y, ex))
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descEq(Gll.Desc{x, 0n, 0n, 0n}, Gll.Desc{y, 0n, 0n, 0n}), Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(rest)), later(m))

# A nullable x is counted.
law nd_in:
  for xs: +List<Nat>
  for +x: Nat
  for +h: {Sets.natIn(x, xs) == True{} : Bool}
  {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(xs)) == True{} : Bool}

def nd_in(xs, x, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      nd_pick2(x, y, rest, Lemma.or_true_cases(Nat.is_eq(x, y), Sets.natIn(x, rest), h), m => nd_in(rest, x, m))

def not_in_desc(b: Bool, +x: Nat, +xs: +List<Nat>, +eb: {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(xs)) == b : Bool},
  +out: {Sets.natIn(x, xs) == False{} : Bool}) -> {Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(xs)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(xs)) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Sets.natIn(x, xs), False{}, Equal.sym(Bool, Sets.natIn(x, xs), True{}, nd_back(xs, x, eb)), out)))
    case False{}:
      eb

# A new nullable lhs: one fewer unseen.
def n_drop(+grammar: +List<Core.Production>, +x: Nat, +acc: +List<Nat>, +inU: {Sets.natIn(x, lhsList(grammar)) == True{} : Bool}, +out: {Sets.natIn(x, acc) == False{} : Bool})
  -> {Nat.is_le(1n+nMeas(grammar, x <> acc), nMeas(grammar, acc)) == True{} : Bool}:
  C.count_drop(nullDescs(lhsList(grammar)), nullDescs(acc), Gll.Desc{x, 0n, 0n, 0n}, nd_in(lhsList(grammar), x, inU),
    not_in_desc(Gll.descIn(Gll.Desc{x, 0n, 0n, 0n}, nullDescs(acc)), x, acc, {==}, out))

# ======== ROUND (NULLS) ========
def not_true(c: Bool, +h: {Bool.not(c) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(h))
    case False{}:
      {==}

# A round that adds nothing at a production: the production keeps the rule.
def nc_from_t(c: Bool, +h: {Bool.not(c) == False{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(h))

def nc_from(a: Bool, c: Bool, +h: {Bool.and(a, Bool.not(c)) == False{} : Bool}) -> {Bool.or(Bool.not(a), c) == True{} : Bool}:
  match a:
    case True{}:
      nc_from_t(c, h)
    case False{}:
      {==}

def nc_to_t(c: Bool, +h: {c == True{} : Bool}) -> {Bool.not(c) == False{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.not(False{}) == False{} : Bool}, Lemma.false_is_not_true(h))

def nc_to(a: Bool, c: Bool, +h: {Bool.or(Bool.not(a), c) == True{} : Bool}) -> {Bool.and(a, Bool.not(c)) == False{} : Bool}:
  match a:
    case True{}:
      nc_to_t(c, h)
    case False{}:
      {==}

def NSame(+prods: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>) -> Type:
  {Sets.nullsClosed(prods, acc) == True{} : Bool} & {Nat.is_le(nMeas(grammar, Sets.nullsOnce(prods, acc)), nMeas(grammar, acc)) == True{} : Bool}

def NRound(+prods: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>) -> Type:
  Either<NSame(prods, grammar, acc), {Nat.is_le(1n+nMeas(grammar, Sets.nullsOnce(prods, acc)), nMeas(grammar, acc)) == True{} : Bool}>

def NRoundB(+b: Bool, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>) -> Type:
  Either<({Bool.and(Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)), Sets.nullsClosed(rest, acc)) == True{} : Bool} & {Nat.is_le(nMeas(grammar, Sets.nullsOnce(rest, Sets.addIf(b, lhs, acc))), nMeas(grammar, acc)) == True{} : Bool}),
    {Nat.is_le(1n+nMeas(grammar, Sets.nullsOnce(rest, Sets.addIf(b, lhs, acc))), nMeas(grammar, acc)) == True{} : Bool}>

def nsame_le(+prods: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>, p: NSame(prods, grammar, acc))
  -> {Nat.is_le(nMeas(grammar, Sets.nullsOnce(prods, acc)), nMeas(grammar, acc)) == True{} : Bool}:
  match p:
    case (+cl, +le):
      le

def nround_le(+prods: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>, r: NRound(prods, grammar, acc))
  -> {Nat.is_le(nMeas(grammar, Sets.nullsOnce(prods, acc)), nMeas(grammar, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      nsame_le(prods, grammar, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(nMeas(grammar, Sets.nullsOnce(prods, acc)), nMeas(grammar, acc), m)

def nb_true(+lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>,
  +inU: {Sets.natIn(lhs, lhsList(grammar)) == True{} : Bool}, +out: {Sets.natIn(lhs, acc) == False{} : Bool},
  r: NRound(rest, grammar, lhs <> acc)) -> NRoundB(True{}, lhs, rhs, rest, grammar, acc):
  Inr{Lemma.le_trans(1n+nMeas(grammar, Sets.nullsOnce(rest, lhs <> acc)), 1n+nMeas(grammar, lhs <> acc), nMeas(grammar, acc),
    nround_le(rest, grammar, lhs <> acc, r), n_drop(grammar, lhs, acc, inU, out))}

def nb_false2(+lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>,
  +hd: {Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)) == True{} : Bool},
  p: NSame(rest, grammar, acc)) -> NRoundB(False{}, lhs, rhs, rest, grammar, acc):
  match p:
    case (+cl, +le):
      Inl{(Lemma.and_true_intro(Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)), Sets.nullsClosed(rest, acc), hd, cl), le)}

def nb_false(+lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>,
  +hd: {Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)) == True{} : Bool},
  r: NRound(rest, grammar, acc)) -> NRoundB(False{}, lhs, rhs, rest, grammar, acc):
  match r:
    case Inl{p}:
      nb_false2(lhs, rhs, rest, grammar, acc, hd, p)
    case Inr{m}:
      Inr{m}

def nround_b(b: Bool, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +grammar: +List<Core.Production>, +acc: +List<Nat>,
  +eb: {Bool.and(Sets.allNull(rhs, acc), Bool.not(Sets.natIn(lhs, acc))) == b : Bool},
  +inU: {Sets.natIn(lhs, lhsList(grammar)) == True{} : Bool},
  later: @a: +List<Nat> -> NRound(rest, grammar, a)) -> NRoundB(b, lhs, rhs, rest, grammar, acc):
  match b:
    case True{}:
      nb_true(lhs, rhs, rest, grammar, acc, inU,
        not_true(Sets.natIn(lhs, acc), Lemma.and_true_right_side(Sets.allNull(rhs, acc), Bool.not(Sets.natIn(lhs, acc)), eb)), later(lhs <> acc))
    case False{}:
      nb_false(lhs, rhs, rest, grammar, acc, nc_from(Sets.allNull(rhs, acc), Sets.natIn(lhs, acc), eb), later(acc))

# One round over productions whose left sides lie in the grammar's: the nullable set is
# closed under them and the count did not rise, or the count drops.
law nround:
  for prods: +List<Core.Production>
  for +grammar: +List<Core.Production>
  for +acc: +List<Nat>
  for +hs: {Sets.allNatIn(lhsList(prods), lhsList(grammar)) == True{} : Bool}
  NRound(prods, grammar, acc)

def nround(prods, grammar, acc, hs):
  match prods:
    case Nil{}:
      Inl{({==}, Lemma.le_refl(nMeas(grammar, acc)))}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      nround_b(Bool.and(Sets.allNull(rhs, acc), Bool.not(Sets.natIn(lhs, acc))), lhs, rhs, rest, grammar, acc, {==},
        Lemma.and_true_left(Sets.natIn(lhs, lhsList(grammar)), Sets.allNatIn(lhsList(rest), lhsList(grammar)), hs),
        a => nround(rest, grammar, a, Lemma.and_true_right_side(Sets.natIn(lhs, lhsList(grammar)), Sets.allNatIn(lhsList(rest), lhsList(grammar)), hs)))

# A closed nullable set is kept by a round.
law nulls_stay:
  for prods: +List<Core.Production>
  for +acc: +List<Nat>
  for +cl: {Sets.nullsClosed(prods, acc) == True{} : Bool}
  {Sets.nullsOnce(prods, acc) == acc : +List<Nat>}

def nulls_stay(prods, acc, cl):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hd = Lemma.and_true_left(Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)), Sets.nullsClosed(rest, acc), cl)
      +e = nc_to(Sets.allNull(rhs, acc), Sets.natIn(lhs, acc), hd)
      %Equal.sym(Bool, Bool.and(Sets.allNull(rhs, acc), Bool.not(Sets.natIn(lhs, acc))), False{}, e) : {Sets.nullsOnce(rest, Sets.addIf(_, lhs, acc)) == acc : +List<Nat>}
      nulls_stay(rest, acc, Lemma.and_true_right_side(Bool.or(Bool.not(Sets.allNull(rhs, acc)), Sets.natIn(lhs, acc)), Sets.nullsClosed(rest, acc), cl))

law grow_nulls_stay:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +acc: +List<Nat>
  for +cl: {Sets.nullsClosed(grammar, acc) == True{} : Bool}
  {Sets.growNulls(n, grammar, acc) == acc : +List<Nat>}

def grow_nulls_stay(n, grammar, acc, cl):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(+List<Nat>, Sets.nullsOnce(grammar, acc), acc, nulls_stay(grammar, acc, cl)) : {Sets.growNulls(p, grammar, _) == acc : +List<Nat>}
      grow_nulls_stay(p, grammar, acc, cl)

def nfix_same2(+f: Nat, +grammar: +List<Core.Production>, +acc: +List<Nat>, +cl: {Sets.nullsClosed(grammar, acc) == True{} : Bool})
  -> {Sets.nullsClosed(grammar, Sets.growNulls(f, grammar, Sets.nullsOnce(grammar, acc))) == True{} : Bool}:
  %Equal.sym(+List<Nat>, Sets.nullsOnce(grammar, acc), acc, nulls_stay(grammar, acc, cl)) : {Sets.nullsClosed(grammar, Sets.growNulls(f, grammar, _)) == True{} : Bool}
  %Equal.sym(+List<Nat>, Sets.growNulls(f, grammar, acc), acc, grow_nulls_stay(f, grammar, acc, cl)) : {Sets.nullsClosed(grammar, _) == True{} : Bool}
  cl

def nfix_same(+f: Nat, +grammar: +List<Core.Production>, +acc: +List<Nat>, p: NSame(grammar, grammar, acc))
  -> {Sets.nullsClosed(grammar, Sets.growNulls(f, grammar, Sets.nullsOnce(grammar, acc))) == True{} : Bool}:
  match p:
    case (+cl, +le):
      nfix_same2(f, grammar, acc, cl)

def nfix_step(+f: Nat, +grammar: +List<Core.Production>, +acc: +List<Nat>, r: NRound(grammar, grammar, acc),
  +hf: {Nat.is_le(nMeas(grammar, acc), f) == True{} : Bool},
  later: {Nat.is_le(1n+nMeas(grammar, Sets.nullsOnce(grammar, acc)), f) == True{} : Bool} -> {Sets.nullsClosed(grammar, Sets.growNulls(f, grammar, Sets.nullsOnce(grammar, acc))) == True{} : Bool})
  -> {Sets.nullsClosed(grammar, Sets.growNulls(f, grammar, Sets.nullsOnce(grammar, acc))) == True{} : Bool}:
  match r:
    case Inl{p}:
      nfix_same(f, grammar, acc, p)
    case Inr{m}:
      later(Lemma.le_trans(1n+nMeas(grammar, Sets.nullsOnce(grammar, acc)), nMeas(grammar, acc), f, m, hf))

# With more rounds than unseen left sides, the nullable set ends closed.
law nulls_fix:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +acc: +List<Nat>
  for +hs: {Sets.allNatIn(lhsList(grammar), lhsList(grammar)) == True{} : Bool}
  for +hf: {Nat.is_le(1n+nMeas(grammar, acc), fuel) == True{} : Bool}
  {Sets.nullsClosed(grammar, Sets.growNulls(fuel, grammar, acc)) == True{} : Bool}

def nulls_fix(fuel, grammar, acc, hs, hf):
  match fuel:
    case 0n:
      Empty.absurd({Sets.nullsClosed(grammar, acc) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      nfix_step(f, grammar, acc, nround(grammar, grammar, acc, hs), hf,
        h2 => nulls_fix(f, grammar, Sets.nullsOnce(grammar, acc), hs, h2))

# ======== NATURAL LISTS ========

def nat_self(+x: Nat, +rest: +List<Nat>) -> {Sets.natIn(x, x <> rest) == True{} : Bool}:
  Lemma.or_true_left_intro(Nat.is_eq(x, x), Sets.natIn(x, rest), Lemma.nat_eq_refl(x))

law all_nat_weaken:
  for xs: +List<Nat>
  for +y: Nat
  for +ys: +List<Nat>
  for +h: {Sets.allNatIn(xs, ys) == True{} : Bool}
  {Sets.allNatIn(xs, y <> ys) == True{} : Bool}

def all_nat_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, y <> ys), Sets.allNatIn(rest, y <> ys),
        Lemma.or_true_right_intro(Nat.is_eq(x, y), Sets.natIn(x, ys), Lemma.and_true_left(Sets.natIn(x, ys), Sets.allNatIn(rest, ys), h)),
        all_nat_weaken(rest, y, ys, Lemma.and_true_right_side(Sets.natIn(x, ys), Sets.allNatIn(rest, ys), h)))

law all_nat_refl:
  for xs: +List<Nat>
  {Sets.allNatIn(xs, xs) == True{} : Bool}

def all_nat_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, x <> rest), Sets.allNatIn(rest, x <> rest), nat_self(x, rest), all_nat_weaken(rest, x, rest, all_nat_refl(rest)))

def nulls_start(+fuel: Nat, +grammar: +List<Core.Production>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+nMeas(grammar, []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(nullDescs(lhsList(grammar)), []), List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), C.count_empty(nullDescs(lhsList(grammar)))) : {Nat.is_le(1n+_, fuel) == True{} : Bool}
  hf

law nulls_closed:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), fuel) == True{} : Bool}
  {Sets.nullsClosed(grammar, Sets.growNulls(fuel, grammar, [])) == True{} : Bool}

def nulls_closed(fuel, grammar, hf):
  nulls_fix(fuel, grammar, [], all_nat_refl(lhsList(grammar)), nulls_start(fuel, grammar, hf))

# ======== NATURAL LISTS, JOINED ========

def nat_join_left_pick(+x: Nat, +y: Nat, +rest: +List<Nat>, +b: +List<Nat>,
  cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Sets.natIn(x, rest) == True{} : Bool}>,
  later: {Sets.natIn(x, rest) == True{} : Bool} -> {Sets.natIn(x, Sets.joinNats(rest, b)) == True{} : Bool})
  -> {Sets.natIn(x, Sets.joinNats(y <> rest, b)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Nat.is_eq(x, y), Sets.natIn(x, Sets.joinNats(rest, b)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Nat.is_eq(x, y), Sets.natIn(x, Sets.joinNats(rest, b)), later(m))

law nat_join_left:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +x: Nat
  for +m: {Sets.natIn(x, a) == True{} : Bool}
  {Sets.natIn(x, Sets.joinNats(a, b)) == True{} : Bool}

def nat_join_left(a, b, x, m):
  match a:
    case Nil{}:
      Empty.absurd({Sets.natIn(x, b) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      nat_join_left_pick(x, y, rest, b, Lemma.or_true_cases(Nat.is_eq(x, y), Sets.natIn(x, rest), m), m2 => nat_join_left(rest, b, x, m2))

law nat_join_right:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +x: Nat
  for +m: {Sets.natIn(x, b) == True{} : Bool}
  {Sets.natIn(x, Sets.joinNats(a, b)) == True{} : Bool}

def nat_join_right(a, b, x, m):
  match a:
    case Nil{}:
      m
    case Con{+y, +rest}:
      Lemma.or_true_right_intro(Nat.is_eq(x, y), Sets.natIn(x, Sets.joinNats(rest, b)), nat_join_right(rest, b, x, m))

law all_join_left:
  for xs: +List<Nat>
  for +a: +List<Nat>
  for +b: +List<Nat>
  for +h: {Sets.allNatIn(xs, a) == True{} : Bool}
  {Sets.allNatIn(xs, Sets.joinNats(a, b)) == True{} : Bool}

def all_join_left(xs, a, b, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, Sets.joinNats(a, b)), Sets.allNatIn(rest, Sets.joinNats(a, b)),
        nat_join_left(a, b, x, Lemma.and_true_left(Sets.natIn(x, a), Sets.allNatIn(rest, a), h)),
        all_join_left(rest, a, b, Lemma.and_true_right_side(Sets.natIn(x, a), Sets.allNatIn(rest, a), h)))

law all_join_right:
  for xs: +List<Nat>
  for +a: +List<Nat>
  for +b: +List<Nat>
  for +h: {Sets.allNatIn(xs, b) == True{} : Bool}
  {Sets.allNatIn(xs, Sets.joinNats(a, b)) == True{} : Bool}

def all_join_right(xs, a, b, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, Sets.joinNats(a, b)), Sets.allNatIn(rest, Sets.joinNats(a, b)),
        nat_join_right(a, b, x, Lemma.and_true_left(Sets.natIn(x, b), Sets.allNatIn(rest, b), h)),
        all_join_right(rest, a, b, Lemma.and_true_right_side(Sets.natIn(x, b), Sets.allNatIn(rest, b), h)))

# Both halves inside: the join inside.
law join_all:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +c: +List<Nat>
  for +ha: {Sets.allNatIn(a, c) == True{} : Bool}
  for +hb: {Sets.allNatIn(b, c) == True{} : Bool}
  {Sets.allNatIn(Sets.joinNats(a, b), c) == True{} : Bool}

def join_all(a, b, c, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+x, +rest}:
      Lemma.and_true_intro(Sets.natIn(x, c), Sets.allNatIn(Sets.joinNats(rest, b), c), Lemma.and_true_left(Sets.natIn(x, c), Sets.allNatIn(rest, c), ha),
        join_all(rest, b, c, Lemma.and_true_right_side(Sets.natIn(x, c), Sets.allNatIn(rest, c), ha), hb))

def add_if_keep(b: Bool, +u: Nat, +t: Nat, +xs: +List<Nat>, +h: {Sets.natIn(t, xs) == True{} : Bool}) -> {Sets.natIn(t, Sets.addIf(b, u, xs)) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.or_true_right_intro(Nat.is_eq(t, u), Sets.natIn(t, xs), h)
    case False{}:
      h

def add_if_all(b: Bool, +u: Nat, +xs: +List<Nat>, +c: +List<Nat>, +hu: {Sets.natIn(u, c) == True{} : Bool}, +h: {Sets.allNatIn(xs, c) == True{} : Bool})
  -> {Sets.allNatIn(Sets.addIf(b, u, xs), c) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(Sets.natIn(u, c), Sets.allNatIn(xs, c), hu, h)
    case False{}:
      h

def nats_if_all(b: Bool, +xs: +List<Nat>, +c: +List<Nat>, +h: {Sets.allNatIn(xs, c) == True{} : Bool}) -> {Sets.allNatIn(T.natsIf(b, xs), c) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

# ======== FIRST ========

# The terminals of items, and of a grammar's right sides.
def termsOf(items: +List<Core.Sym>) -> +List<Nat>:
  match items:
    case Nil{}:
      []
    case Con{Core.Terminal{+k}, rest}:
      k <> termsOf(rest)
    case Con{Core.Nonterminal{+y, +need}, rest}:
      termsOf(rest)

def gramTerms(prods: +List<Core.Production>) -> +List<Nat>:
  match prods:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Sets.joinNats(termsOf(rhs), gramTerms(rest))

# Productions whose left sides lie in L and whose terminals lie in T.
def prodsIn(prods: +List<Core.Production>, +L: +List<Nat>, +T: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)))

# Every FIRST fact's token lies in T.
def firstsOk(facts: +List<T.FirstFact>, +T: +List<Nat>) -> Bool:
  match facts:
    case Nil{}:
      True{}
    case Con{T.FirstFact{+y, +u}, rest}:
      Bool.and(Sets.natIn(u, T), firstsOk(rest, T))

# FIRST facts counted as descriptors: (x, t) as Desc{x, t, 0, 0}; the universe is L times T.
def rowDescs(+x: Nat, ts: +List<Nat>, +k: Nat) -> +List<Gll.Desc>:
  match ts:
    case Nil{}:
      []
    case Con{+t, rest}:
      Gll.Desc{x, t, k, 0n} <> rowDescs(x, rest, k)

def pairDescs(xs: +List<Nat>, +ts: +List<Nat>, +k: Nat) -> +List<Gll.Desc>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.append(&2, Gll.Desc, rowDescs(x, ts, k), pairDescs(rest, ts, k))

def firstDescs(facts: +List<T.FirstFact>) -> +List<Gll.Desc>:
  match facts:
    case Nil{}:
      []
    case Con{T.FirstFact{+x, +t}, rest}:
      Gll.Desc{x, t, 0n, 0n} <> firstDescs(rest)

def fMeas(+L: +List<Nat>, +T: +List<Nat>, +acc: +List<T.FirstFact>) -> Nat:
  Run.countNot(pairDescs(L, T, 0n), firstDescs(acc))

def desc_eq_by(+a: Gll.Desc, +b: Gll.Desc, +e: {a == b : Gll.Desc}) -> {Gll.descEq(a, b) == True{} : Bool}:
  %e : {Gll.descEq(a, _) == True{} : Bool}
  C.desc_eq_refl(a)

def descD(d: Gll.Desc) -> Nat:
  match d:
    case Gll.Desc{+q, +dd, +k, +i}:
      dd

def descK(d: Gll.Desc) -> Nat:
  match d:
    case Gll.Desc{+q, +dd, +k, +i}:
      k

def row_pick(+x: Nat, +t: Nat, +u: Nat, +rest: +List<Nat>, +k: Nat,
  cases: Either<{Nat.is_eq(t, u) == True{} : Bool}, {Sets.natIn(t, rest) == True{} : Bool}>,
  later: {Sets.natIn(t, rest) == True{} : Bool} -> {Gll.descIn(Gll.Desc{x, t, k, 0n}, rowDescs(x, rest, k)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{x, t, k, 0n}, rowDescs(x, u <> rest, k)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +ex = Lemma.nat_eq_sound(t, u, e)
      Lemma.or_true_left_intro(Gll.descEq(Gll.Desc{x, t, k, 0n}, Gll.Desc{x, u, k, 0n}), Gll.descIn(Gll.Desc{x, t, k, 0n}, rowDescs(x, rest, k)),
        desc_eq_by(Gll.Desc{x, t, k, 0n}, Gll.Desc{x, u, k, 0n}, Equal.cong(Nat, Gll.Desc, v => Gll.Desc{x, v, k, 0n}, t, u, ex)))
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.descEq(Gll.Desc{x, t, k, 0n}, Gll.Desc{x, u, k, 0n}), Gll.descIn(Gll.Desc{x, t, k, 0n}, rowDescs(x, rest, k)), later(m))

law row_in:
  for +x: Nat
  for ts: +List<Nat>
  for +k: Nat
  for +t: Nat
  for +h: {Sets.natIn(t, ts) == True{} : Bool}
  {Gll.descIn(Gll.Desc{x, t, k, 0n}, rowDescs(x, ts, k)) == True{} : Bool}

def row_in(x, ts, k, t, h):
  match ts:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+u, +rest}:
      row_pick(x, t, u, rest, k, Lemma.or_true_cases(Nat.is_eq(t, u), Sets.natIn(t, rest), h), m => row_in(x, rest, k, t, m))

def pair_here(+x: Nat, +y: Nat, +rest: +List<Nat>, +ts: +List<Nat>, +k: Nat, +t: Nat, +e: {x == y : Nat}, +ht: {Sets.natIn(t, ts) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{x, t, k, 0n}, pairDescs(y <> rest, ts, k)) == True{} : Bool}:
  %e : {Gll.descIn(Gll.Desc{x, t, k, 0n}, List.append(&2, Gll.Desc, rowDescs(_, ts, k), pairDescs(rest, ts, k))) == True{} : Bool}
  C.desc_in_app_left(rowDescs(x, ts, k), pairDescs(rest, ts, k), Gll.Desc{x, t, k, 0n}, row_in(x, ts, k, t, ht))

def pair_pick(+x: Nat, +y: Nat, +rest: +List<Nat>, +ts: +List<Nat>, +k: Nat, +t: Nat, +ht: {Sets.natIn(t, ts) == True{} : Bool},
  cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Sets.natIn(x, rest) == True{} : Bool}>,
  later: {Sets.natIn(x, rest) == True{} : Bool} -> {Gll.descIn(Gll.Desc{x, t, k, 0n}, pairDescs(rest, ts, k)) == True{} : Bool})
  -> {Gll.descIn(Gll.Desc{x, t, k, 0n}, pairDescs(y <> rest, ts, k)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      pair_here(x, y, rest, ts, k, t, Lemma.nat_eq_sound(x, y, e), ht)
    case Inr{m}:
      C.desc_in_app_right(rowDescs(y, ts, k), pairDescs(rest, ts, k), Gll.Desc{x, t, k, 0n}, later(m))

# A pair of members is in the universe.
law pair_in:
  for xs: +List<Nat>
  for +ts: +List<Nat>
  for +k: Nat
  for +x: Nat
  for +t: Nat
  for +hx: {Sets.natIn(x, xs) == True{} : Bool}
  for +ht: {Sets.natIn(t, ts) == True{} : Bool}
  {Gll.descIn(Gll.Desc{x, t, k, 0n}, pairDescs(xs, ts, k)) == True{} : Bool}

def pair_in(xs, ts, k, x, t, hx, ht):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(hx))
    case Con{+y, +rest}:
      pair_pick(x, y, rest, ts, k, t, ht, Lemma.or_true_cases(Nat.is_eq(x, y), Sets.natIn(x, rest), hx), m => pair_in(rest, ts, k, x, t, m, ht))

def fd_here(+x: Nat, +t: Nat, +y: Nat, +u: Nat, +rest: +List<T.FirstFact>, +exy: {x == y : Nat}, +etu: {t == u : Nat})
  -> {Sets.natIn(t, T.firstsOf(x, T.FirstFact{y, u} <> rest)) == True{} : Bool}:
  %exy : {Sets.natIn(t, Sets.addIf(Nat.is_eq(_, x), u, T.firstsOf(x, rest))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, Lemma.nat_eq_refl(x)) : {Sets.natIn(t, Sets.addIf(_, u, T.firstsOf(x, rest))) == True{} : Bool}
  Lemma.or_true_left_intro(Nat.is_eq(t, u), Sets.natIn(t, T.firstsOf(x, rest)), eq_is_n(t, u, etu))

def fd_pick(+x: Nat, +t: Nat, +y: Nat, +u: Nat, +rest: +List<T.FirstFact>,
  cases: Either<{Gll.descEq(Gll.Desc{x, t, 0n, 0n}, Gll.Desc{y, u, 0n, 0n}) == True{} : Bool}, {Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(rest)) == True{} : Bool}>,
  later: {Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(rest)) == True{} : Bool} -> {Sets.natIn(t, T.firstsOf(x, rest)) == True{} : Bool})
  -> {Sets.natIn(t, T.firstsOf(x, T.FirstFact{y, u} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +ed = G.desc_eq_sound(Gll.Desc{x, t, 0n, 0n}, Gll.Desc{y, u, 0n, 0n}, e)
      fd_here(x, t, y, u, rest, Equal.cong(Gll.Desc, Nat, v => descQ(v), Gll.Desc{x, t, 0n, 0n}, Gll.Desc{y, u, 0n, 0n}, ed),
        Equal.cong(Gll.Desc, Nat, v => descD(v), Gll.Desc{x, t, 0n, 0n}, Gll.Desc{y, u, 0n, 0n}, ed))
    case Inr{m}:
      add_if_keep(Nat.is_eq(y, x), u, t, T.firstsOf(x, rest), later(m))

# A FIRST fact counted is a FIRST fact.
law fd_back:
  for acc: +List<T.FirstFact>
  for +x: Nat
  for +t: Nat
  for +h: {Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(acc)) == True{} : Bool}
  {Sets.natIn(t, T.firstsOf(x, acc)) == True{} : Bool}

def fd_back(acc, x, t, h):
  match acc:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{T.FirstFact{+y, +u}, +rest}:
      fd_pick(x, t, y, u, rest, Lemma.or_true_cases(Gll.descEq(Gll.Desc{x, t, 0n, 0n}, Gll.Desc{y, u, 0n, 0n}), Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(rest)), h),
        m => fd_back(rest, x, t, m))

def fd_out(b: Bool, +x: Nat, +t: Nat, +acc: +List<T.FirstFact>, +eb: {Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(acc)) == b : Bool},
  +out: {Sets.natIn(t, T.firstsOf(x, acc)) == False{} : Bool}) -> {Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(acc)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(acc)) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Sets.natIn(t, T.firstsOf(x, acc)), False{}, Equal.sym(Bool, Sets.natIn(t, T.firstsOf(x, acc)), True{}, fd_back(acc, x, t, eb)), out)))
    case False{}:
      eb

# A new FIRST fact (x, t), x in L and t in T: one fewer unseen.
def f_drop(+L: +List<Nat>, +T: +List<Nat>, +x: Nat, +t: Nat, +acc: +List<T.FirstFact>, +hx: {Sets.natIn(x, L) == True{} : Bool}, +ht: {Sets.natIn(t, T) == True{} : Bool},
  +out: {Sets.natIn(t, T.firstsOf(x, acc)) == False{} : Bool})
  -> {Nat.is_le(1n+fMeas(L, T, T.FirstFact{x, t} <> acc), fMeas(L, T, acc)) == True{} : Bool}:
  C.count_drop(pairDescs(L, T, 0n), firstDescs(acc), Gll.Desc{x, t, 0n, 0n}, pair_in(L, T, 0n, x, t, hx, ht),
    fd_out(Gll.descIn(Gll.Desc{x, t, 0n, 0n}, firstDescs(acc)), x, t, acc, {==}, out))

# ======== FIRST: TOKENS STAY IN T ========

law firsts_of_ok:
  for acc: +List<T.FirstFact>
  for +x: Nat
  for +T: +List<Nat>
  for +h: {firstsOk(acc, T) == True{} : Bool}
  {Sets.allNatIn(T.firstsOf(x, acc), T) == True{} : Bool}

def firsts_of_ok(acc, x, T, h):
  match acc:
    case Nil{}:
      {==}
    case Con{T.FirstFact{+y, +u}, +rest}:
      add_if_all(Nat.is_eq(y, x), u, T.firstsOf(x, rest), T, Lemma.and_true_left(Sets.natIn(u, T), firstsOk(rest, T), h),
        firsts_of_ok(rest, x, T, Lemma.and_true_right_side(Sets.natIn(u, T), firstsOk(rest, T), h)))

def foi_sym(s: Core.Sym, +rest: +List<Core.Sym>, +acc: +List<T.FirstFact>, +nulls: +List<Nat>, +T: +List<Nat>,
  +hi: {Sets.allNatIn(termsOf(s <> rest), T) == True{} : Bool}, +ha: {firstsOk(acc, T) == True{} : Bool},
  later: {Sets.allNatIn(termsOf(rest), T) == True{} : Bool} -> {Sets.allNatIn(T.firstOfItems(rest, acc, nulls), T) == True{} : Bool})
  -> {Sets.allNatIn(T.firstOfItems(s <> rest, acc, nulls), T) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      Lemma.and_true_intro(Sets.natIn(k, T), True{}, Lemma.and_true_left(Sets.natIn(k, T), Sets.allNatIn(termsOf(rest), T), hi), {==})
    case Core.Nonterminal{+y, +need}:
      join_all(T.firstsOf(y, acc), T.natsIf(Sets.itemNull(Core.Nonterminal{y, need}, nulls), T.firstOfItems(rest, acc, nulls)), T,
        firsts_of_ok(acc, y, T, ha), nats_if_all(Sets.itemNull(Core.Nonterminal{y, need}, nulls), T.firstOfItems(rest, acc, nulls), T, later(hi)))

# What items begin with lies in T, when their terminals and the facts' tokens do.
law foi_ok:
  for items: +List<Core.Sym>
  for +acc: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +T: +List<Nat>
  for +hi: {Sets.allNatIn(termsOf(items), T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  {Sets.allNatIn(T.firstOfItems(items, acc, nulls), T) == True{} : Bool}

def foi_ok(items, acc, nulls, T, hi, ha):
  match items:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      foi_sym(s, rest, acc, nulls, T, hi, ha, h2 => foi_ok(rest, acc, nulls, T, h2, ha))

# ======== FIRST: ONE ROUND ========

def pick_ok(have: Bool, +x: Nat, +t: Nat, +acc: +List<T.FirstFact>, +T: +List<Nat>, +ht: {Sets.natIn(t, T) == True{} : Bool}, +ha: {firstsOk(acc, T) == True{} : Bool})
  -> {firstsOk(T.firstPick(have, x, t, acc), T) == True{} : Bool}:
  match have:
    case True{}:
      ha
    case False{}:
      Lemma.and_true_intro(Sets.natIn(t, T), firstsOk(acc, T), ht, ha)

law add_firsts_ok:
  for ts: +List<Nat>
  for +x: Nat
  for +acc: +List<T.FirstFact>
  for +T: +List<Nat>
  for +hts: {Sets.allNatIn(ts, T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  {firstsOk(T.addFirsts(ts, x, acc), T) == True{} : Bool}

def add_firsts_ok(ts, x, acc, T, hts, ha):
  match ts:
    case Nil{}:
      ha
    case Con{+t, +rest}:
      add_firsts_ok(rest, x, T.firstPick(T.firstIn(x, t, acc), x, t, acc), T, Lemma.and_true_right_side(Sets.natIn(t, T), Sets.allNatIn(rest, T), hts),
        pick_ok(T.firstIn(x, t, acc), x, t, acc, T, Lemma.and_true_left(Sets.natIn(t, T), Sets.allNatIn(rest, T), hts), ha))

# A round keeps the facts' tokens in T.
law once_ok:
  for prods: +List<Core.Production>
  for +nulls: +List<Nat>
  for +acc: +List<T.FirstFact>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(prods, L, T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  {firstsOk(T.firstsOnce(prods, nulls, acc), T) == True{} : Bool}

def once_ok(prods, nulls, acc, L, T, hp, ha):
  match prods:
    case Nil{}:
      ha
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hr = Lemma.and_true_right_side(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), hp)
      once_ok(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), L, T, Lemma.and_true_right_side(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr),
        add_firsts_ok(T.firstOfItems(rhs, acc, nulls), lhs, acc, T, foi_ok(rhs, acc, nulls, T, Lemma.and_true_left(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr), ha), ha))

def ASame(+ts: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>) -> Type:
  {T.addFirsts(ts, x, acc) == acc : +List<T.FirstFact>} & {Sets.allNatIn(ts, T.firstsOf(x, acc)) == True{} : Bool}

def ARes(+L: +List<Nat>, +T: +List<Nat>, +ts: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>) -> Type:
  Either<ASame(ts, x, acc), {Nat.is_le(1n+fMeas(L, T, T.addFirsts(ts, x, acc)), fMeas(L, T, acc)) == True{} : Bool}>

def AResB(+b: Bool, +L: +List<Nat>, +T: +List<Nat>, +t: Nat, +rest: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>) -> Type:
  Either<({T.addFirsts(rest, x, T.firstPick(b, x, t, acc)) == acc : +List<T.FirstFact>} & {Bool.and(Sets.natIn(t, T.firstsOf(x, acc)), Sets.allNatIn(rest, T.firstsOf(x, acc))) == True{} : Bool}),
    {Nat.is_le(1n+fMeas(L, T, T.addFirsts(rest, x, T.firstPick(b, x, t, acc))), fMeas(L, T, acc)) == True{} : Bool}>

def fmeas_eq(+L: +List<Nat>, +T: +List<Nat>, +a: +List<T.FirstFact>, +b: +List<T.FirstFact>, +eq: {a == b : +List<T.FirstFact>})
  -> {Nat.is_le(fMeas(L, T, a), fMeas(L, T, b)) == True{} : Bool}:
  %eq : {Nat.is_le(fMeas(L, T, a), fMeas(L, T, _)) == True{} : Bool}
  Lemma.le_refl(fMeas(L, T, a))

def asame_le(+L: +List<Nat>, +T: +List<Nat>, +ts: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>, p: ASame(ts, x, acc))
  -> {Nat.is_le(fMeas(L, T, T.addFirsts(ts, x, acc)), fMeas(L, T, acc)) == True{} : Bool}:
  match p:
    case (+eq, +mem):
      fmeas_eq(L, T, T.addFirsts(ts, x, acc), acc, eq)

def ares_le(+L: +List<Nat>, +T: +List<Nat>, +ts: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>, r: ARes(L, T, ts, x, acc))
  -> {Nat.is_le(fMeas(L, T, T.addFirsts(ts, x, acc)), fMeas(L, T, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      asame_le(L, T, ts, x, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(fMeas(L, T, T.addFirsts(ts, x, acc)), fMeas(L, T, acc), m)

def ab_have2(+L: +List<Nat>, +T: +List<Nat>, +t: Nat, +rest: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>, +eb: {Sets.natIn(t, T.firstsOf(x, acc)) == True{} : Bool},
  p: ASame(rest, x, acc)) -> AResB(True{}, L, T, t, rest, x, acc):
  match p:
    case (+eq, +mem):
      Inl{(eq, Lemma.and_true_intro(Sets.natIn(t, T.firstsOf(x, acc)), Sets.allNatIn(rest, T.firstsOf(x, acc)), eb, mem))}

def ab_have(+L: +List<Nat>, +T: +List<Nat>, +t: Nat, +rest: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>, +eb: {Sets.natIn(t, T.firstsOf(x, acc)) == True{} : Bool},
  r: ARes(L, T, rest, x, acc)) -> AResB(True{}, L, T, t, rest, x, acc):
  match r:
    case Inl{p}:
      ab_have2(L, T, t, rest, x, acc, eb, p)
    case Inr{m}:
      Inr{m}

def ares_b(b: Bool, +L: +List<Nat>, +T: +List<Nat>, +t: Nat, +rest: +List<Nat>, +x: Nat, +acc: +List<T.FirstFact>,
  +eb: {Sets.natIn(t, T.firstsOf(x, acc)) == b : Bool},
  +hx: {Sets.natIn(x, L) == True{} : Bool}, +ht: {Sets.natIn(t, T) == True{} : Bool},
  later: @a: +List<T.FirstFact> -> ARes(L, T, rest, x, a)) -> AResB(b, L, T, t, rest, x, acc):
  match b:
    case True{}:
      ab_have(L, T, t, rest, x, acc, eb, later(acc))
    case False{}:
      Inr{Lemma.le_trans(1n+fMeas(L, T, T.addFirsts(rest, x, T.FirstFact{x, t} <> acc)), 1n+fMeas(L, T, T.FirstFact{x, t} <> acc), fMeas(L, T, acc),
        ares_le(L, T, rest, x, T.FirstFact{x, t} <> acc, later(T.FirstFact{x, t} <> acc)), f_drop(L, T, x, t, acc, hx, ht, eb))}

# Adding the tokens ts to FIRST of x: all were there and nothing changed, or the count drops.
law ares:
  for ts: +List<Nat>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +x: Nat
  for +acc: +List<T.FirstFact>
  for +hx: {Sets.natIn(x, L) == True{} : Bool}
  for +hts: {Sets.allNatIn(ts, T) == True{} : Bool}
  ARes(L, T, ts, x, acc)

def ares(ts, L, T, x, acc, hx, hts):
  match ts:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{+t, +rest}:
      ares_b(T.firstIn(x, t, acc), L, T, t, rest, x, acc, {==}, hx, Lemma.and_true_left(Sets.natIn(t, T), Sets.allNatIn(rest, T), hts),
        a => ares(rest, L, T, x, a, hx, Lemma.and_true_right_side(Sets.natIn(t, T), Sets.allNatIn(rest, T), hts)))

def FSame(+prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>) -> Type:
  {T.firstsOnce(prods, nulls, acc) == acc : +List<T.FirstFact>} & {T.firstsClosed(prods, acc, nulls) == True{} : Bool}

def FRes(+L: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>) -> Type:
  Either<FSame(prods, nulls, acc), {Nat.is_le(1n+fMeas(L, T, T.firstsOnce(prods, nulls, acc)), fMeas(L, T, acc)) == True{} : Bool}>

def fsame_le(+L: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>, p: FSame(prods, nulls, acc))
  -> {Nat.is_le(fMeas(L, T, T.firstsOnce(prods, nulls, acc)), fMeas(L, T, acc)) == True{} : Bool}:
  match p:
    case (+eq, +cl):
      fmeas_eq(L, T, T.firstsOnce(prods, nulls, acc), acc, eq)

def fres_le(+L: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>, r: FRes(L, T, prods, nulls, acc))
  -> {Nat.is_le(fMeas(L, T, T.firstsOnce(prods, nulls, acc)), fMeas(L, T, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      fsame_le(L, T, prods, nulls, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(fMeas(L, T, T.firstsOnce(prods, nulls, acc)), fMeas(L, T, acc), m)

def fclosed_to(+prods: +List<Core.Production>, +nulls: +List<Nat>, +a: +List<T.FirstFact>, +b: +List<T.FirstFact>, +eq: {a == b : +List<T.FirstFact>},
  +h: {T.firstsClosed(prods, a, nulls) == True{} : Bool}) -> {T.firstsClosed(prods, b, nulls) == True{} : Bool}:
  %eq : {T.firstsClosed(prods, _, nulls) == True{} : Bool}
  h

def fmeas_to(+L: +List<Nat>, +T: +List<Nat>, +a: +List<T.FirstFact>, +b: +List<T.FirstFact>, +x: Nat, +eq: {a == b : +List<T.FirstFact>},
  +h: {Nat.is_le(1n+x, fMeas(L, T, a)) == True{} : Bool}) -> {Nat.is_le(1n+x, fMeas(L, T, b)) == True{} : Bool}:
  %eq : {Nat.is_le(1n+x, fMeas(L, T, _)) == True{} : Bool}
  h

def fj_same2(+L: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>,
  +eq: {T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc) == acc : +List<T.FirstFact>}, +mem: {Sets.allNatIn(T.firstOfItems(rhs, acc, nulls), T.firstsOf(lhs, acc)) == True{} : Bool},
  q: FSame(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))) -> FRes(L, T, Core.Production{lhs, rhs} <> rest, nulls, acc):
  match q:
    case (+eq2, +cl):
      Inl{(Equal.trans(+List<T.FirstFact>, T.firstsOnce(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc)), T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), acc, eq2, eq),
        Lemma.and_true_intro(Sets.allNatIn(T.firstOfItems(rhs, acc, nulls), T.firstsOf(lhs, acc)), T.firstsClosed(rest, acc, nulls), mem,
          fclosed_to(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), acc, eq, cl)))}

def fj_same(+L: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>,
  +eq: {T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc) == acc : +List<T.FirstFact>}, +mem: {Sets.allNatIn(T.firstOfItems(rhs, acc, nulls), T.firstsOf(lhs, acc)) == True{} : Bool},
  r: FRes(L, T, rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))) -> FRes(L, T, Core.Production{lhs, rhs} <> rest, nulls, acc):
  match r:
    case Inl{q}:
      fj_same2(L, T, lhs, rhs, rest, nulls, acc, eq, mem, q)
    case Inr{m}:
      Inr{fmeas_to(L, T, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), acc, fMeas(L, T, T.firstsOnce(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))), eq, m)}

def fj_added(+L: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>,
  p: ASame(T.firstOfItems(rhs, acc, nulls), lhs, acc), r: FRes(L, T, rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))) -> FRes(L, T, Core.Production{lhs, rhs} <> rest, nulls, acc):
  match p:
    case (+eq, +mem):
      fj_same(L, T, lhs, rhs, rest, nulls, acc, eq, mem, r)

def fjoin(+L: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>,
  a: ARes(L, T, T.firstOfItems(rhs, acc, nulls), lhs, acc), r: FRes(L, T, rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))) -> FRes(L, T, Core.Production{lhs, rhs} <> rest, nulls, acc):
  match a:
    case Inl{p}:
      fj_added(L, T, lhs, rhs, rest, nulls, acc, p, r)
    case Inr{m1}:
      Inr{Lemma.le_trans(1n+fMeas(L, T, T.firstsOnce(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc))), 1n+fMeas(L, T, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc)), fMeas(L, T, acc),
        fres_le(L, T, rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), r), m1)}

# One FIRST round on productions within L and T, from facts within T: nothing changes and
# the facts are closed, or the count drops.
law fround:
  for prods: +List<Core.Production>
  for +nulls: +List<Nat>
  for +acc: +List<T.FirstFact>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(prods, L, T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  FRes(L, T, prods, nulls, acc)

def fround(prods, nulls, acc, L, T, hp, ha):
  match prods:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hr = Lemma.and_true_right_side(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), hp)
      +hx = Lemma.and_true_left(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), hp)
      +hi = Lemma.and_true_left(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr)
      +hrest = Lemma.and_true_right_side(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr)
      fjoin(L, T, lhs, rhs, rest, nulls, acc, ares(T.firstOfItems(rhs, acc, nulls), L, T, lhs, acc, hx, foi_ok(rhs, acc, nulls, T, hi, ha)),
        fround(rest, nulls, T.addFirsts(T.firstOfItems(rhs, acc, nulls), lhs, acc), L, T, hrest,
          add_firsts_ok(T.firstOfItems(rhs, acc, nulls), lhs, acc, T, foi_ok(rhs, acc, nulls, T, hi, ha), ha)))

# ======== FIRST: THE GROWTH ENDS CLOSED ========

law grow_firsts_stay:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +acc: +List<T.FirstFact>
  for +eq: {T.firstsOnce(grammar, nulls, acc) == acc : +List<T.FirstFact>}
  {T.growFirsts(n, grammar, nulls, acc) == acc : +List<T.FirstFact>}

def grow_firsts_stay(n, grammar, nulls, acc, eq):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(+List<T.FirstFact>, T.firstsOnce(grammar, nulls, acc), acc, eq) : {T.growFirsts(p, grammar, nulls, _) == acc : +List<T.FirstFact>}
      grow_firsts_stay(p, grammar, nulls, acc, eq)

def ffix_same2(+f: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>, +eq: {T.firstsOnce(grammar, nulls, acc) == acc : +List<T.FirstFact>}, +cl: {T.firstsClosed(grammar, acc, nulls) == True{} : Bool})
  -> {T.firstsClosed(grammar, T.growFirsts(f, grammar, nulls, T.firstsOnce(grammar, nulls, acc)), nulls) == True{} : Bool}:
  %Equal.sym(+List<T.FirstFact>, T.firstsOnce(grammar, nulls, acc), acc, eq) : {T.firstsClosed(grammar, T.growFirsts(f, grammar, nulls, _), nulls) == True{} : Bool}
  %Equal.sym(+List<T.FirstFact>, T.growFirsts(f, grammar, nulls, acc), acc, grow_firsts_stay(f, grammar, nulls, acc, eq)) : {T.firstsClosed(grammar, _, nulls) == True{} : Bool}
  cl

def ffix_same(+f: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>, p: FSame(grammar, nulls, acc))
  -> {T.firstsClosed(grammar, T.growFirsts(f, grammar, nulls, T.firstsOnce(grammar, nulls, acc)), nulls) == True{} : Bool}:
  match p:
    case (+eq, +cl):
      ffix_same2(f, grammar, nulls, acc, eq, cl)

def ffix_step(+f: Nat, +grammar: +List<Core.Production>, +nulls: +List<Nat>, +acc: +List<T.FirstFact>, +L: +List<Nat>, +T: +List<Nat>, r: FRes(L, T, grammar, nulls, acc),
  +hf: {Nat.is_le(fMeas(L, T, acc), f) == True{} : Bool},
  later: {Nat.is_le(1n+fMeas(L, T, T.firstsOnce(grammar, nulls, acc)), f) == True{} : Bool} -> {T.firstsClosed(grammar, T.growFirsts(f, grammar, nulls, T.firstsOnce(grammar, nulls, acc)), nulls) == True{} : Bool})
  -> {T.firstsClosed(grammar, T.growFirsts(f, grammar, nulls, T.firstsOnce(grammar, nulls, acc)), nulls) == True{} : Bool}:
  match r:
    case Inl{p}:
      ffix_same(f, grammar, nulls, acc, p)
    case Inr{m}:
      later(Lemma.le_trans(1n+fMeas(L, T, T.firstsOnce(grammar, nulls, acc)), fMeas(L, T, acc), f, m, hf))

law firsts_fix:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +acc: +List<T.FirstFact>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(grammar, L, T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  for +hf: {Nat.is_le(1n+fMeas(L, T, acc), fuel) == True{} : Bool}
  {T.firstsClosed(grammar, T.growFirsts(fuel, grammar, nulls, acc), nulls) == True{} : Bool}

def firsts_fix(fuel, grammar, nulls, acc, L, T, hp, ha, hf):
  match fuel:
    case 0n:
      Empty.absurd({T.firstsClosed(grammar, acc, nulls) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      ffix_step(f, grammar, nulls, acc, L, T, fround(grammar, nulls, acc, L, T, hp, ha), hf,
        h2 => firsts_fix(f, grammar, nulls, T.firstsOnce(grammar, nulls, acc), L, T, hp, once_ok(grammar, nulls, acc, L, T, hp, ha), h2))

# ======== THE GRAMMAR LIES WITHIN ITS OWN UNIVERSE ========

law prods_weaken:
  for prods: +List<Core.Production>
  for +y: Nat
  for +L: +List<Nat>
  for +A: +List<Nat>
  for +T: +List<Nat>
  for +h: {prodsIn(prods, L, T) == True{} : Bool}
  {prodsIn(prods, y <> L, Sets.joinNats(A, T)) == True{} : Bool}

def prods_weaken(prods, y, L, A, T, h):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hr = Lemma.and_true_right_side(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), h)
      Lemma.and_true_intro(Sets.natIn(lhs, y <> L), Bool.and(Sets.allNatIn(termsOf(rhs), Sets.joinNats(A, T)), prodsIn(rest, y <> L, Sets.joinNats(A, T))),
        Lemma.or_true_right_intro(Nat.is_eq(lhs, y), Sets.natIn(lhs, L), Lemma.and_true_left(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), h)),
        Lemma.and_true_intro(Sets.allNatIn(termsOf(rhs), Sets.joinNats(A, T)), prodsIn(rest, y <> L, Sets.joinNats(A, T)),
          all_join_right(termsOf(rhs), A, T, Lemma.and_true_left(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr)),
          prods_weaken(rest, y, L, A, T, Lemma.and_true_right_side(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr))))

law prods_self:
  for prods: +List<Core.Production>
  {prodsIn(prods, lhsList(prods), gramTerms(prods)) == True{} : Bool}

def prods_self(prods):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      Lemma.and_true_intro(Sets.natIn(lhs, lhs <> lhsList(rest)), Bool.and(Sets.allNatIn(termsOf(rhs), Sets.joinNats(termsOf(rhs), gramTerms(rest))), prodsIn(rest, lhs <> lhsList(rest), Sets.joinNats(termsOf(rhs), gramTerms(rest)))),
        nat_self(lhs, lhsList(rest)),
        Lemma.and_true_intro(Sets.allNatIn(termsOf(rhs), Sets.joinNats(termsOf(rhs), gramTerms(rest))), prodsIn(rest, lhs <> lhsList(rest), Sets.joinNats(termsOf(rhs), gramTerms(rest))),
          all_join_left(termsOf(rhs), termsOf(rhs), gramTerms(rest), all_nat_refl(termsOf(rhs))),
          prods_weaken(rest, lhs, lhsList(rest), termsOf(rhs), gramTerms(rest), prods_self(rest))))

def firstUniv(+grammar: +List<Core.Production>) -> +List<Gll.Desc>:
  pairDescs(lhsList(grammar), gramTerms(grammar), 0n)

def firsts_start(+fuel: Nat, +grammar: +List<Core.Production>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, firstUniv(grammar)), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+fMeas(lhsList(grammar), gramTerms(grammar), []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(firstUniv(grammar), []), List.length(&2, Gll.Desc, firstUniv(grammar)), C.count_empty(firstUniv(grammar))) : {Nat.is_le(1n+_, fuel) == True{} : Bool}
  hf

# THE FIRST TABLE CLOSES: with fuel 1 + the number of (left side, terminal) pairs, for any
# nullable set.
law firsts_closed:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, firstUniv(grammar)), fuel) == True{} : Bool}
  {T.firstsClosed(grammar, T.growFirsts(fuel, grammar, nulls, []), nulls) == True{} : Bool}

def firsts_closed(fuel, grammar, nulls, hf):
  firsts_fix(fuel, grammar, nulls, [], lhsList(grammar), gramTerms(grammar), prods_self(grammar), {==}, firsts_start(fuel, grammar, hf))

# ======== FOLLOW: COUNTING ========

# The next tokens allowed in FOLLOW: the end, or a terminal of T.
def maybeOk(n: Maybe<&2, Nat>, +T: +List<Nat>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{+t}:
      Sets.natIn(t, T)

def maybesOk(ns: +List<Maybe<&2, Nat>>, +T: +List<Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, rest}:
      Bool.and(maybeOk(n, T), maybesOk(rest, T))

def followsOk(facts: +List<T.FollowFact>, +T: +List<Nat>) -> Bool:
  match facts:
    case Nil{}:
      True{}
    case Con{T.FollowFact{+y, +n}, rest}:
      Bool.and(maybeOk(n, T), followsOk(rest, T))

# FOLLOW facts counted as descriptors: (y, end) as Desc{y, 0, 0, 0}, (y, t) as Desc{y, t, 1, 0}.
def followDesc(+y: Nat, n: Maybe<&2, Nat>) -> Gll.Desc:
  match n:
    case None{}:
      Gll.Desc{y, 0n, 0n, 0n}
    case Some{+t}:
      Gll.Desc{y, t, 1n, 0n}

def followDescs(facts: +List<T.FollowFact>) -> +List<Gll.Desc>:
  match facts:
    case Nil{}:
      []
    case Con{T.FollowFact{+y, +n}, rest}:
      followDesc(y, n) <> followDescs(rest)

def followUniv(+Y: +List<Nat>, +T: +List<Nat>) -> +List<Gll.Desc>:
  List.append(&2, Gll.Desc, nullDescs(Y), pairDescs(Y, T, 1n))

def oMeas(+Y: +List<Nat>, +T: +List<Nat>, +acc: +List<T.FollowFact>) -> Nat:
  Run.countNot(followUniv(Y, T), followDescs(acc))

def follow_univ(n: Maybe<&2, Nat>, +y: Nat, +Y: +List<Nat>, +T: +List<Nat>, +hy: {Sets.natIn(y, Y) == True{} : Bool}, +hn: {maybeOk(n, T) == True{} : Bool})
  -> {Gll.descIn(followDesc(y, n), followUniv(Y, T)) == True{} : Bool}:
  match n:
    case None{}:
      C.desc_in_app_left(nullDescs(Y), pairDescs(Y, T, 1n), Gll.Desc{y, 0n, 0n, 0n}, nd_in(Y, y, hy))
    case Some{+t}:
      C.desc_in_app_right(nullDescs(Y), pairDescs(Y, T, 1n), Gll.Desc{y, t, 1n, 0n}, pair_in(Y, T, 1n, y, t, hy, hn))

def maybe_eq_refl(n: Maybe<&2, Nat>) -> {T.maybeEq(n, n) == True{} : Bool}:
  match n:
    case None{}:
      {==}
    case Some{+t}:
      Lemma.nat_eq_refl(t)

def maybe_if_keep(b: Bool, +n: Maybe<&2, Nat>, +m: Maybe<&2, Nat>, +xs: +List<Maybe<&2, Nat>>, +h: {T.maybeIn(m, xs) == True{} : Bool})
  -> {T.maybeIn(m, T.maybeIf(b, n, xs)) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.or_true_right_intro(T.maybeEq(m, n), T.maybeIn(m, xs), h)
    case False{}:
      h

def zero_one(+e: {0n == 1n : Nat}) -> Empty:
  Lemma.false_is_not_true(Equal.cong(Nat, Bool, v => Nat.is_eq(v, 1n), 0n, 1n, e))

# Equal descriptors: equal facts.
def od_inv(n: Maybe<&2, Nat>, m: Maybe<&2, Nat>, +y: Nat, +z: Nat, +e: {followDesc(y, n) == followDesc(z, m) : Gll.Desc})
  -> {y == z : Nat} & {n == m : Maybe<&2, Nat>}:
  match n m:
    case None{} None{}:
      (Equal.cong(Gll.Desc, Nat, v => descQ(v), Gll.Desc{y, 0n, 0n, 0n}, Gll.Desc{z, 0n, 0n, 0n}, e), {==})
    case None{} Some{+u}:
      Empty.absurd({y == z : Nat} & {None{} == Some{u} : Maybe<&2, Nat>}, zero_one(Equal.cong(Gll.Desc, Nat, v => descK(v), Gll.Desc{y, 0n, 0n, 0n}, Gll.Desc{z, u, 1n, 0n}, e)))
    case Some{+t} None{}:
      Empty.absurd({y == z : Nat} & {Some{t} == None{} : Maybe<&2, Nat>}, zero_one(Equal.sym(Nat, 1n, 0n, Equal.cong(Gll.Desc, Nat, v => descK(v), Gll.Desc{y, t, 1n, 0n}, Gll.Desc{z, 0n, 0n, 0n}, e))))
    case Some{+t} Some{+u}:
      (Equal.cong(Gll.Desc, Nat, v => descQ(v), Gll.Desc{y, t, 1n, 0n}, Gll.Desc{z, u, 1n, 0n}, e),
        Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, t, u, Equal.cong(Gll.Desc, Nat, v => descD(v), Gll.Desc{y, t, 1n, 0n}, Gll.Desc{z, u, 1n, 0n}, e)))

def od_here2(+y: Nat, +n: Maybe<&2, Nat>, +z: Nat, +m: Maybe<&2, Nat>, +rest: +List<T.FollowFact>, +eyz: {y == z : Nat}, +enm: {n == m : Maybe<&2, Nat>})
  -> {T.maybeIn(n, T.followsOf(y, T.FollowFact{z, m} <> rest)) == True{} : Bool}:
  %eyz : {T.maybeIn(n, T.maybeIf(Nat.is_eq(_, y), m, T.followsOf(y, rest))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(y, y), True{}, Lemma.nat_eq_refl(y)) : {T.maybeIn(n, T.maybeIf(_, m, T.followsOf(y, rest))) == True{} : Bool}
  %enm : {T.maybeIn(n, _ <> T.followsOf(y, rest)) == True{} : Bool}
  Lemma.or_true_left_intro(T.maybeEq(n, n), T.maybeIn(n, T.followsOf(y, rest)), maybe_eq_refl(n))

def od_here(+y: Nat, +n: Maybe<&2, Nat>, +z: Nat, +m: Maybe<&2, Nat>, +rest: +List<T.FollowFact>, p: {y == z : Nat} & {n == m : Maybe<&2, Nat>})
  -> {T.maybeIn(n, T.followsOf(y, T.FollowFact{z, m} <> rest)) == True{} : Bool}:
  match p:
    case (+eyz, +enm):
      od_here2(y, n, z, m, rest, eyz, enm)

def od_pick(+y: Nat, +n: Maybe<&2, Nat>, +z: Nat, +m: Maybe<&2, Nat>, +rest: +List<T.FollowFact>,
  cases: Either<{Gll.descEq(followDesc(y, n), followDesc(z, m)) == True{} : Bool}, {Gll.descIn(followDesc(y, n), followDescs(rest)) == True{} : Bool}>,
  later: {Gll.descIn(followDesc(y, n), followDescs(rest)) == True{} : Bool} -> {T.maybeIn(n, T.followsOf(y, rest)) == True{} : Bool})
  -> {T.maybeIn(n, T.followsOf(y, T.FollowFact{z, m} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      od_here(y, n, z, m, rest, od_inv(n, m, y, z, G.desc_eq_sound(followDesc(y, n), followDesc(z, m), e)))
    case Inr{h}:
      maybe_if_keep(Nat.is_eq(z, y), m, n, T.followsOf(y, rest), later(h))

# A FOLLOW fact counted is a FOLLOW fact.
law od_back:
  for acc: +List<T.FollowFact>
  for +y: Nat
  for +n: Maybe<&2, Nat>
  for +h: {Gll.descIn(followDesc(y, n), followDescs(acc)) == True{} : Bool}
  {T.maybeIn(n, T.followsOf(y, acc)) == True{} : Bool}

def od_back(acc, y, n, h):
  match acc:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{T.FollowFact{+z, +m}, +rest}:
      od_pick(y, n, z, m, rest, Lemma.or_true_cases(Gll.descEq(followDesc(y, n), followDesc(z, m)), Gll.descIn(followDesc(y, n), followDescs(rest)), h),
        h2 => od_back(rest, y, n, h2))

def od_out(b: Bool, +y: Nat, +n: Maybe<&2, Nat>, +acc: +List<T.FollowFact>, +eb: {Gll.descIn(followDesc(y, n), followDescs(acc)) == b : Bool},
  +out: {T.maybeIn(n, T.followsOf(y, acc)) == False{} : Bool}) -> {Gll.descIn(followDesc(y, n), followDescs(acc)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Gll.descIn(followDesc(y, n), followDescs(acc)) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, T.maybeIn(n, T.followsOf(y, acc)), False{}, Equal.sym(Bool, T.maybeIn(n, T.followsOf(y, acc)), True{}, od_back(acc, y, n, eb)), out)))
    case False{}:
      eb

# A new FOLLOW fact within the universe: one fewer unseen.
def o_drop(+Y: +List<Nat>, +T: +List<Nat>, +y: Nat, +n: Maybe<&2, Nat>, +acc: +List<T.FollowFact>, +hy: {Sets.natIn(y, Y) == True{} : Bool}, +hn: {maybeOk(n, T) == True{} : Bool},
  +out: {T.maybeIn(n, T.followsOf(y, acc)) == False{} : Bool})
  -> {Nat.is_le(1n+oMeas(Y, T, T.FollowFact{y, n} <> acc), oMeas(Y, T, acc)) == True{} : Bool}:
  C.count_drop(followUniv(Y, T), followDescs(acc), followDesc(y, n), follow_univ(n, y, Y, T, hy, hn),
    od_out(Gll.descIn(followDesc(y, n), followDescs(acc)), y, n, acc, {==}, out))

# ======== FOLLOW: ADDING NEXT TOKENS ========

def opick_ok(have: Bool, +y: Nat, +n: Maybe<&2, Nat>, +acc: +List<T.FollowFact>, +T: +List<Nat>, +hn: {maybeOk(n, T) == True{} : Bool}, +ha: {followsOk(acc, T) == True{} : Bool})
  -> {followsOk(T.followPick(have, y, n, acc), T) == True{} : Bool}:
  match have:
    case True{}:
      ha
    case False{}:
      Lemma.and_true_intro(maybeOk(n, T), followsOk(acc, T), hn, ha)

law add_follows_ok:
  for ns: +List<Maybe<&2, Nat>>
  for +y: Nat
  for +acc: +List<T.FollowFact>
  for +T: +List<Nat>
  for +hns: {maybesOk(ns, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  {followsOk(T.addFollows(ns, y, acc), T) == True{} : Bool}

def add_follows_ok(ns, y, acc, T, hns, ha):
  match ns:
    case Nil{}:
      ha
    case Con{+n, +rest}:
      add_follows_ok(rest, y, T.followPick(T.followHas(y, n, acc), y, n, acc), T, Lemma.and_true_right_side(maybeOk(n, T), maybesOk(rest, T), hns),
        opick_ok(T.followHas(y, n, acc), y, n, acc, T, Lemma.and_true_left(maybeOk(n, T), maybesOk(rest, T), hns), ha))

def opick_keep(have: Bool, +y: Nat, +n: Maybe<&2, Nat>, +acc: +List<T.FollowFact>, +z: Nat, +m: Maybe<&2, Nat>, +h: {T.followHas(z, m, acc) == True{} : Bool})
  -> {T.followHas(z, m, T.followPick(have, y, n, acc)) == True{} : Bool}:
  match have:
    case True{}:
      h
    case False{}:
      maybe_if_keep(Nat.is_eq(y, z), n, m, T.followsOf(z, acc), h)

law add_follows_keep:
  for ns: +List<Maybe<&2, Nat>>
  for +y: Nat
  for +acc: +List<T.FollowFact>
  for +z: Nat
  for +m: Maybe<&2, Nat>
  for +h: {T.followHas(z, m, acc) == True{} : Bool}
  {T.followHas(z, m, T.addFollows(ns, y, acc)) == True{} : Bool}

def add_follows_keep(ns, y, acc, z, m, h):
  match ns:
    case Nil{}:
      h
    case Con{+n, +rest}:
      add_follows_keep(rest, y, T.followPick(T.followHas(y, n, acc), y, n, acc), z, m, opick_keep(T.followHas(y, n, acc), y, n, acc, z, m, h))

def OSame(+ns: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>) -> Type:
  {T.addFollows(ns, y, acc) == acc : +List<T.FollowFact>} & {T.allMaybeIn(ns, T.followsOf(y, acc)) == True{} : Bool}

def ORes(+Y: +List<Nat>, +T: +List<Nat>, +ns: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>) -> Type:
  Either<OSame(ns, y, acc), {Nat.is_le(1n+oMeas(Y, T, T.addFollows(ns, y, acc)), oMeas(Y, T, acc)) == True{} : Bool}>

def OResB(+b: Bool, +Y: +List<Nat>, +T: +List<Nat>, +n: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>) -> Type:
  Either<({T.addFollows(rest, y, T.followPick(b, y, n, acc)) == acc : +List<T.FollowFact>} & {Bool.and(T.maybeIn(n, T.followsOf(y, acc)), T.allMaybeIn(rest, T.followsOf(y, acc))) == True{} : Bool}),
    {Nat.is_le(1n+oMeas(Y, T, T.addFollows(rest, y, T.followPick(b, y, n, acc))), oMeas(Y, T, acc)) == True{} : Bool}>

def ometa_eq(+Y: +List<Nat>, +T: +List<Nat>, +a: +List<T.FollowFact>, +b: +List<T.FollowFact>, +eq: {a == b : +List<T.FollowFact>}) -> {Nat.is_le(oMeas(Y, T, a), oMeas(Y, T, b)) == True{} : Bool}:
  %eq : {Nat.is_le(oMeas(Y, T, a), oMeas(Y, T, _)) == True{} : Bool}
  Lemma.le_refl(oMeas(Y, T, a))

def omeas_to(+Y: +List<Nat>, +T: +List<Nat>, +a: +List<T.FollowFact>, +b: +List<T.FollowFact>, +x: Nat, +eq: {a == b : +List<T.FollowFact>},
  +h: {Nat.is_le(1n+x, oMeas(Y, T, a)) == True{} : Bool}) -> {Nat.is_le(1n+x, oMeas(Y, T, b)) == True{} : Bool}:
  %eq : {Nat.is_le(1n+x, oMeas(Y, T, _)) == True{} : Bool}
  h

def osame_le(+Y: +List<Nat>, +T: +List<Nat>, +ns: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>, p: OSame(ns, y, acc))
  -> {Nat.is_le(oMeas(Y, T, T.addFollows(ns, y, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match p:
    case (+eq, +mem):
      ometa_eq(Y, T, T.addFollows(ns, y, acc), acc, eq)

def ores_le(+Y: +List<Nat>, +T: +List<Nat>, +ns: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>, r: ORes(Y, T, ns, y, acc))
  -> {Nat.is_le(oMeas(Y, T, T.addFollows(ns, y, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      osame_le(Y, T, ns, y, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(oMeas(Y, T, T.addFollows(ns, y, acc)), oMeas(Y, T, acc), m)

def ob_have2(+Y: +List<Nat>, +T: +List<Nat>, +n: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>, +eb: {T.maybeIn(n, T.followsOf(y, acc)) == True{} : Bool},
  p: OSame(rest, y, acc)) -> OResB(True{}, Y, T, n, rest, y, acc):
  match p:
    case (+eq, +mem):
      Inl{(eq, Lemma.and_true_intro(T.maybeIn(n, T.followsOf(y, acc)), T.allMaybeIn(rest, T.followsOf(y, acc)), eb, mem))}

def ob_have(+Y: +List<Nat>, +T: +List<Nat>, +n: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>, +eb: {T.maybeIn(n, T.followsOf(y, acc)) == True{} : Bool},
  r: ORes(Y, T, rest, y, acc)) -> OResB(True{}, Y, T, n, rest, y, acc):
  match r:
    case Inl{p}:
      ob_have2(Y, T, n, rest, y, acc, eb, p)
    case Inr{m}:
      Inr{m}

def ores_b(b: Bool, +Y: +List<Nat>, +T: +List<Nat>, +n: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +y: Nat, +acc: +List<T.FollowFact>,
  +eb: {T.maybeIn(n, T.followsOf(y, acc)) == b : Bool},
  +hy: {Sets.natIn(y, Y) == True{} : Bool}, +hn: {maybeOk(n, T) == True{} : Bool},
  later: @a: +List<T.FollowFact> -> ORes(Y, T, rest, y, a)) -> OResB(b, Y, T, n, rest, y, acc):
  match b:
    case True{}:
      ob_have(Y, T, n, rest, y, acc, eb, later(acc))
    case False{}:
      Inr{Lemma.le_trans(1n+oMeas(Y, T, T.addFollows(rest, y, T.FollowFact{y, n} <> acc)), 1n+oMeas(Y, T, T.FollowFact{y, n} <> acc), oMeas(Y, T, acc),
        ores_le(Y, T, rest, y, T.FollowFact{y, n} <> acc, later(T.FollowFact{y, n} <> acc)), o_drop(Y, T, y, n, acc, hy, hn, eb))}

# Adding next tokens to FOLLOW of y: all were there and nothing changed, or the count drops.
law ores:
  for ns: +List<Maybe<&2, Nat>>
  for +Y: +List<Nat>
  for +T: +List<Nat>
  for +y: Nat
  for +acc: +List<T.FollowFact>
  for +hy: {Sets.natIn(y, Y) == True{} : Bool}
  for +hns: {maybesOk(ns, T) == True{} : Bool}
  ORes(Y, T, ns, y, acc)

def ores(ns, Y, T, y, acc, hy, hns):
  match ns:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{+n, +rest}:
      ores_b(T.followHas(y, n, acc), Y, T, n, rest, y, acc, {==}, hy, Lemma.and_true_left(maybeOk(n, T), maybesOk(rest, T), hns),
        a => ores(rest, Y, T, y, a, hy, Lemma.and_true_right_side(maybeOk(n, T), maybesOk(rest, T), hns)))

# ======== FOLLOW: LISTS OF NEXT TOKENS ========

law mj_left:
  for a: +List<Maybe<&2, Nat>>
  for +b: +List<Maybe<&2, Nat>>
  for +c: +List<Maybe<&2, Nat>>
  for +h: {T.allMaybeIn(T.joinMaybes(a, b), c) == True{} : Bool}
  {T.allMaybeIn(a, c) == True{} : Bool}

def mj_left(a, b, c, h):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(T.maybeIn(x, c), T.allMaybeIn(rest, c), Lemma.and_true_left(T.maybeIn(x, c), T.allMaybeIn(T.joinMaybes(rest, b), c), h),
        mj_left(rest, b, c, Lemma.and_true_right_side(T.maybeIn(x, c), T.allMaybeIn(T.joinMaybes(rest, b), c), h)))

law mj_right:
  for a: +List<Maybe<&2, Nat>>
  for +b: +List<Maybe<&2, Nat>>
  for +c: +List<Maybe<&2, Nat>>
  for +h: {T.allMaybeIn(T.joinMaybes(a, b), c) == True{} : Bool}
  {T.allMaybeIn(b, c) == True{} : Bool}

def mj_right(a, b, c, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      mj_right(rest, b, c, Lemma.and_true_right_side(T.maybeIn(x, c), T.allMaybeIn(T.joinMaybes(rest, b), c), h))

law some_follow:
  for ts: +List<Nat>
  for +y: Nat
  for +acc: +List<T.FollowFact>
  for +h: {T.allMaybeIn(T.someAll(ts), T.followsOf(y, acc)) == True{} : Bool}
  {T.allFollow(ts, y, acc) == True{} : Bool}

def some_follow(ts, y, acc, h):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      Lemma.and_true_intro(T.followHas(y, Some{t}, acc), T.allFollow(rest, y, acc), Lemma.and_true_left(T.maybeIn(Some{t}, T.followsOf(y, acc)), T.allMaybeIn(T.someAll(rest), T.followsOf(y, acc)), h),
        some_follow(rest, y, acc, Lemma.and_true_right_side(T.maybeIn(Some{t}, T.followsOf(y, acc)), T.allMaybeIn(T.someAll(rest), T.followsOf(y, acc)), h)))

def mif_or(b: Bool, +xs: +List<Maybe<&2, Nat>>, +c: +List<Maybe<&2, Nat>>, +h: {T.allMaybeIn(T.maybesIf(b, xs), c) == True{} : Bool}) -> {Bool.or(Bool.not(b), T.allMaybeIn(xs, c)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

law mok_join:
  for a: +List<Maybe<&2, Nat>>
  for +b: +List<Maybe<&2, Nat>>
  for +T: +List<Nat>
  for +ha: {maybesOk(a, T) == True{} : Bool}
  for +hb: {maybesOk(b, T) == True{} : Bool}
  {maybesOk(T.joinMaybes(a, b), T) == True{} : Bool}

def mok_join(a, b, T, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+x, +rest}:
      Lemma.and_true_intro(maybeOk(x, T), maybesOk(T.joinMaybes(rest, b), T), Lemma.and_true_left(maybeOk(x, T), maybesOk(rest, T), ha),
        mok_join(rest, b, T, Lemma.and_true_right_side(maybeOk(x, T), maybesOk(rest, T), ha), hb))

law mok_some:
  for ts: +List<Nat>
  for +T: +List<Nat>
  for +h: {Sets.allNatIn(ts, T) == True{} : Bool}
  {maybesOk(T.someAll(ts), T) == True{} : Bool}

def mok_some(ts, T, h):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      Lemma.and_true_intro(Sets.natIn(t, T), maybesOk(T.someAll(rest), T), Lemma.and_true_left(Sets.natIn(t, T), Sets.allNatIn(rest, T), h),
        mok_some(rest, T, Lemma.and_true_right_side(Sets.natIn(t, T), Sets.allNatIn(rest, T), h)))

def mok_if(b: Bool, +xs: +List<Maybe<&2, Nat>>, +T: +List<Nat>, +h: {maybesOk(xs, T) == True{} : Bool}) -> {maybesOk(T.maybesIf(b, xs), T) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def mok_pick(b: Bool, +n: Maybe<&2, Nat>, +xs: +List<Maybe<&2, Nat>>, +T: +List<Nat>, +hn: {maybeOk(n, T) == True{} : Bool}, +h: {maybesOk(xs, T) == True{} : Bool})
  -> {maybesOk(T.maybeIf(b, n, xs), T) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(maybeOk(n, T), maybesOk(xs, T), hn, h)
    case False{}:
      h

law mok_follows_of:
  for acc: +List<T.FollowFact>
  for +x: Nat
  for +T: +List<Nat>
  for +h: {followsOk(acc, T) == True{} : Bool}
  {maybesOk(T.followsOf(x, acc), T) == True{} : Bool}

def mok_follows_of(acc, x, T, h):
  match acc:
    case Nil{}:
      {==}
    case Con{T.FollowFact{+y, +n}, +rest}:
      mok_pick(Nat.is_eq(y, x), n, T.followsOf(x, rest), T, Lemma.and_true_left(maybeOk(n, T), followsOk(rest, T), h),
        mok_follows_of(rest, x, T, Lemma.and_true_right_side(maybeOk(n, T), followsOk(rest, T), h)))

# ======== FOLLOW: ONE ITEM ========

def symNt(s: Core.Sym, +Y: +List<Nat>) -> Bool:
  match s:
    case Core.Terminal{k}:
      True{}
    case Core.Nonterminal{+y, need}:
      Sets.natIn(y, Y)

def IRes(+Y: +List<Nat>, +T: +List<Nat>, +s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>) -> Type:
  Either<({T.itemFollows(s, rest, x, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.itemOk(s, rest, x, F, acc, nulls) == True{} : Bool}),
    {Nat.is_le(1n+oMeas(Y, T, T.itemFollows(s, rest, x, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}>

def ires_nt2(+Y: +List<Nat>, +T: +List<Nat>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, p: OSame(T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), y, acc))
  -> IRes(Y, T, Core.Nonterminal{y, need}, rest, x, F, nulls, acc):
  match p:
    case (+eq, +mem):
      Inl{(eq, Lemma.and_true_intro(T.allFollow(T.firstOfItems(rest, F, nulls), y, acc), Bool.or(Bool.not(Sets.allNull(rest, nulls)), T.allMaybeIn(T.followsOf(x, acc), T.followsOf(y, acc))),
        some_follow(T.firstOfItems(rest, F, nulls), y, acc, mj_left(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc)), T.followsOf(y, acc), mem)),
        mif_or(Sets.allNull(rest, nulls), T.followsOf(x, acc), T.followsOf(y, acc), mj_right(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc)), T.followsOf(y, acc), mem))))}

def ires_nt(+Y: +List<Nat>, +T: +List<Nat>, +y: Nat, +need: Core.Need, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, r: ORes(Y, T, T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), y, acc))
  -> IRes(Y, T, Core.Nonterminal{y, need}, rest, x, F, nulls, acc):
  match r:
    case Inl{p}:
      ires_nt2(Y, T, y, need, rest, x, F, nulls, acc, p)
    case Inr{m}:
      Inr{m}

def ns_ok(+rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +T: +List<Nat>, +hr: {Sets.allNatIn(termsOf(rest), T) == True{} : Bool},
  +hF: {firstsOk(F, T) == True{} : Bool}, +ha: {followsOk(acc, T) == True{} : Bool}) -> {maybesOk(T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), T) == True{} : Bool}:
  mok_join(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc)), T,
    mok_some(T.firstOfItems(rest, F, nulls), T, foi_ok(rest, F, nulls, T, hr, hF)),
    mok_if(Sets.allNull(rest, nulls), T.followsOf(x, acc), T, mok_follows_of(acc, x, T, ha)))

# One item's FOLLOW rule: it held and nothing changed, or the count drops.
def iround(s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +Y: +List<Nat>, +T: +List<Nat>, +hs: {symNt(s, Y) == True{} : Bool},
  +hr: {Sets.allNatIn(termsOf(rest), T) == True{} : Bool}, +hF: {firstsOk(F, T) == True{} : Bool}, +ha: {followsOk(acc, T) == True{} : Bool})
  -> IRes(Y, T, s, rest, x, F, nulls, acc):
  match s:
    case Core.Terminal{+k}:
      Inl{({==}, {==})}
    case Core.Nonterminal{+y, +need}:
      ires_nt(Y, T, y, need, rest, x, F, nulls, acc, ores(T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), Y, T, y, acc, hs, ns_ok(rest, x, F, nulls, acc, T, hr, hF, ha)))

def item_ok_pres(s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +T: +List<Nat>,
  +hr: {Sets.allNatIn(termsOf(rest), T) == True{} : Bool}, +hF: {firstsOk(F, T) == True{} : Bool}, +ha: {followsOk(acc, T) == True{} : Bool})
  -> {followsOk(T.itemFollows(s, rest, x, F, nulls, acc), T) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      ha
    case Core.Nonterminal{+y, +need}:
      add_follows_ok(T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), y, acc, T, ns_ok(rest, x, F, nulls, acc, T, hr, hF, ha), ha)

def item_keep(s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +z: Nat, +m: Maybe<&2, Nat>, +h: {T.followHas(z, m, acc) == True{} : Bool})
  -> {T.followHas(z, m, T.itemFollows(s, rest, x, F, nulls, acc)) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      h
    case Core.Nonterminal{+y, +need}:
      add_follows_keep(T.joinMaybes(T.someAll(T.firstOfItems(rest, F, nulls)), T.maybesIf(Sets.allNull(rest, nulls), T.followsOf(x, acc))), y, acc, z, m, h)

# ======== FOLLOW: ONE RIGHT SIDE ========

# The nonterminals of items.
def ntsList(items: +List<Core.Sym>) -> +List<Nat>:
  match items:
    case Nil{}:
      []
    case Con{Core.Terminal{+k}, rest}:
      ntsList(rest)
    case Con{Core.Nonterminal{+y, +need}, rest}:
      y <> ntsList(rest)

def sym_nt_head(s: Core.Sym, +rest: +List<Core.Sym>, +Y: +List<Nat>, +h: {Sets.allNatIn(ntsList(s <> rest), Y) == True{} : Bool}) -> {symNt(s, Y) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      {==}
    case Core.Nonterminal{+y, +need}:
      Lemma.and_true_left(Sets.natIn(y, Y), Sets.allNatIn(ntsList(rest), Y), h)

def nts_tail(s: Core.Sym, +rest: +List<Core.Sym>, +Y: +List<Nat>, +h: {Sets.allNatIn(ntsList(s <> rest), Y) == True{} : Bool}) -> {Sets.allNatIn(ntsList(rest), Y) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      h
    case Core.Nonterminal{+y, +need}:
      Lemma.and_true_right_side(Sets.natIn(y, Y), Sets.allNatIn(ntsList(rest), Y), h)

def terms_tail(s: Core.Sym, +rest: +List<Core.Sym>, +T: +List<Nat>, +h: {Sets.allNatIn(termsOf(s <> rest), T) == True{} : Bool}) -> {Sets.allNatIn(termsOf(rest), T) == True{} : Bool}:
  match s:
    case Core.Terminal{+k}:
      Lemma.and_true_right_side(Sets.natIn(k, T), Sets.allNatIn(termsOf(rest), T), h)
    case Core.Nonterminal{+y, +need}:
      h

def SRes(+Y: +List<Nat>, +T: +List<Nat>, +items: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>) -> Type:
  Either<({T.suffixFollows(items, x, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.suffixOk(items, x, F, acc, nulls) == True{} : Bool}),
    {Nat.is_le(1n+oMeas(Y, T, T.suffixFollows(items, x, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}>

def ssame_le(+Y: +List<Nat>, +T: +List<Nat>, +items: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, p: {T.suffixFollows(items, x, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.suffixOk(items, x, F, acc, nulls) == True{} : Bool})
  -> {Nat.is_le(oMeas(Y, T, T.suffixFollows(items, x, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match p:
    case (+eq, +ok):
      ometa_eq(Y, T, T.suffixFollows(items, x, F, nulls, acc), acc, eq)

def sres_le(+Y: +List<Nat>, +T: +List<Nat>, +items: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, r: SRes(Y, T, items, x, F, nulls, acc))
  -> {Nat.is_le(oMeas(Y, T, T.suffixFollows(items, x, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      ssame_le(Y, T, items, x, F, nulls, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(oMeas(Y, T, T.suffixFollows(items, x, F, nulls, acc)), oMeas(Y, T, acc), m)

def suffix_to(+items: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +a: +List<T.FollowFact>, +b: +List<T.FollowFact>, +eq: {a == b : +List<T.FollowFact>},
  +h: {T.suffixOk(items, x, F, a, nulls) == True{} : Bool}) -> {T.suffixOk(items, x, F, b, nulls) == True{} : Bool}:
  %eq : {T.suffixOk(items, x, F, _, nulls) == True{} : Bool}
  h

def sj_same2(+Y: +List<Nat>, +T: +List<Nat>, +s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +eq: {T.itemFollows(s, rest, x, F, nulls, acc) == acc : +List<T.FollowFact>}, +ok: {T.itemOk(s, rest, x, F, acc, nulls) == True{} : Bool},
  q: {T.suffixFollows(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc)) == T.itemFollows(s, rest, x, F, nulls, acc) : +List<T.FollowFact>} & {T.suffixOk(rest, x, F, T.itemFollows(s, rest, x, F, nulls, acc), nulls) == True{} : Bool}) -> SRes(Y, T, s <> rest, x, F, nulls, acc):
  match q:
    case (+eq2, +sok):
      Inl{(Equal.trans(+List<T.FollowFact>, T.suffixFollows(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc)), T.itemFollows(s, rest, x, F, nulls, acc), acc, eq2, eq),
        Lemma.and_true_intro(T.itemOk(s, rest, x, F, acc, nulls), T.suffixOk(rest, x, F, acc, nulls), ok, suffix_to(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc), acc, eq, sok)))}

def sj_same(+Y: +List<Nat>, +T: +List<Nat>, +s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +eq: {T.itemFollows(s, rest, x, F, nulls, acc) == acc : +List<T.FollowFact>}, +ok: {T.itemOk(s, rest, x, F, acc, nulls) == True{} : Bool},
  r: SRes(Y, T, rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc))) -> SRes(Y, T, s <> rest, x, F, nulls, acc):
  match r:
    case Inl{q}:
      sj_same2(Y, T, s, rest, x, F, nulls, acc, eq, ok, q)
    case Inr{m}:
      Inr{omeas_to(Y, T, T.itemFollows(s, rest, x, F, nulls, acc), acc, oMeas(Y, T, T.suffixFollows(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc))), eq, m)}

def sj_added(+Y: +List<Nat>, +T: +List<Nat>, +s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  p: {T.itemFollows(s, rest, x, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.itemOk(s, rest, x, F, acc, nulls) == True{} : Bool}, r: SRes(Y, T, rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc))) -> SRes(Y, T, s <> rest, x, F, nulls, acc):
  match p:
    case (+eq, +ok):
      sj_same(Y, T, s, rest, x, F, nulls, acc, eq, ok, r)

def sjoin(+Y: +List<Nat>, +T: +List<Nat>, +s: Core.Sym, +rest: +List<Core.Sym>, +x: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  a: IRes(Y, T, s, rest, x, F, nulls, acc), r: SRes(Y, T, rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc))) -> SRes(Y, T, s <> rest, x, F, nulls, acc):
  match a:
    case Inl{p}:
      sj_added(Y, T, s, rest, x, F, nulls, acc, p, r)
    case Inr{m1}:
      Inr{Lemma.le_trans(1n+oMeas(Y, T, T.suffixFollows(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc))), 1n+oMeas(Y, T, T.itemFollows(s, rest, x, F, nulls, acc)), oMeas(Y, T, acc),
        sres_le(Y, T, rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc), r), m1)}

law sround:
  for items: +List<Core.Sym>
  for +x: Nat
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +Y: +List<Nat>
  for +T: +List<Nat>
  for +hn: {Sets.allNatIn(ntsList(items), Y) == True{} : Bool}
  for +ht: {Sets.allNatIn(termsOf(items), T) == True{} : Bool}
  for +hF: {firstsOk(F, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  SRes(Y, T, items, x, F, nulls, acc)

def sround(items, x, F, nulls, acc, Y, T, hn, ht, hF, ha):
  match items:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{+s, +rest}:
      sjoin(Y, T, s, rest, x, F, nulls, acc, iround(s, rest, x, F, nulls, acc, Y, T, sym_nt_head(s, rest, Y, hn), terms_tail(s, rest, T, ht), hF, ha),
        sround(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc), Y, T, nts_tail(s, rest, Y, hn), terms_tail(s, rest, T, ht), hF,
          item_ok_pres(s, rest, x, F, nulls, acc, T, terms_tail(s, rest, T, ht), hF, ha)))

law suffix_ok_pres:
  for items: +List<Core.Sym>
  for +x: Nat
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +T: +List<Nat>
  for +ht: {Sets.allNatIn(termsOf(items), T) == True{} : Bool}
  for +hF: {firstsOk(F, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  {followsOk(T.suffixFollows(items, x, F, nulls, acc), T) == True{} : Bool}

def suffix_ok_pres(items, x, F, nulls, acc, T, ht, hF, ha):
  match items:
    case Nil{}:
      ha
    case Con{+s, +rest}:
      suffix_ok_pres(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc), T, terms_tail(s, rest, T, ht), hF, item_ok_pres(s, rest, x, F, nulls, acc, T, terms_tail(s, rest, T, ht), hF, ha))

law suffix_keep:
  for items: +List<Core.Sym>
  for +x: Nat
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +z: Nat
  for +m: Maybe<&2, Nat>
  for +h: {T.followHas(z, m, acc) == True{} : Bool}
  {T.followHas(z, m, T.suffixFollows(items, x, F, nulls, acc)) == True{} : Bool}

def suffix_keep(items, x, F, nulls, acc, z, m, h):
  match items:
    case Nil{}:
      h
    case Con{+s, +rest}:
      suffix_keep(rest, x, F, nulls, T.itemFollows(s, rest, x, F, nulls, acc), z, m, item_keep(s, rest, x, F, nulls, acc, z, m, h))

# ======== FOLLOW: ONE ROUND ========

def prodsNt(prods: +List<Core.Production>, +Y: +List<Nat>) -> Bool:
  match prods:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Bool.and(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y))

def PRes(+Y: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>) -> Type:
  Either<({T.followsOnce(prods, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.followsClosed(prods, F, acc, nulls) == True{} : Bool}),
    {Nat.is_le(1n+oMeas(Y, T, T.followsOnce(prods, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}>

def psame_le(+Y: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, p: {T.followsOnce(prods, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.followsClosed(prods, F, acc, nulls) == True{} : Bool})
  -> {Nat.is_le(oMeas(Y, T, T.followsOnce(prods, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match p:
    case (+eq, +cl):
      ometa_eq(Y, T, T.followsOnce(prods, F, nulls, acc), acc, eq)

def pres_le(+Y: +List<Nat>, +T: +List<Nat>, +prods: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, r: PRes(Y, T, prods, F, nulls, acc))
  -> {Nat.is_le(oMeas(Y, T, T.followsOnce(prods, F, nulls, acc)), oMeas(Y, T, acc)) == True{} : Bool}:
  match r:
    case Inl{p}:
      psame_le(Y, T, prods, F, nulls, acc, p)
    case Inr{m}:
      Lemma.le_of_succ_le(oMeas(Y, T, T.followsOnce(prods, F, nulls, acc)), oMeas(Y, T, acc), m)

def oclosed_to(+prods: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +a: +List<T.FollowFact>, +b: +List<T.FollowFact>, +eq: {a == b : +List<T.FollowFact>},
  +h: {T.followsClosed(prods, F, a, nulls) == True{} : Bool}) -> {T.followsClosed(prods, F, b, nulls) == True{} : Bool}:
  %eq : {T.followsClosed(prods, F, _, nulls) == True{} : Bool}
  h

def pj_same2(+Y: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  +eq: {T.suffixFollows(rhs, lhs, F, nulls, acc) == acc : +List<T.FollowFact>}, +ok: {T.suffixOk(rhs, lhs, F, acc, nulls) == True{} : Bool},
  q: {T.followsOnce(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc)) == T.suffixFollows(rhs, lhs, F, nulls, acc) : +List<T.FollowFact>} & {T.followsClosed(rest, F, T.suffixFollows(rhs, lhs, F, nulls, acc), nulls) == True{} : Bool})
  -> PRes(Y, T, Core.Production{lhs, rhs} <> rest, F, nulls, acc):
  match q:
    case (+eq2, +cl):
      Inl{(Equal.trans(+List<T.FollowFact>, T.followsOnce(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc)), T.suffixFollows(rhs, lhs, F, nulls, acc), acc, eq2, eq),
        Lemma.and_true_intro(T.suffixOk(rhs, lhs, F, acc, nulls), T.followsClosed(rest, F, acc, nulls), ok, oclosed_to(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc), acc, eq, cl)))}

def pj_same(+Y: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  +eq: {T.suffixFollows(rhs, lhs, F, nulls, acc) == acc : +List<T.FollowFact>}, +ok: {T.suffixOk(rhs, lhs, F, acc, nulls) == True{} : Bool},
  r: PRes(Y, T, rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc))) -> PRes(Y, T, Core.Production{lhs, rhs} <> rest, F, nulls, acc):
  match r:
    case Inl{q}:
      pj_same2(Y, T, lhs, rhs, rest, F, nulls, acc, eq, ok, q)
    case Inr{m}:
      Inr{omeas_to(Y, T, T.suffixFollows(rhs, lhs, F, nulls, acc), acc, oMeas(Y, T, T.followsOnce(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc))), eq, m)}

def pj_added(+Y: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  p: {T.suffixFollows(rhs, lhs, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.suffixOk(rhs, lhs, F, acc, nulls) == True{} : Bool},
  r: PRes(Y, T, rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc))) -> PRes(Y, T, Core.Production{lhs, rhs} <> rest, F, nulls, acc):
  match p:
    case (+eq, +ok):
      pj_same(Y, T, lhs, rhs, rest, F, nulls, acc, eq, ok, r)

def pjoin(+Y: +List<Nat>, +T: +List<Nat>, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>,
  a: SRes(Y, T, rhs, lhs, F, nulls, acc), r: PRes(Y, T, rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc))) -> PRes(Y, T, Core.Production{lhs, rhs} <> rest, F, nulls, acc):
  match a:
    case Inl{p}:
      pj_added(Y, T, lhs, rhs, rest, F, nulls, acc, p, r)
    case Inr{m1}:
      Inr{Lemma.le_trans(1n+oMeas(Y, T, T.followsOnce(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc))), 1n+oMeas(Y, T, T.suffixFollows(rhs, lhs, F, nulls, acc)), oMeas(Y, T, acc),
        pres_le(Y, T, rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc), r), m1)}

# One FOLLOW round: nothing changes and the facts are closed, or the count drops.
law pround:
  for prods: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +L: +List<Nat>
  for +Y: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(prods, L, T) == True{} : Bool}
  for +hq: {prodsNt(prods, Y) == True{} : Bool}
  for +hF: {firstsOk(F, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  PRes(Y, T, prods, F, nulls, acc)

def pround(prods, F, nulls, acc, L, Y, T, hp, hq, hF, ha):
  match prods:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hr = Lemma.and_true_right_side(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), hp)
      +ht = Lemma.and_true_left(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr)
      +hrest = Lemma.and_true_right_side(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr)
      +hn = Lemma.and_true_left(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), hq)
      +hq2 = Lemma.and_true_right_side(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), hq)
      pjoin(Y, T, lhs, rhs, rest, F, nulls, acc, sround(rhs, lhs, F, nulls, acc, Y, T, hn, ht, hF, ha),
        pround(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc), L, Y, T, hrest, hq2, hF, suffix_ok_pres(rhs, lhs, F, nulls, acc, T, ht, hF, ha)))

law follows_once_ok:
  for prods: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(prods, L, T) == True{} : Bool}
  for +hF: {firstsOk(F, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  {followsOk(T.followsOnce(prods, F, nulls, acc), T) == True{} : Bool}

def follows_once_ok(prods, F, nulls, acc, L, T, hp, hF, ha):
  match prods:
    case Nil{}:
      ha
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +hr = Lemma.and_true_right_side(Sets.natIn(lhs, L), Bool.and(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T)), hp)
      follows_once_ok(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc), L, T, Lemma.and_true_right_side(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr), hF,
        suffix_ok_pres(rhs, lhs, F, nulls, acc, T, Lemma.and_true_left(Sets.allNatIn(termsOf(rhs), T), prodsIn(rest, L, T), hr), hF, ha))

law follows_once_keep:
  for prods: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +z: Nat
  for +m: Maybe<&2, Nat>
  for +h: {T.followHas(z, m, acc) == True{} : Bool}
  {T.followHas(z, m, T.followsOnce(prods, F, nulls, acc)) == True{} : Bool}

def follows_once_keep(prods, F, nulls, acc, z, m, h):
  match prods:
    case Nil{}:
      h
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      follows_once_keep(rest, F, nulls, T.suffixFollows(rhs, lhs, F, nulls, acc), z, m, suffix_keep(rhs, lhs, F, nulls, acc, z, m, h))

# The seed of FOLLOW stays.
law grow_follows_keep:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +z: Nat
  for +m: Maybe<&2, Nat>
  for +h: {T.followHas(z, m, acc) == True{} : Bool}
  {T.followHas(z, m, T.growFollows(n, grammar, F, nulls, acc)) == True{} : Bool}

def grow_follows_keep(n, grammar, F, nulls, acc, z, m, h):
  match n:
    case 0n:
      h
    case 1n+(+p):
      grow_follows_keep(p, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc), z, m, follows_once_keep(grammar, F, nulls, acc, z, m, h))

# ======== FOLLOW: THE GROWTH ENDS CLOSED ========

law grow_follows_stay:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +eq: {T.followsOnce(grammar, F, nulls, acc) == acc : +List<T.FollowFact>}
  {T.growFollows(n, grammar, F, nulls, acc) == acc : +List<T.FollowFact>}

def grow_follows_stay(n, grammar, F, nulls, acc, eq):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(+List<T.FollowFact>, T.followsOnce(grammar, F, nulls, acc), acc, eq) : {T.growFollows(p, grammar, F, nulls, _) == acc : +List<T.FollowFact>}
      grow_follows_stay(p, grammar, F, nulls, acc, eq)

def ofix_same2(+f: Nat, +grammar: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +eq: {T.followsOnce(grammar, F, nulls, acc) == acc : +List<T.FollowFact>}, +cl: {T.followsClosed(grammar, F, acc, nulls) == True{} : Bool})
  -> {T.followsClosed(grammar, F, T.growFollows(f, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc)), nulls) == True{} : Bool}:
  %Equal.sym(+List<T.FollowFact>, T.followsOnce(grammar, F, nulls, acc), acc, eq) : {T.followsClosed(grammar, F, T.growFollows(f, grammar, F, nulls, _), nulls) == True{} : Bool}
  %Equal.sym(+List<T.FollowFact>, T.growFollows(f, grammar, F, nulls, acc), acc, grow_follows_stay(f, grammar, F, nulls, acc, eq)) : {T.followsClosed(grammar, F, _, nulls) == True{} : Bool}
  cl

def ofix_same(+f: Nat, +grammar: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, p: {T.followsOnce(grammar, F, nulls, acc) == acc : +List<T.FollowFact>} & {T.followsClosed(grammar, F, acc, nulls) == True{} : Bool})
  -> {T.followsClosed(grammar, F, T.growFollows(f, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc)), nulls) == True{} : Bool}:
  match p:
    case (+eq, +cl):
      ofix_same2(f, grammar, F, nulls, acc, eq, cl)

def ofix_step(+f: Nat, +grammar: +List<Core.Production>, +F: +List<T.FirstFact>, +nulls: +List<Nat>, +acc: +List<T.FollowFact>, +Y: +List<Nat>, +T: +List<Nat>, r: PRes(Y, T, grammar, F, nulls, acc),
  +hf: {Nat.is_le(oMeas(Y, T, acc), f) == True{} : Bool},
  later: {Nat.is_le(1n+oMeas(Y, T, T.followsOnce(grammar, F, nulls, acc)), f) == True{} : Bool} -> {T.followsClosed(grammar, F, T.growFollows(f, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc)), nulls) == True{} : Bool})
  -> {T.followsClosed(grammar, F, T.growFollows(f, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc)), nulls) == True{} : Bool}:
  match r:
    case Inl{p}:
      ofix_same(f, grammar, F, nulls, acc, p)
    case Inr{m}:
      later(Lemma.le_trans(1n+oMeas(Y, T, T.followsOnce(grammar, F, nulls, acc)), oMeas(Y, T, acc), f, m, hf))

law follows_fix:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +F: +List<T.FirstFact>
  for +nulls: +List<Nat>
  for +acc: +List<T.FollowFact>
  for +L: +List<Nat>
  for +Y: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(grammar, L, T) == True{} : Bool}
  for +hq: {prodsNt(grammar, Y) == True{} : Bool}
  for +hF: {firstsOk(F, T) == True{} : Bool}
  for +ha: {followsOk(acc, T) == True{} : Bool}
  for +hf: {Nat.is_le(1n+oMeas(Y, T, acc), fuel) == True{} : Bool}
  {T.followsClosed(grammar, F, T.growFollows(fuel, grammar, F, nulls, acc), nulls) == True{} : Bool}

def follows_fix(fuel, grammar, F, nulls, acc, L, Y, T, hp, hq, hF, ha, hf):
  match fuel:
    case 0n:
      Empty.absurd({T.followsClosed(grammar, F, acc, nulls) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      ofix_step(f, grammar, F, nulls, acc, Y, T, pround(grammar, F, nulls, acc, L, Y, T, hp, hq, hF, ha), hf,
        h2 => follows_fix(f, grammar, F, nulls, T.followsOnce(grammar, F, nulls, acc), L, Y, T, hp, hq, hF, follows_once_ok(grammar, F, nulls, acc, L, T, hp, hF, ha), h2))

# ======== THE GRAMMAR'S NONTERMINALS ========

def gramNts(prods: +List<Core.Production>) -> +List<Nat>:
  match prods:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, +rhs}, rest}:
      Sets.joinNats(ntsList(rhs), gramNts(rest))

law prods_nt_join:
  for prods: +List<Core.Production>
  for +A: +List<Nat>
  for +Y: +List<Nat>
  for +h: {prodsNt(prods, Y) == True{} : Bool}
  {prodsNt(prods, Sets.joinNats(A, Y)) == True{} : Bool}

def prods_nt_join(prods, A, Y, h):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      Lemma.and_true_intro(Sets.allNatIn(ntsList(rhs), Sets.joinNats(A, Y)), prodsNt(rest, Sets.joinNats(A, Y)),
        all_join_right(ntsList(rhs), A, Y, Lemma.and_true_left(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), h)),
        prods_nt_join(rest, A, Y, Lemma.and_true_right_side(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), h)))

law prods_nt_cons:
  for prods: +List<Core.Production>
  for +y: Nat
  for +Y: +List<Nat>
  for +h: {prodsNt(prods, Y) == True{} : Bool}
  {prodsNt(prods, y <> Y) == True{} : Bool}

def prods_nt_cons(prods, y, Y, h):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      Lemma.and_true_intro(Sets.allNatIn(ntsList(rhs), y <> Y), prodsNt(rest, y <> Y),
        all_nat_weaken(ntsList(rhs), y, Y, Lemma.and_true_left(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), h)),
        prods_nt_cons(rest, y, Y, Lemma.and_true_right_side(Sets.allNatIn(ntsList(rhs), Y), prodsNt(rest, Y), h)))

law prods_nt_self:
  for prods: +List<Core.Production>
  {prodsNt(prods, gramNts(prods)) == True{} : Bool}

def prods_nt_self(prods):
  match prods:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      Lemma.and_true_intro(Sets.allNatIn(ntsList(rhs), Sets.joinNats(ntsList(rhs), gramNts(rest))), prodsNt(rest, Sets.joinNats(ntsList(rhs), gramNts(rest))),
        all_join_left(ntsList(rhs), ntsList(rhs), gramNts(rest), all_nat_refl(ntsList(rhs))),
        prods_nt_join(rest, ntsList(rhs), gramNts(rest), prods_nt_self(rest)))

# ======== THE THREE TABLES CLOSE ========

law grow_firsts_ok:
  for n: Nat
  for +grammar: +List<Core.Production>
  for +nulls: +List<Nat>
  for +acc: +List<T.FirstFact>
  for +L: +List<Nat>
  for +T: +List<Nat>
  for +hp: {prodsIn(grammar, L, T) == True{} : Bool}
  for +ha: {firstsOk(acc, T) == True{} : Bool}
  {firstsOk(T.growFirsts(n, grammar, nulls, acc), T) == True{} : Bool}

def grow_firsts_ok(n, grammar, nulls, acc, L, T, hp, ha):
  match n:
    case 0n:
      ha
    case 1n+(+p):
      grow_firsts_ok(p, grammar, nulls, T.firstsOnce(grammar, nulls, acc), L, T, hp, once_ok(grammar, nulls, acc, L, T, hp, ha))

law all_maybe_weaken:
  for xs: +List<Maybe<&2, Nat>>
  for +y: Maybe<&2, Nat>
  for +ys: +List<Maybe<&2, Nat>>
  for +h: {T.allMaybeIn(xs, ys) == True{} : Bool}
  {T.allMaybeIn(xs, y <> ys) == True{} : Bool}

def all_maybe_weaken(xs, y, ys, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(T.maybeIn(x, y <> ys), T.allMaybeIn(rest, y <> ys),
        Lemma.or_true_right_intro(T.maybeEq(x, y), T.maybeIn(x, ys), Lemma.and_true_left(T.maybeIn(x, ys), T.allMaybeIn(rest, ys), h)),
        all_maybe_weaken(rest, y, ys, Lemma.and_true_right_side(T.maybeIn(x, ys), T.allMaybeIn(rest, ys), h)))

law all_maybe_refl:
  for xs: +List<Maybe<&2, Nat>>
  {T.allMaybeIn(xs, xs) == True{} : Bool}

def all_maybe_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(T.maybeIn(x, x <> rest), T.allMaybeIn(rest, x <> rest),
        Lemma.or_true_left_intro(T.maybeEq(x, x), T.maybeIn(x, rest), maybe_eq_refl(x)), all_maybe_weaken(rest, x, rest, all_maybe_refl(rest)))

# The start symbol's FOLLOW rule holds on any FOLLOW table.
def start_suffix(+start: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>)
  -> {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool}:
  Lemma.and_true_intro(T.itemOk(Core.Nonterminal{start, Core.Anything{}}, [], start, firsts, follows, nulls), True{},
    Lemma.and_true_intro(True{}, Bool.or(False{}, T.allMaybeIn(T.followsOf(start, follows), T.followsOf(start, follows))), {==},
      all_maybe_refl(T.followsOf(start, follows))), {==})

def followY(+grammar: +List<Core.Production>, +start: Nat) -> +List<Nat>:
  start <> gramNts(grammar)

def followSeedUniv(+grammar: +List<Core.Production>, +start: Nat) -> +List<Gll.Desc>:
  followUniv(followY(grammar, start), gramTerms(grammar))

def len_to(+fuel: Nat, +U: +List<Gll.Desc>, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, U), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+Run.countNot(U, []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(U, []), List.length(&2, Gll.Desc, U), C.count_empty(U)) : {Nat.is_le(1n+_, fuel) == True{} : Bool}
  hf

def follows_start(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, followSeedUniv(grammar, start)), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+oMeas(followY(grammar, start), gramTerms(grammar), [T.FollowFact{start, None{}}]), fuel) == True{} : Bool}:
  Lemma.le_trans(1n+oMeas(followY(grammar, start), gramTerms(grammar), [T.FollowFact{start, None{}}]), 1n+Run.countNot(followSeedUniv(grammar, start), []), fuel,
    C.count_mono(followSeedUniv(grammar, start), [], followDescs([T.FollowFact{start, None{}}]), {==}), len_to(fuel, followSeedUniv(grammar, start), hf))

# ======== THE TABLES OF THE PREDICTING PARSER CLOSE ========

# The rounds the three tables need: unseen nullable left sides, FIRST pairs and FOLLOW pairs.
def tableSize(+grammar: +List<Core.Production>, +start: Nat) -> Nat:
  Nat.add(List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), Nat.add(List.length(&2, Gll.Desc, firstUniv(grammar)), List.length(&2, Gll.Desc, followSeedUniv(grammar, start))))

def size_parts(+fuel: Nat, +a: Nat, +b: Nat, +c: Nat, +hf: {Nat.is_le(1n+Nat.add(a, Nat.add(b, c)), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+a, fuel) == True{} : Bool} & {Nat.is_le(1n+b, fuel) == True{} : Bool} & {Nat.is_le(1n+c, fuel) == True{} : Bool}:
  +S = Nat.add(a, Nat.add(b, c))
  (Lemma.le_trans(1n+a, 1n+S, fuel, Lemma.le_add_right(a, Nat.add(b, c)), hf),
    (Lemma.le_trans(1n+b, 1n+S, fuel, Lemma.le_trans(b, Nat.add(b, c), S, Lemma.le_add_right(b, c), Lemma.le_add_left(a, Nat.add(b, c))), hf),
      Lemma.le_trans(1n+c, 1n+S, fuel, Lemma.le_trans(c, Nat.add(b, c), S, Lemma.le_add_left(b, c), Lemma.le_add_left(a, Nat.add(b, c))), hf)))

def follows_closed(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +F: +List<T.FirstFact>, +nulls: +List<Nat>,
  +hF: {firstsOk(F, gramTerms(grammar)) == True{} : Bool}, +hf: {Nat.is_le(1n+List.length(&2, Gll.Desc, followSeedUniv(grammar, start)), fuel) == True{} : Bool})
  -> {T.followsClosed(grammar, F, T.growFollows(fuel, grammar, F, nulls, [T.FollowFact{start, None{}}]), nulls) == True{} : Bool}:
  follows_fix(fuel, grammar, F, nulls, [T.FollowFact{start, None{}}], lhsList(grammar), followY(grammar, start), gramTerms(grammar), prods_self(grammar),
    prods_nt_cons(grammar, start, gramNts(grammar), prods_nt_self(grammar)), hF, {==}, follows_start(fuel, grammar, start, hf))

def seed_has(+start: Nat) -> {T.followHas(start, None{}, [T.FollowFact{start, None{}}]) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(start, start), True{}, Lemma.nat_eq_refl(start)) : {T.maybeIn(None{}, T.maybeIf(_, None{}, [])) == True{} : Bool}
  {==}

def tables_of(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat,
  p: {Nat.is_le(1n+List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), fuel) == True{} : Bool} & {Nat.is_le(1n+List.length(&2, Gll.Desc, firstUniv(grammar)), fuel) == True{} : Bool} & {Nat.is_le(1n+List.length(&2, Gll.Desc, followSeedUniv(grammar, start)), fuel) == True{} : Bool})
  -> {P.tablesClosed(grammar, start, Sets.growNulls(fuel, grammar, []), T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])) == True{} : Bool}:
  match p:
    case (+h1, (+h2, h3)):
      Lemma.and_true_intro(Sets.nullsClosed(grammar, Sets.growNulls(fuel, grammar, [])), Bool.and(T.firstsClosed(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, [])), Bool.and(T.followsClosed(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, [])), Bool.and(T.followHas(start, None{}, T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])), T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))))),
        nulls_closed(fuel, grammar, h1),
        Lemma.and_true_intro(T.firstsClosed(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, [])), Bool.and(T.followsClosed(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, [])), Bool.and(T.followHas(start, None{}, T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])), T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, [])))),
          firsts_closed(fuel, grammar, Sets.growNulls(fuel, grammar, []), h2),
          Lemma.and_true_intro(T.followsClosed(grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, [])), Bool.and(T.followHas(start, None{}, T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])), T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))),
            follows_closed(fuel, grammar, start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), grow_firsts_ok(fuel, grammar, Sets.growNulls(fuel, grammar, []), [], lhsList(grammar), gramTerms(grammar), prods_self(grammar), {==}), h3),
            Lemma.and_true_intro(T.followHas(start, None{}, T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])), T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, [])),
              grow_follows_keep(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}], start, None{}, seed_has(start)),
              start_suffix(start, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}]), Sets.growNulls(fuel, grammar, []))))))

# THE TABLES CLOSE: with fuel 1 + the table size, the nullable, FIRST and FOLLOW tables the
# predicting parser grows are closed, the start symbol is followed by the end, and its
# FOLLOW rule holds: `tablesClosed` (PREDICT.bend) is true, on every grammar.
law tables_closed:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +hf: {Nat.is_le(1n+tableSize(grammar, start), fuel) == True{} : Bool}
  {P.tablesClosed(grammar, start, Sets.growNulls(fuel, grammar, []), T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), T.growFollows(fuel, grammar, T.growFirsts(fuel, grammar, Sets.growNulls(fuel, grammar, []), []), Sets.growNulls(fuel, grammar, []), [T.FollowFact{start, None{}}])) == True{} : Bool}

def tables_closed(fuel, grammar, start, hf):
  tables_of(fuel, grammar, start, size_parts(fuel, List.length(&2, Gll.Desc, nullDescs(lhsList(grammar))), List.length(&2, Gll.Desc, firstUniv(grammar)), List.length(&2, Gll.Desc, followSeedUniv(grammar, start)), hf))
