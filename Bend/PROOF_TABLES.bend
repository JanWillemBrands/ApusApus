import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./FIRST.bend as First
import ./LEMMAS.bend as Lemma
import ./PROOF_SETS.bend as Sets

# CLOSED TABLES ARE SOUND: a forest that reads nothing makes its items nullable, and the
# first token a forest reads is in its items' FIRST set.

# ---- A production's facts, from the check ----

law prod_fact:
  for prods: +List<Spec.Production>
  for q: Nat
  for +x: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +i0: Nat
  for ok: {First.prodsOk(prods, grammar, t, i0) == True{} : Bool}
  for lhsOk: {Spec.lhsIs(prods, q, x) == True{} : Bool}
  {First.prodOk(x, Spec.rhsOf(prods, q), grammar, t, Nat.add(q, i0)) == True{} : Bool}

def prod_fact(prods, q, x, grammar, t, i0, ok, lhsOk):
  match prods q:
    case Nil{} _:
      Empty.absurd({First.prodOk(x, Spec.rhsOf([], q), grammar, t, Nat.add(q, i0)) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      +ex = Lemma.nat_eq_sound(lhs, x, lhsOk)
      here = Lemma.and_true_left(First.prodOk(lhs, rhs, grammar, t, i0), First.prodsOk(rest, grammar, t, 1n+i0), ok)
      %ex : {First.prodOk(_, rhs, grammar, t, i0) == True{} : Bool}
      here
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+p):
      later = Lemma.and_true_right_side(First.prodOk(lhs, rhs, grammar, t, i0), First.prodsOk(rest, grammar, t, 1n+i0), ok)
      +r = prod_fact(rest, p, x, grammar, t, 1n+i0, later, lhsOk)
      %Lemma.add_succ_right(p, i0) : {First.prodOk(x, Spec.rhsOf(rest, p), grammar, t, _) == True{} : Bool}
      r

# The facts of production q of x in the whole grammar.
law prod_at:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for +t: Gll.Tables
  for ok: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {First.prodOk(x, Spec.rhsOf(grammar, q), grammar, t, q) == True{} : Bool}

def prod_at(grammar, q, x, t, ok, lhsOk):
  +r = prod_fact(grammar, q, x, grammar, t, 0n, ok, lhsOk)
  %Lemma.add_zero_right(q) : {First.prodOk(x, Spec.rhsOf(grammar, q), grammar, t, _) == True{} : Bool}
  r

law prod_nul:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for +t: Gll.Tables
  for ok: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for nul: {Gll.nulOf(Gll.infoItems(Spec.rhsOf(grammar, q), t)) == True{} : Bool}
  {Gll.boolAt(Gll.nulTab(t), x) == True{} : Bool}

def prod_nul(grammar, q, x, t, ok, lhsOk, nul):
  +info = Gll.infoItems(Spec.rhsOf(grammar, q), t)
  +all = prod_at(grammar, q, x, t, ok, lhsOk)
  +nulOk = Lemma.and_true_left(Bool.or(Bool.not(Gll.nulOf(info)), Gll.boolAt(Gll.nulTab(t), x)), Bool.and(First.lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x)), First.followsOk(Gll.nestFuel(), Gll.MItems{}, Spec.rhsOf(grammar, q), [], grammar, t, q, [], 0n)), all)
  %nul : {Bool.or(Bool.not(_), Gll.boolAt(Gll.nulTab(t), x)) == True{} : Bool}
  nulOk

law prod_first:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for +t: Gll.Tables
  for ok: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for lhsOk: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +tok: Maybe<&2, Nat>
  for h: {Gll.lsHas(tok, Gll.firstOf(Gll.infoItems(Spec.rhsOf(grammar, q), t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.lsAt(Gll.fstTab(t), x)) == True{} : Bool}

def prod_first(grammar, q, x, t, ok, lhsOk, tok, h):
  +info = Gll.infoItems(Spec.rhsOf(grammar, q), t)
  +all = prod_at(grammar, q, x, t, ok, lhsOk)
  +rest = Lemma.and_true_right_side(Bool.or(Bool.not(Gll.nulOf(info)), Gll.boolAt(Gll.nulTab(t), x)), Bool.and(First.lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x)), First.followsOk(Gll.nestFuel(), Gll.MItems{}, Spec.rhsOf(grammar, q), [], grammar, t, q, [], 0n)), all)
  sub = Lemma.and_true_left(First.lsSub(Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x)), First.followsOk(Gll.nestFuel(), Gll.MItems{}, Spec.rhsOf(grammar, q), [], grammar, t, q, [], 0n), rest)
  Sets.ls_sub_has(tok, Gll.firstOf(info), Gll.lsAt(Gll.fstTab(t), x), sub, h)

# ---- Info of a sequence: an item followed by the rest ----

law cons_first_left:
  for +h: Gll.Info
  for +r: Gll.Info
  for +tok: Maybe<&2, Nat>
  for e: {Gll.lsHas(tok, Gll.firstOf(h)) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoCons(h, r))) == True{} : Bool}

def cons_first_left(h, r, tok, e):
  match h r:
    case Gll.Info{True{}, +f1} Gll.Info{n2, +f2}:
      Sets.ls_has_union_left(tok, f1, f2, e)
    case Gll.Info{False{}, f1} Gll.Info{n2, f2}:
      e

law cons_first_right:
  for +h: Gll.Info
  for +r: Gll.Info
  for +tok: Maybe<&2, Nat>
  for nul: {Gll.nulOf(h) == True{} : Bool}
  for e: {Gll.lsHas(tok, Gll.firstOf(r)) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoCons(h, r))) == True{} : Bool}

def cons_first_right(h, r, tok, nul, e):
  match h r:
    case Gll.Info{True{}, +f1} Gll.Info{n2, +f2}:
      Sets.ls_has_union_right(tok, f1, f2, e)
    case Gll.Info{False{}, f1} Gll.Info{n2, f2}:
      Empty.absurd({Gll.lsHas(tok, f1) == True{} : Bool}, Lemma.false_is_not_true(nul))

law cons_nul:
  for +h: Gll.Info
  for +r: Gll.Info
  for nh: {Gll.nulOf(h) == True{} : Bool}
  for nr: {Gll.nulOf(r) == True{} : Bool}
  {Gll.nulOf(Gll.infoCons(h, r)) == True{} : Bool}

def cons_nul(h, r, nh, nr):
  match h r:
    case Gll.Info{True{}, f1} Gll.Info{n2, f2}:
      nr
    case Gll.Info{False{}, f1} Gll.Info{n2, f2}:
      nh

law cons_nul_head:
  for +h: Gll.Info
  for +r: Gll.Info
  for e: {Gll.nulOf(Gll.infoCons(h, r)) == True{} : Bool}
  {Gll.nulOf(h) == True{} : Bool}

def cons_nul_head(h, r, e):
  match h r:
    case Gll.Info{True{}, f1} Gll.Info{n2, f2}:
      {==}
    case Gll.Info{False{}, f1} Gll.Info{n2, f2}:
      e

law cons_first_inv:
  for +h: Gll.Info
  for +r: Gll.Info
  for +tok: Maybe<&2, Nat>
  for e: {Gll.lsHas(tok, Gll.firstOf(Gll.infoCons(h, r))) == True{} : Bool}
  Either<{Gll.lsHas(tok, Gll.firstOf(h)) == True{} : Bool}, {Gll.lsHas(tok, Gll.firstOf(r)) == True{} : Bool}>

def cons_first_inv(h, r, tok, e):
  match h r:
    case Gll.Info{True{}, +f1} Gll.Info{n2, +f2}:
      Sets.ls_has_union_inv(tok, f1, f2, e)
    case Gll.Info{False{}, f1} Gll.Info{n2, f2}:
      Inl{e}

law first_bracket:
  for +kind: Spec.Bracket
  for +x: Gll.Info
  {Gll.firstOf(Gll.infoBracket(kind, x)) == Gll.firstOf(x) : Gll.LSet}

def first_bracket(kind, x):
  match x:
    case Gll.Info{n, f}:
      {==}

law nul_group:
  for +x: Gll.Info
  {Gll.nulOf(Gll.infoBracket(Spec.Group{}, x)) == Gll.nulOf(x) : Bool}

def nul_group(x):
  match x:
    case Gll.Info{n, f}:
      {==}

law nul_skippable:
  for +kind: Spec.Bracket
  for +x: Gll.Info
  for sk: {Gll.canSkip(kind) == True{} : Bool}
  {Gll.nulOf(Gll.infoBracket(kind, x)) == True{} : Bool}

def nul_skippable(kind, x, sk):
  match x:
    case Gll.Info{n, f}:
      Lemma.or_true_left_intro(Gll.canSkip(kind), n, sk)

law empty_has_not:
  for +tok: Maybe<&2, Nat>
  for e: {Gll.lsHas(tok, Gll.emptyLS()) == True{} : Bool}
  Empty

def empty_has_not(tok, e):
  match tok:
    case None{}:
      Lemma.false_is_not_true(e)
    case Some{+t}:
      Lemma.false_is_not_true(e)

# ---- Info of a bracket's alternatives ----

law first_or_left:
  for +x: Gll.Info
  for +y: Gll.Info
  for +tok: Maybe<&2, Nat>
  for h: {Gll.lsHas(tok, Gll.firstOf(x)) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOr(x, y))) == True{} : Bool}

def first_or_left(x, y, tok, h):
  match x y:
    case Gll.Info{n1, +f1} Gll.Info{n2, +f2}:
      Sets.ls_has_union_left(tok, f1, f2, h)

law first_or_right:
  for +x: Gll.Info
  for +y: Gll.Info
  for +tok: Maybe<&2, Nat>
  for h: {Gll.lsHas(tok, Gll.firstOf(y)) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOr(x, y))) == True{} : Bool}

def first_or_right(x, y, tok, h):
  match x y:
    case Gll.Info{n1, +f1} Gll.Info{n2, +f2}:
      Sets.ls_has_union_right(tok, f1, f2, h)

law nul_or_left:
  for +x: Gll.Info
  for +y: Gll.Info
  for h: {Gll.nulOf(x) == True{} : Bool}
  {Gll.nulOf(Gll.infoOr(x, y)) == True{} : Bool}

def nul_or_left(x, y, h):
  match x y:
    case Gll.Info{+n1, f1} Gll.Info{n2, f2}:
      Lemma.or_true_left_intro(n1, n2, h)

law nul_or_right:
  for +x: Gll.Info
  for +y: Gll.Info
  for h: {Gll.nulOf(y) == True{} : Bool}
  {Gll.nulOf(Gll.infoOr(x, y)) == True{} : Bool}

def nul_or_right(x, y, h):
  match x y:
    case Gll.Info{+n1, f1} Gll.Info{+n2, f2}:
      Lemma.or_true_right_intro(n1, n2, h)

law alt_first:
  for alts: +List<+List<Spec.Item>>
  for a: Nat
  for +f: Nat
  for +t: Gll.Tables
  for +tok: Maybe<&2, Nat>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for h: {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MItems{}, Spec.altOf(alts, a), [], t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}

def alt_first(alts, a, f, t, tok, isA, h):
  match alts a:
    case Nil{} 0n:
      Empty.absurd({Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], [], t))) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Nil{} 1n+b:
      Empty.absurd({Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], [], t))) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Con{+alt, +rest} 0n:
      first_or_left(Gll.infoOf(f, Gll.MItems{}, alt, [], t), Gll.infoOf(1n+f, Gll.MAlts{}, [], rest, t), tok, h)
    case Con{+alt, +rest} 1n+(+b):
      first_or_right(Gll.infoOf(f, Gll.MItems{}, alt, [], t), Gll.infoOf(1n+f, Gll.MAlts{}, [], rest, t), tok, alt_first(rest, b, f, t, tok, isA, h))

law alt_nul:
  for alts: +List<+List<Spec.Item>>
  for a: Nat
  for +f: Nat
  for +t: Gll.Tables
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for h: {Gll.nulOf(Gll.infoOf(f, Gll.MItems{}, Spec.altOf(alts, a), [], t)) == True{} : Bool}
  {Gll.nulOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], alts, t)) == True{} : Bool}

def alt_nul(alts, a, f, t, isA, h):
  match alts a:
    case Nil{} 0n:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], [], t)) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Nil{} 1n+b:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MAlts{}, [], [], t)) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Con{+alt, +rest} 0n:
      nul_or_left(Gll.infoOf(f, Gll.MItems{}, alt, [], t), Gll.infoOf(1n+f, Gll.MAlts{}, [], rest, t), h)
    case Con{+alt, +rest} 1n+(+b):
      nul_or_right(Gll.infoOf(f, Gll.MItems{}, alt, [], t), Gll.infoOf(1n+f, Gll.MAlts{}, [], rest, t), alt_nul(rest, b, f, t, isA, h))

# ---- Info of the rounds of a loop: n copies of ( τ ) ----

law times_first_pick:
  for +f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +t: Gll.Tables
  for +tok: Maybe<&2, Nat>
  for +restInfo: Gll.Info
  for c: Either<{Gll.lsHas(tok, Gll.firstOf(Gll.infoBracket(Spec.Group{}, Gll.infoOf(f, Gll.MAlts{}, [], alts, t)))) == True{} : Bool}, {Gll.lsHas(tok, Gll.firstOf(restInfo)) == True{} : Bool}>
  for later: {Gll.lsHas(tok, Gll.firstOf(restInfo)) == True{} : Bool} -> {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}

def times_first_pick(f, alts, t, tok, restInfo, c, later):
  match c:
    case Inl{here}:
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      %first_bracket(Spec.Group{}, x) : {Gll.lsHas(tok, _) == True{} : Bool}
      here
    case Inr{there}:
      later(there)

# A token first in some rounds of a loop is first in the loop's alternatives.
law times_first:
  for n: Nat
  for +f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +t: Gll.Tables
  for +tok: Maybe<&2, Nat>
  for h: {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.times(n, Spec.Brack{Spec.Group{}, alts}), [], t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}

def times_first(n, f, alts, t, tok, h):
  match n:
    case 0n:
      Empty.absurd({Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}, empty_has_not(tok, h))
    case 1n+(+m):
      +head = Gll.infoBracket(Spec.Group{}, Gll.infoOf(f, Gll.MAlts{}, [], alts, t))
      +restInfo = Gll.infoOf(1n+f, Gll.MItems{}, Spec.times(m, Spec.Brack{Spec.Group{}, alts}), [], t)
      times_first_pick(f, alts, t, tok, restInfo, cons_first_inv(head, restInfo, tok, h),
        there => times_first(m, f, alts, t, tok, there))

# Rounds that read nothing, at least one of them: the loop's alternatives are nullable.
law times_nul:
  for +m: Nat
  for +f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +t: Gll.Tables
  for h: {Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.times(1n+m, Spec.Brack{Spec.Group{}, alts}), [], t)) == True{} : Bool}
  {Gll.nulOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t)) == True{} : Bool}

def times_nul(m, f, alts, t, h):
  +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
  +head = Gll.infoBracket(Spec.Group{}, x)
  +restInfo = Gll.infoOf(1n+f, Gll.MItems{}, Spec.times(m, Spec.Brack{Spec.Group{}, alts}), [], t)
  +nh = cons_nul_head(head, restInfo, h)
  %nul_group(x) : {_ == True{} : Bool}
  nh

# ---- Lists that read nothing ----

law append_nil_left:
  for x: +List<Nat>
  for -y: +List<Nat>
  for e: {List.append(&2, Nat, x, y) == [] : +List<Nat>}
  {x == [] : +List<Nat>}

def append_nil_left(x, y, e):
  match x:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      Empty.absurd({h <> r == [] : +List<Nat>}, Lemma.nil_is_not_cons(h, List.append(&2, Nat, r, y), Equal.sym(+List<Nat>, h <> List.append(&2, Nat, r, y), [], e)))

law append_nil_right_part:
  for x: +List<Nat>
  for +y: +List<Nat>
  for e: {List.append(&2, Nat, x, y) == [] : +List<Nat>}
  {y == [] : +List<Nat>}

def append_nil_right_part(x, y, e):
  match x:
    case Nil{}:
      e
    case Con{+h, +r}:
      Empty.absurd({y == [] : +List<Nat>}, Lemma.nil_is_not_cons(h, List.append(&2, Nat, r, y), Equal.sym(+List<Nat>, h <> List.append(&2, Nat, r, y), [], e)))

# The alternatives are nullable when the chosen one is, at any nesting fuel.
law alts_nul_of:
  for f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +t: Gll.Tables
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for ih: @g: Nat -> {Gll.nulOf(Gll.infoOf(g, Gll.MItems{}, Spec.altOf(alts, a), [], t)) == True{} : Bool}
  {Gll.nulOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t)) == True{} : Bool}

def alts_nul_of(f, alts, a, t, isA, ih):
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      alt_nul(alts, a, g, t, isA, ih(g))

law nul_positive:
  for +x: Gll.Info
  {Gll.nulOf(Gll.infoBracket(Spec.Positive{}, x)) == Gll.nulOf(x) : Bool}

def nul_positive(x):
  match x:
    case Gll.Info{n, f}:
      {==}

law positive_nul:
  for rs: +List<Spec.Tree>
  for +f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +t: Gll.Tables
  for roundsP: {Spec.roundsOk(Spec.Positive{}, rs) == True{} : Bool}
  for nulRs: {Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), [], t)) == True{} : Bool}
  {Gll.nulOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t)) == True{} : Bool}

def positive_nul(rs, f, alts, t, roundsP, nulRs):
  match rs:
    case Nil{}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t)) == True{} : Bool}, Lemma.false_is_not_true(roundsP))
    case Con{r, +rr}:
      times_nul(List.length(&2, Spec.Tree, rr), f, alts, t, nulRs)

# ---- NULLABLE IS SOUND: a forest that fits the items and reads nothing ----

law nul_sound:
  for forest: +List<Spec.Tree>
  for +fuel: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for empty: {Spec.leaves(forest) == [] : +List<Nat>}
  {Gll.nulOf(Gll.infoOf(fuel, Gll.MItems{}, items, [], t)) == True{} : Bool}

def nul_sound(forest, fuel, items, grammar, t, pc, fit, empty):
  match forest fuel items:
    case Nil{} 0n _:
      {==}
    case Con{t0, ts} 0n _:
      {==}
    case Nil{} 1n+(+f) Nil{}:
      {==}
    case Nil{} 1n+(+f) Con{it, rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, it <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{t0, ts} 1n+(+f) Nil{}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t)) == True{} : Bool}, Lemma.nil_is_not_cons(kind, Spec.leaves(ts), Equal.sym(+List<Nat>, kind <> Spec.leaves(ts), [], empty)))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{kind}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      nulCh = nul_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, append_nil_left(Spec.leaves(ch), Spec.leaves(ts), e2))
      nx = prod_nul(grammar, q, x, t, pc, lhsOk, nulCh)
      cons_nul(Gll.Info{Gll.boolAt(Gll.nulTab(t), x), Gll.lsAt(Gll.fstTab(t), x)}, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nx,
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      nulX = alts_nul_of(f, alts, a, t, isA, g => nul_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, append_nil_left(Spec.leaves(ch), Spec.leaves(ts), e2)))
      nh = Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Group{}, x)), Gll.nulOf(x), True{}, nul_group(x), nulX)
      cons_nul(Gll.infoBracket(Spec.Group{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nh,
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +both = fit
      fitTs = Lemma.and_true_right_side(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Optional{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Optional{}, x, {==}),
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Optional{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Optional{}, x, {==}),
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fit, empty))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      nul_sound(ts, 1n+f, rest, grammar, t, pc, fit, empty)
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      +both = fit
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Closure{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Closure{}, x, {==}),
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, append_nil_right_part(Spec.leaves(rs), Spec.leaves(ts), e2)))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      roundsP = Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), inner)
      fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      nulRs = nul_sound(rs, 1n+f, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), grammar, t, pc, fitRs, append_nil_left(Spec.leaves(rs), Spec.leaves(ts), e2))
      nulX = positive_nul(rs, f, alts, t, roundsP, nulRs)
      nh = Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Positive{}, x)), Gll.nulOf(x), True{}, nul_positive(x), nulX)
      cons_nul(Gll.infoBracket(Spec.Positive{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nh,
        nul_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, append_nil_right_part(Spec.leaves(rs), Spec.leaves(ts), e2)))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))

# ---- FIRST IS SOUND: the first token a fitting forest reads is in FIRST ----

def tailOf(l: +List<Nat>) -> +List<Nat>:
  match l:
    case Nil{}:
      []
    case Con{h, t}:
      t

law cons_head_eq:
  for -h: Nat
  for -t: +List<Nat>
  for -k0: Nat
  for -w: +List<Nat>
  for e: {h <> t == k0 <> w : +List<Nat>}
  {h == k0 : Nat}

def cons_head_eq(h, t, k0, w, e):
  Equal.cong(+List<Nat>, Nat, l => Lemma.headOr(l, 0n), h <> t, k0 <> w, e)

law first_split:
  for lc: +List<Nat>
  for +lt: +List<Nat>
  for +k0: Nat
  for +w: +List<Nat>
  for -G: Type
  for lv: {List.append(&2, Nat, lc, lt) == k0 <> w : +List<Nat>}
  for here: {lc == k0 <> tailOf(lc) : +List<Nat>} -> G
  for later: {lc == [] : +List<Nat>} -> {lt == k0 <> w : +List<Nat>} -> G
  G

def first_split(lc, lt, k0, w, G, lv, here, later):
  match lc:
    case Nil{}:
      later({==}, lv)
    case Con{+h, +r}:
      +eh = cons_head_eq(h, List.append(&2, Nat, r, lt), k0, w, lv)
      here(Equal.cong(Nat, +List<Nat>, v => v <> r, h, k0, eh))

# The alternatives start with what the chosen one starts with, at any nesting fuel.
law alts_first_of:
  for f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +t: Gll.Tables
  for +tok: Maybe<&2, Nat>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for ih: @g: Nat -> {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(g, Gll.MItems{}, Spec.altOf(alts, a), [], t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}

def alts_first_of(f, alts, a, t, tok, isA, ih):
  match f:
    case 0n:
      Sets.any_has(tok, True{}, [], True{}, {==})
    case 1n+(+g):
      alt_first(alts, a, g, t, tok, isA, ih(g))

law first_sound:
  for forest: +List<Spec.Tree>
  for +fuel: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +k0: Nat
  for +w: +List<Nat>
  for +lv: {Spec.leaves(forest) == k0 <> w : +List<Nat>}
  {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(fuel, Gll.MItems{}, items, [], t))) == True{} : Bool}

def first_sound(forest, fuel, items, grammar, t, pc, fit, k0, w, lv):
  match forest fuel items:
    case Nil{} 0n _:
      {==}
    case Con{t0, ts} 0n _:
      {==}
    case Nil{} 1n+(+f) Nil{}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t))) == True{} : Bool}, Lemma.nil_is_not_cons(k0, w, lv))
    case Nil{} 1n+(+f) Con{it, rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, it <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{t0, ts} 1n+(+f) Nil{}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      isK = Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), fit)
      +ek = cons_head_eq(kind, Spec.leaves(ts), k0, w, lv)
      eq = Equal.trans(Bool, Nat.is_eq(k0, k), Nat.is_eq(kind, k), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(v, k), k0, kind, Equal.sym(Nat, kind, k0, ek)), isK)
      Lemma.or_true_left_intro(Nat.is_eq(k0, k), False{}, eq)
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Leaf{+kind}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      +inner = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), fit)
      +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), fit)
      +h = {Gll.Info{Gll.boolAt(Gll.nulTab(t), x), Gll.lsAt(Gll.fstTab(t), x)} : Gll.Info}
      first_split(Spec.leaves(ch), Spec.leaves(ts), k0, w, {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t))) == True{} : Bool}, lv,
        eqCh => cons_first_left(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, prod_first(grammar, q, x, t, pc, lhsOk, Some{k0}, first_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, k0, tailOf(Spec.leaves(ch)), eqCh))),
        eqNil => eqTs => cons_first_right(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, prod_nul(grammar, q, x, t, pc, lhsOk, nul_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, eqNil)), first_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, k0, w, eqTs)))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{+q, +ch}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      +inner = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), fit)
      +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), fit)
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(Spec.Group{}, x)
      first_split(Spec.leaves(ch), Spec.leaves(ts), k0, w, {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t))) == True{} : Bool}, lv,
        eqCh => cons_first_left(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(Spec.Group{}, x)), alts_first_of(f, alts, a, t, Some{k0}, isA, g => first_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, k0, tailOf(Spec.leaves(ch)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Group{}, x)), Gll.nulOf(x), True{}, nul_group(x), alts_nul_of(f, alts, a, t, isA, g => nul_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, eqNil))), first_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, k0, w, eqTs)))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +optP = Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +inner = Lemma.and_true_left(optP, Spec.fits(ts, grammar, rest), fit)
      +inner2 = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +isA = Lemma.and_true_right_side(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), inner2)
      +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitTs = Lemma.and_true_right_side(optP, Spec.fits(ts, grammar, rest), fit)
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(Spec.Optional{}, x)
      first_split(Spec.leaves(ch), Spec.leaves(ts), k0, w, {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t))) == True{} : Bool}, lv,
        eqCh => cons_first_left(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(Spec.Optional{}, x)), alts_first_of(f, alts, a, t, Some{k0}, isA, g => first_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, k0, tailOf(Spec.leaves(ch)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, nul_skippable(Spec.Optional{}, x, {==}), first_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, k0, w, eqTs)))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{+a, +ch}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_first_right(Gll.infoBracket(Spec.Optional{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, nul_skippable(Spec.Optional{}, x, {==}), first_sound(ts, 1n+f, rest, grammar, t, pc, fit, k0, w, lv))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      first_sound(ts, 1n+f, rest, grammar, t, pc, fit, k0, w, lv)
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Terminal{k}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Sym{Spec.Nonterminal{x}} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Group{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Optional{}, alts} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      +tms = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +roundsP = Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tms), inner)
      +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tms), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(Spec.Closure{}, x)
      first_split(Spec.leaves(rs), Spec.leaves(ts), k0, w, {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Closure{}, alts} <> rest, [], t))) == True{} : Bool}, lv,
        eqCh => cons_first_left(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(Spec.Closure{}, x)), times_first(List.length(&2, Spec.Tree, rs), f, alts, t, Some{k0}, first_sound(rs, 1n+f, tms, grammar, t, pc, fitRs, k0, tailOf(Spec.leaves(rs)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, nul_skippable(Spec.Closure{}, x, {==}), first_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, k0, w, eqTs)))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      +tms = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +roundsP = Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tms), inner)
      +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tms), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(Spec.Positive{}, x)
      first_split(Spec.leaves(rs), Spec.leaves(ts), k0, w, {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Brack{Spec.Positive{}, alts} <> rest, [], t))) == True{} : Bool}, lv,
        eqCh => cons_first_left(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(Spec.Positive{}, x)), times_first(List.length(&2, Spec.Tree, rs), f, alts, t, Some{k0}, first_sound(rs, 1n+f, tms, grammar, t, pc, fitRs, k0, tailOf(Spec.leaves(rs)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), Some{k0}, Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Positive{}, x)), Gll.nulOf(x), True{}, nul_positive(x), positive_nul(rs, f, alts, t, roundsP, nul_sound(rs, 1n+f, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), grammar, t, pc, fitRs, eqNil))), first_sound(ts, 1n+f, rest, grammar, t, pc, fitTs, k0, w, eqTs)))
    case Con{Spec.Loop{+rs}, +ts} 1n+(+f) Con{Spec.Eps{}, +rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
