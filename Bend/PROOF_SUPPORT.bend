import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./CHECK.bend as Check
import ./UNBEATEN.bend as Unb
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_SUBPARSE.bend as Sub
import ./PROOF_GUARD.bend as PG
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# THE PRUNING KEEPS EVERY FOREST OF JUDGED STEPS. UNBEATEN.bend prunes the judged steps
# of a sub-parse from below, and hands the result out only when `closedOver` says it
# holds every judged step it supports. Then every forest whose steps are all judged has
# all of its steps in the pruned set: walking the forest from its leaves up, each step
# is supported by the steps below and before it, which are in the pruned set already.

# ======== SMALL FACTS ========

law or_not_true:
  for a: Bool
  for +b: Bool
  for e: {Bool.or(Bool.not(a), b) == True{} : Bool}
  for ea: {a == True{} : Bool}
  {b == True{} : Bool}

def or_not_true(a, b, e, ea):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, Lemma.false_is_not_true(ea))

law closed_pick:
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for cases: Either<{y == x : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +okX: {Bool.or(Bool.not(Unb.supported(K, grammar, input, x)), Spec.bsrMember(x, K)) == True{} : Bool}
  for +sup: {Unb.supported(K, grammar, input, y) == True{} : Bool}
  for later: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Spec.bsrMember(y, K) == True{} : Bool}
  {Spec.bsrMember(y, K) == True{} : Bool}

def closed_pick(x, rest, y, K, grammar, input, cases, okX, sup, later):
  match cases:
    case Inl{same0}:
      +same = {same0 : {y == x : Spec.Bsr}}
      +supX = Equal.trans(Bool, Unb.supported(K, grammar, input, x), Unb.supported(K, grammar, input, y), True{}, Equal.cong(Spec.Bsr, Bool, v => Unb.supported(K, grammar, input, v), x, y, Equal.sym(Spec.Bsr, y, x, same)), sup)
      +memX = or_not_true(Unb.supported(K, grammar, input, x), Spec.bsrMember(x, K), okX, supX)
      Equal.trans(Bool, Spec.bsrMember(y, K), Spec.bsrMember(x, K), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, K), y, x, same), memX)
    case Inr{m}:
      later(m)

# A judged step that the pruned set supports is in it.
law closed_mem:
  for es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  for +sup: {Unb.supported(K, grammar, input, y) == True{} : Bool}
  {Spec.bsrMember(y, K) == True{} : Bool}

def closed_mem(es, K, grammar, input, closed, y, m, sup):
  match es:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, K) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+x, +rest}:
      +hx = Bool.or(Bool.not(Unb.supported(K, grammar, input, x)), Spec.bsrMember(x, K))
      +okX = Lemma.and_true_left(hx, Unb.closedOver(rest, K, grammar, input), closed)
      +okR = Lemma.and_true_right_side(hx, Unb.closedOver(rest, K, grammar, input), closed)
      closed_pick(x, rest, y, K, grammar, input, G.ebnf_member_cases(y, x, rest, m), okX, sup,
        later => closed_mem(rest, K, grammar, input, okR, y, later, sup))

# ======== FINDING A STEP ========

law step_is_self:
  for +idx: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Unb.stepIs(idx, path, i, j, Spec.Bsr{Spec.Slot{idx, path}, i, k, j}) == True{} : Bool}

def step_is_self(idx, path, i, k, j):
  Lemma.and_true_intro(Nat.is_eq(idx, idx), Bool.and(Gll.natsEq(path, path), Bool.and(Nat.is_eq(i, i), Nat.is_eq(j, j))), Lemma.nat_eq_refl(idx),
    Lemma.and_true_intro(Gll.natsEq(path, path), Bool.and(Nat.is_eq(i, i), Nat.is_eq(j, j)), Sub.nats_eq_refl(path),
      Lemma.and_true_intro(Nat.is_eq(i, i), Nat.is_eq(j, j), Lemma.nat_eq_refl(i), Lemma.nat_eq_refl(j))))

law has_step_pick:
  for +idx: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for cases: Either<{Spec.Bsr{Spec.Slot{idx, path}, i, k, j} == x : Spec.Bsr}, {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, path}, i, k, j}, rest) == True{} : Bool}>
  for later: {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, path}, i, k, j}, rest) == True{} : Bool} -> {Unb.hasStep(rest, idx, path, i, j) == True{} : Bool}
  {Unb.hasStep(x <> rest, idx, path, i, j) == True{} : Bool}

def has_step_pick(idx, path, i, k, j, x, rest, cases, later):
  match cases:
    case Inl{same}:
      %same : {Bool.or(Unb.stepIs(idx, path, i, j, _), Unb.hasStep(rest, idx, path, i, j)) == True{} : Bool}
      Lemma.or_true_left_intro(Unb.stepIs(idx, path, i, j, Spec.Bsr{Spec.Slot{idx, path}, i, k, j}), Unb.hasStep(rest, idx, path, i, j), step_is_self(idx, path, i, k, j))
    case Inr{m}:
      Lemma.or_true_right_intro(Unb.stepIs(idx, path, i, j, x), Unb.hasStep(rest, idx, path, i, j), later(m))

# A step of the set makes hasStep true.
law has_step_of:
  for set: +List<Spec.Bsr>
  for +idx: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for m: {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, path}, i, k, j}, set) == True{} : Bool}
  {Unb.hasStep(set, idx, path, i, j) == True{} : Bool}

def has_step_of(set, idx, path, i, k, j, m):
  match set:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, G.ebnf_not_in_empty(Spec.Bsr{Spec.Slot{idx, path}, i, k, j}, m))
    case Con{+x, +rest}:
      has_step_pick(idx, path, i, k, j, x, rest, G.ebnf_member_cases(Spec.Bsr{Spec.Slot{idx, path}, i, k, j}, x, rest, m),
        later => has_step_of(rest, idx, path, i, k, j, later))

law ends_prod_pick:
  for b: Bool
  for +q: Nat
  for +m: Nat
  for +eb: {Nat.is_eq(m, q) == b : Bool}
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +lt: {Nat.is_lt(q, 1n+m) == True{} : Bool}
  for +lhs: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +has: {Unb.hasStep(set, q, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))], k, j) == True{} : Bool}
  for later: {Nat.is_lt(q, m) == True{} : Bool} -> {Unb.endsProd(m, set, grammar, x, k, j) == True{} : Bool}
  {Unb.endsProd(1n+m, set, grammar, x, k, j) == True{} : Bool}

def ends_prod_pick(b, q, m, eb, set, grammar, x, k, j, lt, lhs, has, later):
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(m, q, eb)
      +hit = Bool.and(Spec.lhsIs(grammar, m, x), Unb.hasStep(set, m, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, m))], k, j))
      +hitQ = Lemma.and_true_intro(Spec.lhsIs(grammar, q, x), Unb.hasStep(set, q, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))], k, j), lhs, has)
      +hitM = Equal.trans(Bool, hit, Bool.and(Spec.lhsIs(grammar, q, x), Unb.hasStep(set, q, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))], k, j)), True{}, Equal.cong(Nat, Bool, v => Bool.and(Spec.lhsIs(grammar, v, x), Unb.hasStep(set, v, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, v))], k, j)), m, q, e), hitQ)
      Lemma.or_true_left_intro(hit, Unb.endsProd(m, set, grammar, x, k, j), hitM)
    case False{}:
      Lemma.or_true_right_intro(Bool.and(Spec.lhsIs(grammar, m, x), Unb.hasStep(set, m, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, m))], k, j)), Unb.endsProd(m, set, grammar, x, k, j), later(Lemma.lt_succ_ne(q, m, lt, eb)))

# A production of x, below n, that ends from k to j makes endsProd true.
law ends_prod_of:
  for n: Nat
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +k: Nat
  for +j: Nat
  for +q: Nat
  for +lt: {Nat.is_lt(q, n) == True{} : Bool}
  for +lhs: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +has: {Unb.hasStep(set, q, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))], k, j) == True{} : Bool}
  {Unb.endsProd(n, set, grammar, x, k, j) == True{} : Bool}

def ends_prod_of(n, set, grammar, x, k, j, q, lt, lhs, has):
  match n:
    case 0n:
      Empty.absurd({False{} == True{} : Bool}, Lemma.lt_zero_false(q, lt))
    case 1n+(+m):
      ends_prod_pick(Nat.is_eq(m, q), q, m, {==}, set, grammar, x, k, j, lt, lhs, has,
        lt2 => ends_prod_of(m, set, grammar, x, k, j, q, lt2, lhs, has))

law ends_alt_pick:
  for b: Bool
  for +a: Nat
  for +m: Nat
  for +eb: {Nat.is_eq(m, a) == b : Bool}
  for +set: +List<Spec.Bsr>
  for +idx: Nat
  for +path: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +k: Nat
  for +j: Nat
  for +lt: {Nat.is_lt(a, 1n+m) == True{} : Bool}
  for +has: {Unb.hasStep(set, idx, List.append(&2, Nat, path, [a, List.length(&2, Spec.Item, Spec.altOf(alts, a))]), k, j) == True{} : Bool}
  for later: {Nat.is_lt(a, m) == True{} : Bool} -> {Unb.endsAlt(m, set, idx, path, alts, k, j) == True{} : Bool}
  {Unb.endsAlt(1n+m, set, idx, path, alts, k, j) == True{} : Bool}

def ends_alt_pick(b, a, m, eb, set, idx, path, alts, k, j, lt, has, later):
  match b:
    case True{}:
      +e = Lemma.nat_eq_sound(m, a, eb)
      +hit = Unb.hasStep(set, idx, List.append(&2, Nat, path, [m, List.length(&2, Spec.Item, Spec.altOf(alts, m))]), k, j)
      +hitM = Equal.trans(Bool, hit, Unb.hasStep(set, idx, List.append(&2, Nat, path, [a, List.length(&2, Spec.Item, Spec.altOf(alts, a))]), k, j), True{}, Equal.cong(Nat, Bool, v => Unb.hasStep(set, idx, List.append(&2, Nat, path, [v, List.length(&2, Spec.Item, Spec.altOf(alts, v))]), k, j), m, a, e), has)
      Lemma.or_true_left_intro(hit, Unb.endsAlt(m, set, idx, path, alts, k, j), hitM)
    case False{}:
      Lemma.or_true_right_intro(Unb.hasStep(set, idx, List.append(&2, Nat, path, [m, List.length(&2, Spec.Item, Spec.altOf(alts, m))]), k, j), Unb.endsAlt(m, set, idx, path, alts, k, j), later(Lemma.lt_succ_ne(a, m, lt, eb)))

law ends_alt_of:
  for n: Nat
  for +set: +List<Spec.Bsr>
  for +idx: Nat
  for +path: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +k: Nat
  for +j: Nat
  for +a: Nat
  for +lt: {Nat.is_lt(a, n) == True{} : Bool}
  for +has: {Unb.hasStep(set, idx, List.append(&2, Nat, path, [a, List.length(&2, Spec.Item, Spec.altOf(alts, a))]), k, j) == True{} : Bool}
  {Unb.endsAlt(n, set, idx, path, alts, k, j) == True{} : Bool}

def ends_alt_of(n, set, idx, path, alts, k, j, a, lt, has):
  match n:
    case 0n:
      Empty.absurd({False{} == True{} : Bool}, Lemma.lt_zero_false(a, lt))
    case 1n+(+m):
      ends_alt_pick(Nat.is_eq(m, a), a, m, {==}, set, idx, path, alts, k, j, lt, has,
        lt2 => ends_alt_of(m, set, idx, path, alts, k, j, a, lt2, has))

# ======== WHAT SUPPORT ASKS OF A STEP OF A WALK ========

law sup_decode:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Unb.supported(K, grammar, input, Spec.at(idx, prefix, 1n+d, i, k, j)) == Bool.and(Unb.beforeOk(d, rpath, K, grammar, idx, i, k), Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), d), K, grammar, input, idx, Gll.reverseOnto(rpath, [d]), k, j)) : Bool}

def sup_decode(K, grammar, input, idx, rpath, prefix, pEq, d, i, k, j):
  Equal.cong(+List<Nat>, Bool, v => Unb.supAt(v, K, grammar, input, idx, i, k, j), Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+d]), []), (1n+d) <> rpath, R.step_rev(rpath, prefix, 1n+d, pEq))

law sup_decode0:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +k: Nat
  {Unb.supported(K, grammar, input, Spec.at(idx, prefix, 0n, i, k, k)) == Bool.and(Nat.is_eq(k, k), Unb.startOk(rpath, K, grammar, idx, i, k)) : Bool}

def sup_decode0(K, grammar, input, idx, rpath, prefix, pEq, i, k):
  Equal.cong(+List<Nat>, Bool, v => Unb.supAt(v, K, grammar, input, idx, i, k, k), Gll.reverseOnto(List.append(&2, Nat, prefix, [0n]), []), 0n <> rpath, R.step_rev(rpath, prefix, 0n, pEq))

# A step of the walk that the pruned set supports is in it.
law sup_kept:
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +memJ: {Spec.bsrMember(Spec.at(idx, prefix, 1n+d, i, k, j), es) == True{} : Bool}
  for +before: {Unb.beforeOk(d, rpath, K, grammar, idx, i, k) == True{} : Bool}
  for +item: {Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), d), K, grammar, input, idx, Gll.reverseOnto(rpath, [d]), k, j) == True{} : Bool}
  {Spec.bsrMember(Spec.at(idx, prefix, 1n+d, i, k, j), K) == True{} : Bool}

def sup_kept(es, K, grammar, input, closed, idx, rpath, prefix, pEq, d, i, k, j, memJ, before, item):
  +y = Spec.at(idx, prefix, 1n+d, i, k, j)
  +both = Lemma.and_true_intro(Unb.beforeOk(d, rpath, K, grammar, idx, i, k), Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), d), K, grammar, input, idx, Gll.reverseOnto(rpath, [d]), k, j), before, item)
  +sup = Equal.trans(Bool, Unb.supported(K, grammar, input, y), Bool.and(Unb.beforeOk(d, rpath, K, grammar, idx, i, k), Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), d), K, grammar, input, idx, Gll.reverseOnto(rpath, [d]), k, j)), True{}, sup_decode(K, grammar, input, idx, rpath, prefix, pEq, d, i, k, j), both)
  closed_mem(es, K, grammar, input, closed, y, memJ, sup)

law sup_kept0:
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +k: Nat
  for +memJ: {Spec.bsrMember(Spec.at(idx, prefix, 0n, i, k, k), es) == True{} : Bool}
  for +start: {Unb.startOk(rpath, K, grammar, idx, i, k) == True{} : Bool}
  {Spec.bsrMember(Spec.at(idx, prefix, 0n, i, k, k), K) == True{} : Bool}

def sup_kept0(es, K, grammar, input, closed, idx, rpath, prefix, pEq, i, k, memJ, start):
  +y = Spec.at(idx, prefix, 0n, i, k, k)
  +both = Lemma.and_true_intro(Nat.is_eq(k, k), Unb.startOk(rpath, K, grammar, idx, i, k), Lemma.nat_eq_refl(k), start)
  +sup = Equal.trans(Bool, Unb.supported(K, grammar, input, y), Bool.and(Nat.is_eq(k, k), Unb.startOk(rpath, K, grammar, idx, i, k)), True{}, sup_decode0(K, grammar, input, idx, rpath, prefix, pEq, i, k), both)
  closed_mem(es, K, grammar, input, closed, y, memJ, sup)

# The step after item d, in the pruned set, lets item d + 1 start where it ends.
law before_next:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +m: {Spec.bsrMember(Spec.at(idx, prefix, 1n+d, i, k, e), K) == True{} : Bool}
  {Unb.beforeOk(1n+d, rpath, K, grammar, idx, i, e) == True{} : Bool}

def before_next(K, grammar, idx, rpath, prefix, pEq, d, i, k, e, m):
  +h = has_step_of(K, idx, List.append(&2, Nat, prefix, [1n+d]), i, k, e, m)
  Equal.trans(Bool, Unb.hasStep(K, idx, Gll.reverseOnto(rpath, [1n+d]), i, e), Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [1n+d]), i, e), True{}, Equal.cong(+List<Nat>, Bool, v => Unb.hasStep(K, idx, v, i, e), Gll.reverseOnto(rpath, [1n+d]), List.append(&2, Nat, prefix, [1n+d]), Equal.sym(+List<Nat>, List.append(&2, Nat, prefix, [1n+d]), Gll.reverseOnto(rpath, [1n+d]), G.prefix_ext(rpath, prefix, [1n+d], pEq))), h)

# ======== WHAT SUPPORT ASKS OF AN ITEM ========

law item_term:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +idx: Nat
  for +path: +List<Nat>
  for +k: Nat
  for +t: Nat
  for +kind: Nat
  for +r: +List<Nat>
  for +eqT: {Nat.is_eq(kind, t) == True{} : Bool}
  for +pos: {kind <> r == Lemma.dropN(k, input) : +List<Nat>}
  {Unb.itemOk(Some{Spec.Sym{Spec.Terminal{t}}}, K, grammar, input, idx, path, k, 1n+k) == True{} : Bool}

def item_term(K, grammar, input, idx, path, k, t, kind, r, eqT, pos):
  +hd = Equal.trans(Bool, Unb.headIs(Lemma.dropN(k, input), t), Unb.headIs(kind <> r, t), True{}, Equal.cong(+List<Nat>, Bool, v => Unb.headIs(v, t), Lemma.dropN(k, input), kind <> r, Equal.sym(+List<Nat>, kind <> r, Lemma.dropN(k, input), pos)), eqT)
  Lemma.and_true_intro(Nat.is_eq(1n+k, 1n+k), Unb.headIs(Lemma.dropN(k, input), t), Lemma.nat_eq_refl(1n+k), hd)

law lhs_lt:
  for +grammar: +List<Spec.Production>
  for p: Nat
  for +a: Nat
  for e: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  {Nat.is_lt(p, List.length(&2, Spec.Production, grammar)) == True{} : Bool}

def lhs_lt(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{lhs, rhs}, +rest} 0n:
      {==}
    case Con{Spec.Production{pl, pr}, +rest} 1n+q:
      lhs_lt(rest, q, a, e)

law seq_end_last:
  for +ch: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +idx: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +n: Nat
  for +nEq: {List.length(&2, Spec.Tree, ch) == n : Nat}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, idx, prefix, 0n, i, k), K) == True{} : Bool}
  for last: Sub.LastIn(ch, idx, prefix, 0n, i, k)
  {Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [n]), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def seq_end_last(ch, K, idx, prefix, i, k, n, nEq, allK, last):
  match last:
    case (piv0, m0):
      +piv = {piv0 : Nat}
      +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +nc = List.length(&2, Spec.Tree, ch)
      +mK = G.ebnf_all_in_member(Spec.walk(ch, False{}, idx, prefix, 0n, i, k), K, Spec.at(idx, prefix, Nat.add(0n, nc), i, piv, e), allK, m0)
      +h = has_step_of(K, idx, List.append(&2, Nat, prefix, [Nat.add(0n, nc)]), i, piv, e, mK)
      Equal.trans(Bool, Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [n]), i, e), Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [Nat.add(0n, nc)]), i, e), True{}, Equal.cong(Nat, Bool, v => Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [v]), i, e), n, Nat.add(0n, nc), Equal.sym(Nat, Nat.add(0n, nc), n, nEq)), h)

# The end of a sequence walked from k, in the pruned set.
law seq_end_kept:
  for +ch: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +idx: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +n: Nat
  for +nEq: {List.length(&2, Spec.Tree, ch) == n : Nat}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, idx, prefix, 0n, i, k), K) == True{} : Bool}
  {Unb.hasStep(K, idx, List.append(&2, Nat, prefix, [n]), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def seq_end_kept(ch, K, idx, prefix, i, k, n, nEq, allK):
  seq_end_last(ch, K, idx, prefix, i, k, n, nEq, allK, Sub.last_any(ch, idx, prefix, i, k))

law item_nt:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +idx: Nat
  for +path: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhs: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), K) == True{} : Bool}
  {Unb.itemOk(Some{Spec.Sym{Spec.Nonterminal{x}}}, K, grammar, input, idx, path, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def item_nt(K, grammar, input, idx, path, x, q, ch, k, lhs, fitCh, allK):
  +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
  +h = seq_end_kept(ch, K, q, [], k, k, n, Fits.fits_count(ch, grammar, Spec.rhsOf(grammar, q), fitCh), allK)
  ends_prod_of(List.length(&2, Spec.Production, grammar), K, grammar, x, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), q, lhs_lt(grammar, q, x, lhs), lhs, h)

# A pick of alternative a of the bracket at path, walked from k.
law pick_ends:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +path: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, idx, List.append(&2, Nat, path, [a]), 0n, i, k), K) == True{} : Bool}
  {Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def pick_ends(K, grammar, idx, path, alts, a, ch, i, k, isA, fitCh, allK):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
  +h = seq_end_kept(ch, K, idx, List.append(&2, Nat, path, [a]), i, k, n, Fits.fits_count(ch, grammar, Spec.altOf(alts, a), fitCh), allK)
  +h2 = Equal.trans(Bool, Unb.hasStep(K, idx, List.append(&2, Nat, path, [a, n]), i, e), Unb.hasStep(K, idx, List.append(&2, Nat, List.append(&2, Nat, path, [a]), [n]), i, e), True{}, Equal.cong(+List<Nat>, Bool, v => Unb.hasStep(K, idx, v, i, e), List.append(&2, Nat, path, [a, n]), List.append(&2, Nat, List.append(&2, Nat, path, [a]), [n]), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, path, [a]), [n]), List.append(&2, Nat, path, [a, n]), G.nat_append_assoc(path, [a], [n]))), h)
  ends_alt_of(List.length(&2, +List<Spec.Item>, alts), K, idx, path, alts, i, e, a, isA, h2)

# ======== LOOPS ========

law len_leaves_cons:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +k: Nat
  {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), List.length(&2, Nat, Spec.leaves(ts))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))) : Nat}

def len_leaves_cons(t, ts, k):
  +a = List.length(&2, Nat, Spec.leaves([t]))
  +b = List.length(&2, Nat, Spec.leaves(ts))
  Equal.trans(Nat, Nat.add(Nat.add(k, a), b), Nat.add(k, Nat.add(a, b)), Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))), Lemma.add_assoc(k, a, b),
    Equal.cong(Nat, Nat, v => Nat.add(k, v), Nat.add(a, b), List.length(&2, Nat, Spec.leaves(t <> ts)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), Nat.add(a, b),
      Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), List.length(&2, Nat, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts))), Nat.add(a, b), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Sub.leaves_cons(t, ts)), Lemma.length_append(Spec.leaves([t]), Spec.leaves(ts))))))

law leaves_one_pick:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  {List.length(&2, Nat, Spec.leaves(ch)) == List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}])) : Nat}

def leaves_one_pick(a, ch):
  Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))

# After the first round: the last round is this one, or one of the rest.
law rounds_ends_tail:
  for ts: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +path: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +k: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +fitTs: {Spec.fits(ts, grammar, Spec.times(List.length(&2, Spec.Tree, ts), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +allTs: {Spec.allIn(Spec.walk(ts, True{}, idx, path, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), K) == True{} : Bool}
  for +here: {Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for later: {Spec.fits(ts, grammar, Spec.times(List.length(&2, Spec.Tree, ts), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} -> {List.is_empty(&2, Spec.Tree, ts) == False{} : Bool} -> {Spec.allIn(Spec.walk(ts, True{}, idx, path, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), K) == True{} : Bool} -> {Unb.bracketEnds(K, idx, path, alts, i, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(ts)))) == True{} : Bool}
  {Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts)))) == True{} : Bool}

def rounds_ends_tail(ts, K, grammar, idx, path, alts, i, k, a, ch, fitTs, allTs, here, later):
  match ts:
    case Nil{}:
      +lch = List.length(&2, Nat, Spec.leaves(ch))
      +lone = leaves_one_pick(a, ch)
      Equal.trans(Bool, Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}])))), Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, lch)), True{}, Equal.cong(Nat, Bool, v => Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, v)), List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}])), lch, Equal.sym(Nat, lch, List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}])), lone)), here)
    case Con{+t2, +ts2}:
      +lch = List.length(&2, Nat, Spec.leaves(ch))
      +rs = {t2 <> ts2 : +List<Spec.Tree>}
      +lone = leaves_one_pick(a, ch)
      +p = {Spec.Pick{a, ch} : Spec.Tree}
      +lenEq = Equal.trans(Nat, Nat.add(Nat.add(k, lch), List.length(&2, Nat, Spec.leaves(rs))), Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves([p]))), List.length(&2, Nat, Spec.leaves(rs))), Nat.add(k, List.length(&2, Nat, Spec.leaves(p <> rs))),
        Equal.cong(Nat, Nat, v => Nat.add(Nat.add(k, v), List.length(&2, Nat, Spec.leaves(rs))), lch, List.length(&2, Nat, Spec.leaves([p])), lone), len_leaves_cons(p, rs, k))
      +there = later(fitTs, {==}, allTs)
      Equal.trans(Bool, Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(p <> rs)))), Unb.bracketEnds(K, idx, path, alts, i, Nat.add(Nat.add(k, lch), List.length(&2, Nat, Spec.leaves(rs)))), True{}, Equal.cong(Nat, Bool, v => Unb.bracketEnds(K, idx, path, alts, i, v), Nat.add(k, List.length(&2, Nat, Spec.leaves(p <> rs))), Nat.add(Nat.add(k, lch), List.length(&2, Nat, Spec.leaves(rs))), Equal.sym(Nat, Nat.add(Nat.add(k, lch), List.length(&2, Nat, Spec.leaves(rs))), Nat.add(k, List.length(&2, Nat, Spec.leaves(p <> rs))), lenEq)), there)

# Rounds of a loop, all in the pruned set, end with a round of the loop.
law rounds_ends:
  for rs: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +path: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +k: Nat
  for +fit: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +ne: {List.is_empty(&2, Spec.Tree, rs) == False{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(rs, True{}, idx, path, 0n, i, k), K) == True{} : Bool}
  {Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))) == True{} : Bool}

def rounds_ends(rs, K, grammar, idx, path, alts, i, k, fit, ne, allK):
  match rs:
    case Nil{}:
      Empty.absurd({Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, 0n)) == True{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Pick{+a, +ch}, +ts}:
      +item = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +rest = Spec.times(List.length(&2, Spec.Tree, ts), item)
      +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, item, rest, fit)
      +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
      +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, item, rest, fit)
      +lch = List.length(&2, Nat, Spec.leaves(ch))
      +end = Nat.add(k, lch)
      +wCh = Spec.walk(ch, False{}, idx, List.append(&2, Nat, path, [a]), 0n, i, k)
      +wTs = Spec.walk(ts, True{}, idx, path, 0n, i, end)
      +allCh = R.in_app_left(wCh, wTs, K, allK)
      +allTs = R.in_app_right(wCh, wTs, K, allK)
      +lone = leaves_one_pick(a, ch)
      rounds_ends_tail(ts, K, grammar, idx, path, alts, i, k, a, ch, fitTs, allTs, pick_ends(K, grammar, idx, path, alts, a, ch, i, k, isA, fitCh, allCh),
        f => ne2 => al => rounds_ends(ts, K, grammar, idx, path, alts, i, end, f, ne2, al))
    case Con{Spec.Leaf{t}, +ts}:
      Empty.absurd({Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{t} <> ts)))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, ch}, +ts}:
      Empty.absurd({Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts)))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, +ts}:
      Empty.absurd({Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts)))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{r}, +ts}:
      Empty.absurd({Unb.bracketEnds(K, idx, path, alts, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{r} <> ts)))) == True{} : Bool}, Lemma.false_is_not_true(fit))

# ======== THE WALK: EVERY FOREST OF JUDGED STEPS IS IN THE PRUNED SET ========

def SwReady(rounds: Bool, +grammar: +List<Spec.Production>, +input: +List<Nat>, +es: +List<Spec.Bsr>, +K: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), es) == True{} : Bool} & {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), es) == True{} : Bool} & {Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, index, prefix, alts, i, k)) == True{} : Bool}

def SwDone(rounds: Bool, +K: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Data:
  {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, i, k), K) == True{} : Bool}

def SwIH(+grammar: +List<Spec.Production>, +input: +List<Nat>, +es: +List<Spec.Bsr>, +K: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @after: +List<Nat> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> SwReady(rounds, grammar, input, es, K, forest, index, rpath, prefix, dot, i, k, items, kind, alts) -> SwDone(rounds, K, forest, index, prefix, dot, i, k)

# A sequence's first item: it starts the sequence.
law start_here:
  for +rp: +List<Nat>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +k: Nat
  {Unb.beforeOk(0n, rp, K, grammar, idx, k, k) == True{} : Bool}

def start_here(rp, K, grammar, idx, k):
  Lemma.or_true_left_intro(Nat.is_eq(k, k), Unb.roundBefore(rp, K, grammar, idx, k, k), Lemma.nat_eq_refl(k))

# The item at the dot, as support reads it.
law item_at:
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +idx: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +item: Spec.Item
  for +k: Nat
  for +j: Nat
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, idx, rpath), dot) == Some{item} : Maybe<&2, Spec.Item>}
  for +ok: {Unb.itemOk(Some{item}, K, grammar, input, idx, Gll.reverseOnto(rpath, [dot]), k, j) == True{} : Bool}
  {Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), dot), K, grammar, input, idx, Gll.reverseOnto(rpath, [dot]), k, j) == True{} : Bool}

def item_at(K, grammar, input, idx, rpath, dot, item, k, j, itemEq, ok):
  Equal.trans(Bool, Unb.itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rpath), dot), K, grammar, input, idx, Gll.reverseOnto(rpath, [dot]), k, j), Unb.itemOk(Some{item}, K, grammar, input, idx, Gll.reverseOnto(rpath, [dot]), k, j), True{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Unb.itemOk(v, K, grammar, input, idx, Gll.reverseOnto(rpath, [dot]), k, j), Gll.nthItem(Gll.seqAt(grammar, idx, rpath), dot), Some{item}, itemEq), ok)

# A bracket's end, read along the reversed path.
law ends_path:
  for +K: +List<Spec.Bsr>
  for +idx: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +j: Nat
  for +h: {Unb.bracketEnds(K, idx, List.append(&2, Nat, prefix, [dot]), alts, i, j) == True{} : Bool}
  {Unb.bracketEnds(K, idx, Gll.reverseOnto(rpath, [dot]), alts, i, j) == True{} : Bool}

def ends_path(K, idx, rpath, prefix, pEq, dot, alts, i, j, h):
  Equal.trans(Bool, Unb.bracketEnds(K, idx, Gll.reverseOnto(rpath, [dot]), alts, i, j), Unb.bracketEnds(K, idx, List.append(&2, Nat, prefix, [dot]), alts, i, j), True{}, Equal.cong(+List<Nat>, Bool, v => Unb.bracketEnds(K, idx, v, alts, i, j), Gll.reverseOnto(rpath, [dot]), List.append(&2, Nat, prefix, [dot]), Equal.sym(+List<Nat>, List.append(&2, Nat, prefix, [dot]), Gll.reverseOnto(rpath, [dot]), G.prefix_ext(rpath, prefix, [dot], pEq))), h)

# A step, its children and the rest.
law sw_join:
  for +x: Spec.Bsr
  for +wCh: +List<Spec.Bsr>
  for +wTs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +mx: {Spec.bsrMember(x, set) == True{} : Bool}
  for +hc: {Spec.allIn(wCh, set) == True{} : Bool}
  for +ht: {Spec.allIn(wTs, set) == True{} : Bool}
  {Spec.allIn(x <> List.append(&2, Spec.Bsr, wCh, wTs), set) == True{} : Bool}

def sw_join(x, wCh, wTs, set, mx, hc, ht):
  Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wTs), set), mx, G.all_in_app(wCh, wTs, set, hc, ht))

# A round of a loop starts at the loop's start, or where an earlier round ended.
law loop_before_ends:
  for kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +K: +List<Spec.Bsr>
  for +idx: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  {Unb.loopBefore(Some{Spec.Brack{kind, alts}}, K, idx, path, i, k) == Unb.bracketEnds(K, idx, path, alts, i, k) : Bool}

def loop_before_ends(kind, alts, K, idx, path, i, k, isL):
  match kind:
    case Spec.Group{}:
      Empty.absurd({False{} == Unb.bracketEnds(K, idx, path, alts, i, k) : Bool}, Lemma.false_is_not_true(isL))
    case Spec.Optional{}:
      Empty.absurd({False{} == Unb.bracketEnds(K, idx, path, alts, i, k) : Bool}, Lemma.false_is_not_true(isL))
    case Spec.Closure{}:
      {==}
    case Spec.Positive{}:
      {==}

law round_start:
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +idx: Nat
  for +prefix: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +k: Nat
  for +loopIt: {G.loopItem(grammar, idx, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +b0: {Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, idx, prefix, alts, i, k)) == True{} : Bool}
  {Unb.beforeOk(0n, a <> m <> outer, K, grammar, idx, i, k) == True{} : Bool}

def round_start(a, m, outer, K, grammar, idx, prefix, kind, alts, i, k, loopIt, isL, pEq, b0):
  +P = Gll.reverseOnto(m <> outer, [])
  +e1 = Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Bool.or(Nat.is_eq(k, i), Unb.loopBefore(v, K, idx, P, i, k)), G.loopItem(grammar, idx, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
  +e2 = Equal.cong(Bool, Bool, v => Bool.or(Nat.is_eq(k, i), v), Unb.loopBefore(Some{Spec.Brack{kind, alts}}, K, idx, P, i, k), Unb.bracketEnds(K, idx, P, alts, i, k), loop_before_ends(kind, alts, K, idx, P, i, k, isL))
  +e3 = Equal.cong(+List<Nat>, Bool, v => Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, idx, v, alts, i, k)), P, prefix, Equal.sym(+List<Nat>, prefix, P, pEq))
  Equal.trans(Bool, Bool.or(Nat.is_eq(k, i), Unb.loopBefore(G.loopItem(grammar, idx, m <> outer), K, idx, P, i, k)), Bool.or(Nat.is_eq(k, i), Unb.loopBefore(Some{Spec.Brack{kind, alts}}, K, idx, P, i, k)), True{}, e1,
    Equal.trans(Bool, Bool.or(Nat.is_eq(k, i), Unb.loopBefore(Some{Spec.Brack{kind, alts}}, K, idx, P, i, k)), Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, idx, P, alts, i, k)), True{}, e2,
      Equal.trans(Bool, Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, idx, P, alts, i, k)), Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, idx, prefix, alts, i, k)), True{}, e3, b0)))

# A loop with no rounds reads nothing.
law empty_loop:
  for +k: Nat
  {Nat.is_eq(k, Nat.add(k, List.length(&2, Nat, Spec.leaves([])))) == True{} : Bool}

def empty_loop(k):
  Equal.trans(Bool, Nat.is_eq(k, Nat.add(k, 0n)), Nat.is_eq(k, k), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(k, v), Nat.add(k, 0n), k, Lemma.add_zero_right(k)), Lemma.nat_eq_refl(k))

law sw_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(False{}, grammar, input, es, K, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SwIH(grammar, input, es, K, ch)
  for ihTs: SwIH(grammar, input, es, K, ts)
  SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k)

def sw_node(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), es), allW)
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), es, allW)
          +allCh = R.in_app_left(wCh, wTs, es, allIn2)
          +allTs = R.in_app_right(wCh, wTs, es, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
          +kCh = ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, next, {==}, posCh, ({==}, (fitCh, (allCh, start_here([], K, grammar, q, k)))))
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Sym{Spec.Nonterminal{x}}, k, end, itemEq, item_nt(K, grammar, input, index, Gll.reverseOnto(rpath, [dot]), x, q, ch, k, lhsQ, fitCh, kCh))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, end, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, end, memK)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, befTs))))
          sw_join(hx, wCh, wTs, K, memK, kCh, kTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sw_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(False{}, grammar, input, es, K, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SwIH(grammar, input, es, K, ch)
  for ihTs: SwIH(grammar, input, es, K, ts)
  SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)

def sw_pick(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), es), allW)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +isA = Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), es, allW)
          +allCh = R.in_app_left(wCh, wTs, es, allIn2)
          +allTs = R.in_app_right(wCh, wTs, es, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, es), Spec.allIn(wCh, es), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), es), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
          +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, (allCh2, start_here(a <> dot <> rpath, K, grammar, index, k)))))
          +kCh = Equal.trans(Bool, Spec.allIn(wCh, K), Spec.allIn(wCh2, K), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), K), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Brack{Spec.Group{}, balts}, k, end, itemEq, ends_path(K, index, rpath, prefix, pEq, dot, balts, k, end, pick_ends(K, grammar, index, List.append(&2, Nat, prefix, [dot]), balts, a, ch, k, k, isA, fitCh, kCh2)))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, end, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, end, memK)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, befTs))))
          sw_join(hx, wCh, wTs, K, memK, kCh, kTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), es), allW)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +isA = Lemma.and_true_right_side(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh))
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), es, allW)
          +allCh = R.in_app_left(wCh, wTs, es, allIn2)
          +allTs = R.in_app_right(wCh, wTs, es, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, es), Spec.allIn(wCh, es), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), es), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
          +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, (allCh2, start_here(a <> dot <> rpath, K, grammar, index, k)))))
          +kCh = Equal.trans(Bool, Spec.allIn(wCh, K), Spec.allIn(wCh2, K), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), K), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Brack{Spec.Optional{}, balts}, k, end, itemEq, Lemma.or_true_right_intro(Nat.is_eq(k, end), Unb.bracketEnds(K, index, Gll.reverseOnto(rpath, [dot]), balts, k, end), ends_path(K, index, rpath, prefix, pEq, dot, balts, k, end, pick_ends(K, grammar, index, List.append(&2, Nat, prefix, [dot]), balts, a, ch, k, k, isA, fitCh, kCh2))))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, end, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, end, memK)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, befTs))))
          sw_join(hx, wCh, wTs, K, memK, kCh, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sw_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(False{}, grammar, input, es, K, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: SwIH(grammar, input, es, K, ts)
  SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k)

def sw_leaf(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, 1n+k)
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), es), allW)
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +eqT = Lemma.and_true_left(Nat.is_eq(k0, t0), Spec.fits(ts, grammar, rest), fit)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Sym{Spec.Terminal{t0}}, k, 1n+k, itemEq, item_term(K, grammar, input, index, Gll.reverseOnto(rpath, [dot]), k, t0, k0, List.append(&2, Nat, Spec.leaves(ts), after), eqT, pos))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, 1n+k, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, 1n+k, memK)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), es, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, after, pEq, PG.pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, befTs))))
          Lemma.and_true_intro(Spec.bsrMember(hx, K), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), K), memK, kTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sw_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Skip{} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(False{}, grammar, input, es, K, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: SwIH(grammar, input, es, K, ts)
  SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k)

def sw_skip(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), es), allW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Brack{Spec.Optional{}, balts}, k, k, itemEq, Lemma.or_true_left_intro(Nat.is_eq(k, k), Unb.bracketEnds(K, index, Gll.reverseOnto(rpath, [dot]), balts, k, k), Lemma.nat_eq_refl(k)))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, k, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, k, memK)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), es, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, befTs))))
          Lemma.and_true_intro(Spec.bsrMember(hx, K), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), K), memK, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), es), allW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Eps{}, k, k, itemEq, Lemma.nat_eq_refl(k))
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, k, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, k, memK)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), es, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, befTs))))
          Lemma.and_true_intro(Spec.bsrMember(hx, K), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), K), memK, kTs)

law loop_closure_ok:
  for rs: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +balts: +List<+List<Spec.Item>>
  for +k: Nat
  for +rok: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +kRs: {Spec.allIn(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), K) == True{} : Bool}
  {Unb.itemOk(Some{Spec.Brack{Spec.Closure{}, balts}}, K, grammar, input, index, Gll.reverseOnto(rpath, [dot]), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))) == True{} : Bool}

def loop_closure_ok(rs, K, grammar, input, index, rpath, prefix, pEq, dot, balts, k, rok, fitRs, kRs):
  match rs:
    case Nil{}:
      Lemma.or_true_left_intro(Nat.is_eq(k, Nat.add(k, 0n)), Unb.bracketEnds(K, index, Gll.reverseOnto(rpath, [dot]), balts, k, Nat.add(k, 0n)), empty_loop(k))
    case Con{+r, +rr}:
      Lemma.or_true_right_intro(Nat.is_eq(k, Nat.add(k, List.length(&2, Nat, Spec.leaves(r <> rr)))), Unb.bracketEnds(K, index, Gll.reverseOnto(rpath, [dot]), balts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(r <> rr)))), ends_path(K, index, rpath, prefix, pEq, dot, balts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(r <> rr))), rounds_ends(r <> rr, K, grammar, index, List.append(&2, Nat, prefix, [dot]), balts, k, k, fitRs, {==}, kRs)))

law loop_positive_ok:
  for rs: +List<Spec.Tree>
  for +K: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +balts: +List<+List<Spec.Item>>
  for +k: Nat
  for +rok: {Spec.roundsOk(Spec.Positive{}, rs) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +kRs: {Spec.allIn(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), K) == True{} : Bool}
  {Unb.itemOk(Some{Spec.Brack{Spec.Positive{}, balts}}, K, grammar, input, index, Gll.reverseOnto(rpath, [dot]), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))) == True{} : Bool}

def loop_positive_ok(rs, K, grammar, input, index, rpath, prefix, pEq, dot, balts, k, rok, fitRs, kRs):
  match rs:
    case Nil{}:
      Empty.absurd({Unb.itemOk(Some{Spec.Brack{Spec.Positive{}, balts}}, K, grammar, input, index, Gll.reverseOnto(rpath, [dot]), k, Nat.add(k, List.length(&2, Nat, Spec.leaves([])))) == True{} : Bool}, Lemma.false_is_not_true(rok))
    case Con{+r, +rr}:
      ends_path(K, index, rpath, prefix, pEq, dot, balts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(r <> rr))), rounds_ends(r <> rr, K, grammar, index, List.append(&2, Nat, prefix, [dot]), balts, k, k, fitRs, {==}, kRs))

law sw_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(False{}, grammar, input, es, K, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihRs: SwIH(grammar, input, es, K, rs)
  for ihTs: SwIH(grammar, input, es, K, ts)
  SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k)

def sw_loop(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))), es), allW)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +roundsOk = Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), es, allW)
          +allRs = R.in_app_left(wRs, wTs, es, allIn2)
          +allTs = R.in_app_right(wRs, wTs, es, allIn2)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, (allRs, Lemma.or_true_left_intro(Nat.is_eq(k, k), Unb.bracketEnds(K, index, path, balts, k, k), Lemma.nat_eq_refl(k)))))))
          +lok = loop_closure_ok(rs, K, grammar, input, index, rpath, prefix, pEq, dot, balts, k, roundsOk, fitRs, kRs)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Brack{Spec.Closure{}, balts}, k, end, itemEq, lok)
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, end, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, end, memK)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, befTs))))
          sw_join(hx, wRs, wTs, K, memK, kRs, kTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +before = {bef0 : {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}}
          +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
          +memJ = Lemma.and_true_left(Spec.bsrMember(hx, es), Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))), es), allW)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +roundsOk = Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), es, allW)
          +allRs = R.in_app_left(wRs, wTs, es, allIn2)
          +allTs = R.in_app_right(wRs, wTs, es, allIn2)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, (allRs, Lemma.or_true_left_intro(Nat.is_eq(k, k), Unb.bracketEnds(K, index, path, balts, k, k), Lemma.nat_eq_refl(k)))))))
          +lok = loop_positive_ok(rs, K, grammar, input, index, rpath, prefix, pEq, dot, balts, k, roundsOk, fitRs, kRs)
          +ok = item_at(K, grammar, input, index, rpath, dot, Spec.Brack{Spec.Positive{}, balts}, k, end, itemEq, lok)
          +memK = sup_kept(es, K, grammar, input, closed, index, rpath, prefix, pEq, dot, i, k, end, memJ, before, ok)
          +befTs = before_next(K, grammar, index, rpath, prefix, pEq, dot, i, k, end, memK)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, befTs))))
          sw_join(hx, wRs, wTs, K, memK, kRs, kTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(SwDone(False{}, K, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sw_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(True{}, grammar, input, es, K, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SwIH(grammar, input, es, K, ch)
  for ihRest: SwIH(grammar, input, es, K, rest)
  SwDone(True{}, K, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k)

def sw_round(rpath, grammar, input, es, K, closed, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(SwDone(True{}, K, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, (all0, bef0)))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), es) == True{} : Bool}}
          +bef = {bef0 : {Bool.or(Nat.is_eq(k, i), Unb.bracketEnds(K, index, prefix, alts, i, k)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lr, after)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +allCh = R.in_app_left(wCh, wRest, es, allW)
          +allRest = R.in_app_right(wCh, wRest, es, allW)
          +posCh = PG.pos_children(w, lr, after, input, k, pos)
          +posRest = PG.pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +befCh = round_start(a, m, outer, K, grammar, index, prefix, kind, alts, i, k, loopIt, isL, pEq, bef)
          +kCh = ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, next, pEqA, posCh, (itemsEqR, (fitCh, (allCh, befCh))))
          +befRest = Lemma.or_true_right_intro(Nat.is_eq(end, i), Unb.bracketEnds(K, index, prefix, alts, i, end), pick_ends(K, grammar, index, prefix, alts, a, ch, i, k, isA, fitCh, kCh))
          +kRest = ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, after, pEq, posRest, (loopIt, (isL, (fitRest, (allRest, befRest)))))
          G.all_in_app(wCh, wRest, K, kCh, kRest)

law sw_nil:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +allJ: {Spec.allIn(Spec.walk([], False{}, index, prefix, dot, i, k), es) == True{} : Bool}
  for +before: {Unb.beforeOk(dot, rpath, K, grammar, index, i, k) == True{} : Bool}
  SwDone(False{}, K, [], index, prefix, dot, i, k)

def sw_nil(dot, grammar, input, es, K, closed, index, rpath, prefix, i, k, pEq, allJ, before):
  match dot:
    case 0n:
      +y = Spec.at(index, prefix, 0n, i, k, k)
      Lemma.and_true_intro(Spec.bsrMember(y, K), True{}, sup_kept0(es, K, grammar, input, closed, index, rpath, prefix, pEq, i, k, Lemma.and_true_left(Spec.bsrMember(y, es), True{}, allJ), before), {==})
    case 1n+d:
      {==}

law sw_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +es: +List<Spec.Bsr>
  for +K: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(es, K, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SwReady(rounds, grammar, input, es, K, forest, index, rpath, prefix, dot, i, k, items, kind, alts)
  SwDone(rounds, K, forest, index, prefix, dot, i, k)

def sw_walk(forest, rounds, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, items, kind, alts, after, pEq, pos, ready):
  match forest rounds:
    case Nil{} False{}:
      match ready:
        case (rem0, (fit0, (all0, bef0))):
          sw_nil(dot, grammar, input, es, K, closed, index, rpath, prefix, i, k, pEq, all0, bef0)
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      sw_leaf(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ts, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      sw_node(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ch, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ts, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      sw_pick(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ch, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ts, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      sw_skip(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ts, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      sw_loop(items, grammar, input, es, K, closed, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(rs, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ts, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      sw_round(rpath, grammar, input, es, K, closed, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(ch, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => sw_walk(rest, ri, grammar, input, es, K, closed, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(SwDone(True{}, K, Spec.Leaf{k0} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(SwDone(True{}, K, Spec.Node{q, ch} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(SwDone(True{}, K, Spec.Skip{} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(SwDone(True{}, K, Spec.Loop{rs} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

# ======== THE SUB-PARSE, PUT BACK IN PLACE ========
#
# UNBEATEN.bend moves the sub-parse's steps to where they stand in the input: shifted by
# the choice's start i, and with the extra production's slots read as the rival's. A
# forest of the original grammar has no node of the extra production, so its nodes keep
# their slots; only the steps of the extra production's own sequence move.

# Every node of the forest is of a production below n.
def nodesBelow(+n: Nat, forest: +List<Spec.Tree>) -> Bool:
  match forest:
    case Nil{}:
      True{}
    case Con{Spec.Leaf{k}, ts}:
      nodesBelow(n, ts)
    case Con{Spec.Node{q, ch}, ts}:
      Bool.and(Nat.is_lt(q, n), Bool.and(nodesBelow(n, ch), nodesBelow(n, ts)))
    case Con{Spec.Pick{a, ch}, ts}:
      Bool.and(nodesBelow(n, ch), nodesBelow(n, ts))
    case Con{Spec.Skip{}, ts}:
      nodesBelow(n, ts)
    case Con{Spec.Loop{rs}, ts}:
      Bool.and(nodesBelow(n, rs), nodesBelow(n, ts))

law lt_neq:
  for a: Nat
  for b: Nat
  for lt: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_eq(a, b) == False{} : Bool}

def lt_neq(a, b, lt):
  match a b:
    case 0n 0n:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(lt))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({False{} == False{} : Bool}, Lemma.false_is_not_true(lt))
    case 1n+p 1n+q:
      lt_neq(p, q, lt)

# Where a slot of the sub-parse goes: the extra production's to the rival's sequence.
def tgtIdx(fr: Bool, +idx: Nat, +x: Nat) -> Nat:
  match fr:
    case True{}:
      idx
    case False{}:
      x

def tgtPre(fr: Bool, +pre: +List<Nat>, +p: +List<Nat>) -> +List<Nat>:
  match fr:
    case True{}:
      List.append(&2, Nat, pre, p)
    case False{}:
      p

law tgt_app:
  for +fr: Bool
  for +pre: +List<Nat>
  for +p: +List<Nat>
  for +ext: +List<Nat>
  {tgtPre(fr, pre, List.append(&2, Nat, p, ext)) == List.append(&2, Nat, tgtPre(fr, pre, p), ext) : +List<Nat>}

def tgt_app(fr, pre, p, ext):
  match fr:
    case True{}:
      Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, pre, p), ext), List.append(&2, Nat, pre, List.append(&2, Nat, p, ext)), G.nat_append_assoc(pre, p, ext))
    case False{}:
      {==}

law place_slot_b:
  for b: Bool
  for +idx: Nat
  for +pre: +List<Nat>
  for +x: Nat
  for +p: +List<Nat>
  {Unb.placeSlot(b, idx, pre, x, p) == Spec.Slot{tgtIdx(b, idx, x), tgtPre(b, pre, p)} : Spec.Slot}

def place_slot_b(b, idx, pre, x, p):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law place_slot:
  for +fr: Bool
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +x: Nat
  for +p: +List<Nat>
  for +eqFr: {Nat.is_eq(x, lg) == fr : Bool}
  {Unb.placeSlot(Nat.is_eq(x, lg), idx, pre, x, p) == Spec.Slot{tgtIdx(fr, idx, x), tgtPre(fr, pre, p)} : Spec.Slot}

def place_slot(fr, lg, idx, pre, x, p, eqFr):
  %eqFr : {Unb.placeSlot(Nat.is_eq(x, lg), idx, pre, x, p) == Spec.Slot{tgtIdx(_, idx, x), tgtPre(_, pre, p)} : Spec.Slot}
  place_slot_b(Nat.is_eq(x, lg), idx, pre, x, p)

# One step of the walk, placed.
law place_at:
  for +fr: Bool
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +x: Nat
  for +p: +List<Nat>
  for +d: Nat
  for +a: Nat
  for +k: Nat
  for +j: Nat
  for +eqFr: {Nat.is_eq(x, lg) == fr : Bool}
  {Unb.place(lg, idx, pre, i, Spec.at(x, p, d, a, k, j)) == Spec.at(tgtIdx(fr, idx, x), tgtPre(fr, pre, p), d, Nat.add(i, a), Nat.add(i, k), Nat.add(i, j)) : Spec.Bsr}

def place_at(fr, lg, idx, pre, i, x, p, d, a, k, j, eqFr):
  +s1 = place_slot(fr, lg, idx, pre, x, List.append(&2, Nat, p, [d]), eqFr)
  +s2 = Equal.cong(+List<Nat>, Spec.Slot, v => Spec.Slot{tgtIdx(fr, idx, x), v}, tgtPre(fr, pre, List.append(&2, Nat, p, [d])), List.append(&2, Nat, tgtPre(fr, pre, p), [d]), tgt_app(fr, pre, p, [d]))
  +sl = Equal.trans(Spec.Slot, Unb.placeSlot(Nat.is_eq(x, lg), idx, pre, x, List.append(&2, Nat, p, [d])), Spec.Slot{tgtIdx(fr, idx, x), tgtPre(fr, pre, List.append(&2, Nat, p, [d]))}, Spec.Slot{tgtIdx(fr, idx, x), List.append(&2, Nat, tgtPre(fr, pre, p), [d])}, s1, s2)
  Equal.cong(Spec.Slot, Spec.Bsr, v => Spec.Bsr{v, Nat.add(i, a), Nat.add(i, k), Nat.add(i, j)}, Unb.placeSlot(Nat.is_eq(x, lg), idx, pre, x, List.append(&2, Nat, p, [d])), Spec.Slot{tgtIdx(fr, idx, x), List.append(&2, Nat, tgtPre(fr, pre, p), [d])}, sl)

law place_app:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  {Unb.placeAll(List.append(&2, Spec.Bsr, xs, ys), lg, idx, pre, i) == List.append(&2, Spec.Bsr, Unb.placeAll(xs, lg, idx, pre, i), Unb.placeAll(ys, lg, idx, pre, i)) : +List<Spec.Bsr>}

def place_app(xs, ys, lg, idx, pre, i):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(+List<Spec.Bsr>, +List<Spec.Bsr>, v => Unb.place(lg, idx, pre, i, x) <> v, Unb.placeAll(List.append(&2, Spec.Bsr, rest, ys), lg, idx, pre, i), List.append(&2, Spec.Bsr, Unb.placeAll(rest, lg, idx, pre, i), Unb.placeAll(ys, lg, idx, pre, i)), place_app(rest, ys, lg, idx, pre, i))

law cons_eq:
  for +x: Spec.Bsr
  for +y: Spec.Bsr
  for +xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +e1: {x == y : Spec.Bsr}
  for +e2: {xs == ys : +List<Spec.Bsr>}
  {x <> xs == y <> ys : +List<Spec.Bsr>}

def cons_eq(x, y, xs, ys, e1, e2):
  Equal.trans(+List<Spec.Bsr>, x <> xs, y <> xs, y <> ys, Equal.cong(Spec.Bsr, +List<Spec.Bsr>, v => v <> xs, x, y, e1), Equal.cong(+List<Spec.Bsr>, +List<Spec.Bsr>, v => y <> v, xs, ys, e2))

law app_eq:
  for +xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +us: +List<Spec.Bsr>
  for +vs: +List<Spec.Bsr>
  for +e1: {xs == ys : +List<Spec.Bsr>}
  for +e2: {us == vs : +List<Spec.Bsr>}
  {List.append(&2, Spec.Bsr, xs, us) == List.append(&2, Spec.Bsr, ys, vs) : +List<Spec.Bsr>}

def app_eq(xs, ys, us, vs, e1, e2):
  Equal.trans(+List<Spec.Bsr>, List.append(&2, Spec.Bsr, xs, us), List.append(&2, Spec.Bsr, ys, us), List.append(&2, Spec.Bsr, ys, vs), Equal.cong(+List<Spec.Bsr>, +List<Spec.Bsr>, v => List.append(&2, Spec.Bsr, v, us), xs, ys, e1), Equal.cong(+List<Spec.Bsr>, +List<Spec.Bsr>, v => List.append(&2, Spec.Bsr, ys, v), us, vs, e2))

# A walk at an end k + L, placed: the shift goes inside.
law shift_add:
  for +i: Nat
  for +k: Nat
  for +l: Nat
  {Nat.add(i, Nat.add(k, l)) == Nat.add(Nat.add(i, k), l) : Nat}

def shift_add(i, k, l):
  Equal.sym(Nat, Nat.add(Nat.add(i, k), l), Nat.add(i, Nat.add(k, l)), Lemma.add_assoc(i, k, l))

def WalkAt(+forest: +List<Spec.Tree>, +rounds: Bool, +idx: Nat, +pre: +List<Nat>, +d: Nat, +a: Nat, +k: Nat) -> +List<Spec.Bsr>:
  Spec.walk(forest, rounds, idx, pre, d, a, k)

law walk_at_eq:
  for +forest: +List<Spec.Tree>
  for +rounds: Bool
  for +idx: Nat
  for +pre: +List<Nat>
  for +p2: +List<Nat>
  for +d: Nat
  for +a: Nat
  for +k: Nat
  for +k2: Nat
  for +eP: {pre == p2 : +List<Nat>}
  for +eK: {k == k2 : Nat}
  {Spec.walk(forest, rounds, idx, pre, d, a, k) == Spec.walk(forest, rounds, idx, p2, d, a, k2) : +List<Spec.Bsr>}

def walk_at_eq(forest, rounds, idx, pre, p2, d, a, k, k2, eP, eK):
  Equal.trans(+List<Spec.Bsr>, Spec.walk(forest, rounds, idx, pre, d, a, k), Spec.walk(forest, rounds, idx, p2, d, a, k), Spec.walk(forest, rounds, idx, p2, d, a, k2), Equal.cong(+List<Nat>, +List<Spec.Bsr>, v => Spec.walk(forest, rounds, idx, v, d, a, k), pre, p2, eP), Equal.cong(Nat, +List<Spec.Bsr>, v => Spec.walk(forest, rounds, idx, p2, d, a, v), k, k2, eK))

law place_empty:
  for d: Nat
  for +fr: Bool
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +x: Nat
  for +p: +List<Nat>
  for +a: Nat
  for +k: Nat
  for +eqFr: {Nat.is_eq(x, lg) == fr : Bool}
  {Unb.placeAll(Spec.emptyStep(d, x, p, a, k), lg, idx, pre, i) == Spec.emptyStep(d, tgtIdx(fr, idx, x), tgtPre(fr, pre, p), Nat.add(i, a), Nat.add(i, k)) : +List<Spec.Bsr>}

def place_empty(d, fr, lg, idx, pre, i, x, p, a, k, eqFr):
  match d:
    case 0n:
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 0n, a, k, k)), Spec.at(tgtIdx(fr, idx, x), tgtPre(fr, pre, p), 0n, Nat.add(i, a), Nat.add(i, k), Nat.add(i, k)), [], [], place_at(fr, lg, idx, pre, i, x, p, 0n, a, k, k, eqFr), {==})
    case 1n+e:
      {==}

# The walk of a forest with no node of the extra production, placed.
law place_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +fr: Bool
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +x: Nat
  for +p: +List<Nat>
  for +d: Nat
  for +a: Nat
  for +k: Nat
  for +eqFr: {Nat.is_eq(x, lg) == fr : Bool}
  for +below: {nodesBelow(lg, forest) == True{} : Bool}
  {Unb.placeAll(Spec.walk(forest, rounds, x, p, d, a, k), lg, idx, pre, i) == Spec.walk(forest, rounds, tgtIdx(fr, idx, x), tgtPre(fr, pre, p), d, Nat.add(i, a), Nat.add(i, k)) : +List<Spec.Bsr>}

def place_walk(forest, rounds, fr, lg, idx, pre, i, x, p, d, a, k, eqFr, below):
  match forest rounds:
    case Nil{} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      place_empty(d, fr, lg, idx, pre, i, x, p, a, k, eqFr)
    case Nil{} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      {==}
    case Con{Spec.Leaf{kind}, +ts} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +h = place_at(fr, lg, idx, pre, i, x, p, 1n+d, a, k, 1n+k, eqFr)
      +r = place_walk(ts, False{}, fr, lg, idx, pre, i, x, p, 1n+d, a, 1n+k, eqFr, below)
      +sh = Lemma.add_succ_right(i, k)
      +h2 = Equal.trans(Spec.Bsr, Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, 1n+k)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(i, 1n+k)), Spec.at(tx, tp, 1n+d, ia, ik, 1n+ik), h, Equal.cong(Nat, Spec.Bsr, v => Spec.at(tx, tp, 1n+d, ia, ik, v), Nat.add(i, 1n+k), 1n+ik, sh))
      +r2 = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, 1n+k), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(i, 1n+k)), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, 1n+ik), r, walk_at_eq(ts, False{}, tx, tp, tp, 1n+d, ia, Nat.add(i, 1n+k), 1n+ik, {==}, sh))
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, 1n+k)), Spec.at(tx, tp, 1n+d, ia, ik, 1n+ik), Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, 1n+k), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, 1n+ik), h2, r2)
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +l = List.length(&2, Nat, Spec.leaves(ch))
      +end = Nat.add(k, l)
      +ltQ = Lemma.and_true_left(Nat.is_lt(q, lg), Bool.and(nodesBelow(lg, ch), nodesBelow(lg, ts)), below)
      +bb = Lemma.and_true_right_side(Nat.is_lt(q, lg), Bool.and(nodesBelow(lg, ch), nodesBelow(lg, ts)), below)
      +bCh = Lemma.and_true_left(nodesBelow(lg, ch), nodesBelow(lg, ts), bb)
      +bTs = Lemma.and_true_right_side(nodesBelow(lg, ch), nodesBelow(lg, ts), bb)
      +sh = shift_add(i, k, l)
      +h = place_at(fr, lg, idx, pre, i, x, p, 1n+d, a, k, end, eqFr)
      +h2 = Equal.trans(Spec.Bsr, Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(i, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), h, Equal.cong(Nat, Spec.Bsr, v => Spec.at(tx, tp, 1n+d, ia, ik, v), Nat.add(i, end), Nat.add(ik, l), sh))
      +rCh = place_walk(ch, False{}, False{}, lg, idx, pre, i, q, [], 0n, k, k, lt_neq(q, lg, ltQ), bCh)
      +rTs0 = place_walk(ts, False{}, fr, lg, idx, pre, i, x, p, 1n+d, a, end, eqFr, bTs)
      +rTs = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, end), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(i, end)), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l)), rTs0, walk_at_eq(ts, False{}, tx, tp, tp, 1n+d, ia, Nat.add(i, end), Nat.add(ik, l), {==}, sh))
      +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
      +wTs = Spec.walk(ts, False{}, x, p, 1n+d, a, end)
      +both = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(List.append(&2, Spec.Bsr, wCh, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, Unb.placeAll(wCh, lg, idx, pre, i), Unb.placeAll(wTs, lg, idx, pre, i)), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, ik, ik), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l))), place_app(wCh, wTs, lg, idx, pre, i), app_eq(Unb.placeAll(wCh, lg, idx, pre, i), Spec.walk(ch, False{}, q, [], 0n, ik, ik), Unb.placeAll(wTs, lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l)), rCh, rTs))
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), Unb.placeAll(List.append(&2, Spec.Bsr, wCh, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, ik, ik), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l))), h2, both)
    case Con{Spec.Pick{+b, +ch}, +ts} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +l = List.length(&2, Nat, Spec.leaves(ch))
      +end = Nat.add(k, l)
      +bCh = Lemma.and_true_left(nodesBelow(lg, ch), nodesBelow(lg, ts), below)
      +bTs = Lemma.and_true_right_side(nodesBelow(lg, ch), nodesBelow(lg, ts), below)
      +sh = shift_add(i, k, l)
      +h = place_at(fr, lg, idx, pre, i, x, p, 1n+d, a, k, end, eqFr)
      +h2 = Equal.trans(Spec.Bsr, Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(i, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), h, Equal.cong(Nat, Spec.Bsr, v => Spec.at(tx, tp, 1n+d, ia, ik, v), Nat.add(i, end), Nat.add(ik, l), sh))
      +pp = List.append(&2, Nat, p, [d, b])
      +rCh0 = place_walk(ch, False{}, fr, lg, idx, pre, i, x, pp, 0n, k, k, eqFr, bCh)
      +rCh = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ch, False{}, x, pp, 0n, k, k), lg, idx, pre, i), Spec.walk(ch, False{}, tx, tgtPre(fr, pre, pp), 0n, ik, ik), Spec.walk(ch, False{}, tx, List.append(&2, Nat, tp, [d, b]), 0n, ik, ik), rCh0, walk_at_eq(ch, False{}, tx, tgtPre(fr, pre, pp), List.append(&2, Nat, tp, [d, b]), 0n, ik, ik, ik, tgt_app(fr, pre, p, [d, b]), {==}))
      +rTs0 = place_walk(ts, False{}, fr, lg, idx, pre, i, x, p, 1n+d, a, end, eqFr, bTs)
      +rTs = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, end), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(i, end)), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l)), rTs0, walk_at_eq(ts, False{}, tx, tp, tp, 1n+d, ia, Nat.add(i, end), Nat.add(ik, l), {==}, sh))
      +wCh = Spec.walk(ch, False{}, x, pp, 0n, k, k)
      +wTs = Spec.walk(ts, False{}, x, p, 1n+d, a, end)
      +tCh = Spec.walk(ch, False{}, tx, List.append(&2, Nat, tp, [d, b]), 0n, ik, ik)
      +tTs = Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l))
      +both = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(List.append(&2, Spec.Bsr, wCh, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, Unb.placeAll(wCh, lg, idx, pre, i), Unb.placeAll(wTs, lg, idx, pre, i)), List.append(&2, Spec.Bsr, tCh, tTs), place_app(wCh, wTs, lg, idx, pre, i), app_eq(Unb.placeAll(wCh, lg, idx, pre, i), tCh, Unb.placeAll(wTs, lg, idx, pre, i), tTs, rCh, rTs))
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), Unb.placeAll(List.append(&2, Spec.Bsr, wCh, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, tCh, tTs), h2, both)
    case Con{Spec.Skip{}, +ts} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +h = place_at(fr, lg, idx, pre, i, x, p, 1n+d, a, k, k, eqFr)
      +r = place_walk(ts, False{}, fr, lg, idx, pre, i, x, p, 1n+d, a, k, eqFr, below)
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, k)), Spec.at(tx, tp, 1n+d, ia, ik, ik), Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, k), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, ik), h, r)
    case Con{Spec.Loop{+rs}, +ts} False{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +l = List.length(&2, Nat, Spec.leaves(rs))
      +end = Nat.add(k, l)
      +bRs = Lemma.and_true_left(nodesBelow(lg, rs), nodesBelow(lg, ts), below)
      +bTs = Lemma.and_true_right_side(nodesBelow(lg, rs), nodesBelow(lg, ts), below)
      +sh = shift_add(i, k, l)
      +h = place_at(fr, lg, idx, pre, i, x, p, 1n+d, a, k, end, eqFr)
      +h2 = Equal.trans(Spec.Bsr, Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(i, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), h, Equal.cong(Nat, Spec.Bsr, v => Spec.at(tx, tp, 1n+d, ia, ik, v), Nat.add(i, end), Nat.add(ik, l), sh))
      +pp = List.append(&2, Nat, p, [d])
      +rRs0 = place_walk(rs, True{}, fr, lg, idx, pre, i, x, pp, 0n, k, k, eqFr, bRs)
      +rRs = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(rs, True{}, x, pp, 0n, k, k), lg, idx, pre, i), Spec.walk(rs, True{}, tx, tgtPre(fr, pre, pp), 0n, ik, ik), Spec.walk(rs, True{}, tx, List.append(&2, Nat, tp, [d]), 0n, ik, ik), rRs0, walk_at_eq(rs, True{}, tx, tgtPre(fr, pre, pp), List.append(&2, Nat, tp, [d]), 0n, ik, ik, ik, tgt_app(fr, pre, p, [d]), {==}))
      +rTs0 = place_walk(ts, False{}, fr, lg, idx, pre, i, x, p, 1n+d, a, end, eqFr, bTs)
      +rTs = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ts, False{}, x, p, 1n+d, a, end), lg, idx, pre, i), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(i, end)), Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l)), rTs0, walk_at_eq(ts, False{}, tx, tp, tp, 1n+d, ia, Nat.add(i, end), Nat.add(ik, l), {==}, sh))
      +wRs = Spec.walk(rs, True{}, x, pp, 0n, k, k)
      +wTs = Spec.walk(ts, False{}, x, p, 1n+d, a, end)
      +tRs = Spec.walk(rs, True{}, tx, List.append(&2, Nat, tp, [d]), 0n, ik, ik)
      +tTs = Spec.walk(ts, False{}, tx, tp, 1n+d, ia, Nat.add(ik, l))
      +both = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(List.append(&2, Spec.Bsr, wRs, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, Unb.placeAll(wRs, lg, idx, pre, i), Unb.placeAll(wTs, lg, idx, pre, i)), List.append(&2, Spec.Bsr, tRs, tTs), place_app(wRs, wTs, lg, idx, pre, i), app_eq(Unb.placeAll(wRs, lg, idx, pre, i), tRs, Unb.placeAll(wTs, lg, idx, pre, i), tTs, rRs, rTs))
      cons_eq(Unb.place(lg, idx, pre, i, Spec.at(x, p, 1n+d, a, k, end)), Spec.at(tx, tp, 1n+d, ia, ik, Nat.add(ik, l)), Unb.placeAll(List.append(&2, Spec.Bsr, wRs, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, tRs, tTs), h2, both)
    case Con{Spec.Pick{+b, +ch}, +ts} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      +l = List.length(&2, Nat, Spec.leaves(ch))
      +end = Nat.add(k, l)
      +bCh = Lemma.and_true_left(nodesBelow(lg, ch), nodesBelow(lg, ts), below)
      +bTs = Lemma.and_true_right_side(nodesBelow(lg, ch), nodesBelow(lg, ts), below)
      +sh = shift_add(i, k, l)
      +pp = List.append(&2, Nat, p, [b])
      +rCh0 = place_walk(ch, False{}, fr, lg, idx, pre, i, x, pp, 0n, a, k, eqFr, bCh)
      +rCh = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ch, False{}, x, pp, 0n, a, k), lg, idx, pre, i), Spec.walk(ch, False{}, tx, tgtPre(fr, pre, pp), 0n, ia, ik), Spec.walk(ch, False{}, tx, List.append(&2, Nat, tp, [b]), 0n, ia, ik), rCh0, walk_at_eq(ch, False{}, tx, tgtPre(fr, pre, pp), List.append(&2, Nat, tp, [b]), 0n, ia, ik, ik, tgt_app(fr, pre, p, [b]), {==}))
      +rTs0 = place_walk(ts, True{}, fr, lg, idx, pre, i, x, p, 0n, a, end, eqFr, bTs)
      +rTs = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(Spec.walk(ts, True{}, x, p, 0n, a, end), lg, idx, pre, i), Spec.walk(ts, True{}, tx, tp, 0n, ia, Nat.add(i, end)), Spec.walk(ts, True{}, tx, tp, 0n, ia, Nat.add(ik, l)), rTs0, walk_at_eq(ts, True{}, tx, tp, tp, 0n, ia, Nat.add(i, end), Nat.add(ik, l), {==}, sh))
      +wCh = Spec.walk(ch, False{}, x, pp, 0n, a, k)
      +wTs = Spec.walk(ts, True{}, x, p, 0n, a, end)
      +tCh = Spec.walk(ch, False{}, tx, List.append(&2, Nat, tp, [b]), 0n, ia, ik)
      +tTs = Spec.walk(ts, True{}, tx, tp, 0n, ia, Nat.add(ik, l))
      Equal.trans(+List<Spec.Bsr>, Unb.placeAll(List.append(&2, Spec.Bsr, wCh, wTs), lg, idx, pre, i), List.append(&2, Spec.Bsr, Unb.placeAll(wCh, lg, idx, pre, i), Unb.placeAll(wTs, lg, idx, pre, i)), List.append(&2, Spec.Bsr, tCh, tTs), place_app(wCh, wTs, lg, idx, pre, i), app_eq(Unb.placeAll(wCh, lg, idx, pre, i), tCh, Unb.placeAll(wTs, lg, idx, pre, i), tTs, rCh, rTs))
    case Con{Spec.Leaf{kind}, ts} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      {==}
    case Con{Spec.Node{q, ch}, ts} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      {==}
    case Con{Spec.Skip{}, ts} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      {==}
    case Con{Spec.Loop{rs}, ts} True{}:
      +tx = tgtIdx(fr, idx, x)
      +tp = tgtPre(fr, pre, p)
      +ia = Nat.add(i, a)
      +ik = Nat.add(i, k)
      {==}

# A forest of the grammar has only nodes of its productions.
law fits_below:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for items: +List<Spec.Item>
  for e: {Spec.fits(forest, grammar, items) == True{} : Bool}
  {nodesBelow(List.length(&2, Spec.Production, grammar), forest) == True{} : Bool}

def fits_below(forest, grammar, items, e):
  match forest items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{it, rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), []) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{t, ts} Nil{}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), t <> ts) == True{} : Bool}, Fits.fits_cons_nil(t, ts, grammar, e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      fits_below(ts, grammar, rest, Lemma.and_true_right_side(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Leaf{kind} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      +l = Lemma.and_true_left(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +bc = fits_below(ch, grammar, Spec.rhsOf(grammar, q), Lemma.and_true_right_side(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh))
      +bt = fits_below(ts, grammar, rest, Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both))
      Lemma.and_true_intro(Nat.is_lt(q, List.length(&2, Spec.Production, grammar)), Bool.and(nodesBelow(List.length(&2, Spec.Production, grammar), ch), nodesBelow(List.length(&2, Spec.Production, grammar), ts)), lhs_lt(grammar, q, id, l), Lemma.and_true_intro(nodesBelow(List.length(&2, Spec.Production, grammar), ch), nodesBelow(List.length(&2, Spec.Production, grammar), ts), bc, bt))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Node{q, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Pick{a, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Pick{a, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +bc = fits_below(ch, grammar, Spec.altOf(alts, a), Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh))
      +bt = fits_below(ts, grammar, rest, Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both))
      Lemma.and_true_intro(nodesBelow(List.length(&2, Spec.Production, grammar), ch), nodesBelow(List.length(&2, Spec.Production, grammar), ts), bc, bt)
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +bc = fits_below(ch, grammar, Spec.altOf(alts, a), Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh))
      +bt = fits_below(ts, grammar, rest, Lemma.and_true_right_side(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both))
      Lemma.and_true_intro(nodesBelow(List.length(&2, Spec.Production, grammar), ch), nodesBelow(List.length(&2, Spec.Production, grammar), ts), bc, bt)
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Pick{a, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Pick{a, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Pick{a, ch} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Skip{} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Skip{} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Skip{} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      fits_below(ts, grammar, rest, e)
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Skip{} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Skip{} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Eps{}, +rest}:
      fits_below(ts, grammar, rest, e)
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Loop{rs} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Loop{rs} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Loop{rs} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Loop{rs} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +br = fits_below(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh))
      +bt = fits_below(ts, grammar, rest, Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both))
      Lemma.and_true_intro(nodesBelow(List.length(&2, Spec.Production, grammar), rs), nodesBelow(List.length(&2, Spec.Production, grammar), ts), br, bt)
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +br = fits_below(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh))
      +bt = fits_below(ts, grammar, rest, Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both))
      Lemma.and_true_intro(nodesBelow(List.length(&2, Spec.Production, grammar), rs), nodesBelow(List.length(&2, Spec.Production, grammar), ts), br, bt)
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({nodesBelow(List.length(&2, Spec.Production, grammar), Spec.Loop{rs} <> ts) == True{} : Bool}, Lemma.false_is_not_true(e))

# ======== A NO FROM THE ADMISSIBLE SUB-PARSE LEAVES NO ADMISSIBLE RIVAL ========

law member_place_pick:
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for later: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Spec.bsrMember(Unb.place(lg, idx, pre, i, e), Unb.placeAll(rest, lg, idx, pre, i)) == True{} : Bool}
  {Spec.bsrMember(Unb.place(lg, idx, pre, i, e), Unb.place(lg, idx, pre, i, x) <> Unb.placeAll(rest, lg, idx, pre, i)) == True{} : Bool}

def member_place_pick(e, x, rest, lg, idx, pre, i, cases, later):
  match cases:
    case Inl{same0}:
      +same = {same0 : {e == x : Spec.Bsr}}
      +pr = Unb.placeAll(rest, lg, idx, pre, i)
      Equal.trans(Bool, Spec.bsrMember(Unb.place(lg, idx, pre, i, e), Unb.place(lg, idx, pre, i, x) <> pr), Spec.bsrMember(Unb.place(lg, idx, pre, i, x), Unb.place(lg, idx, pre, i, x) <> pr), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(Unb.place(lg, idx, pre, i, v), Unb.place(lg, idx, pre, i, x) <> pr), e, x, same), R.bsr_member_head(Unb.place(lg, idx, pre, i, x), pr))
    case Inr{m}:
      R.bsr_member_cons(Unb.place(lg, idx, pre, i, e), Unb.place(lg, idx, pre, i, x), Unb.placeAll(rest, lg, idx, pre, i), later(m))

law member_place:
  for set: +List<Spec.Bsr>
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, set) == True{} : Bool}
  {Spec.bsrMember(Unb.place(lg, idx, pre, i, e), Unb.placeAll(set, lg, idx, pre, i)) == True{} : Bool}

def member_place(set, lg, idx, pre, i, e, m):
  match set:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(Unb.place(lg, idx, pre, i, e), []) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      member_place_pick(e, x, rest, lg, idx, pre, i, G.ebnf_member_cases(e, x, rest, m),
        later => member_place(rest, lg, idx, pre, i, e, later))

law all_in_place:
  for xs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +lg: Nat
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +h: {Spec.allIn(xs, set) == True{} : Bool}
  {Spec.allIn(Unb.placeAll(xs, lg, idx, pre, i), Unb.placeAll(set, lg, idx, pre, i)) == True{} : Bool}

def all_in_place(xs, set, lg, idx, pre, i, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hx = Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(rest, set), h)
      +hr = Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(rest, set), h)
      Lemma.and_true_intro(Spec.bsrMember(Unb.place(lg, idx, pre, i, x), Unb.placeAll(set, lg, idx, pre, i)), Spec.allIn(Unb.placeAll(rest, lg, idx, pre, i), Unb.placeAll(set, lg, idx, pre, i)), member_place(set, lg, idx, pre, i, x, hx), all_in_place(rest, set, lg, idx, pre, i, hr))

# ---- What a no says ----

def EndNo(+found: Maybe<&2, +List<Spec.Bsr>>, +idx: Nat, +pre: +List<Nat>, +n: Nat, +i: Nat, +j: Nat) -> Type:
  &ks: +List<Spec.Bsr> -> {found == Some{ks} : Maybe<&2, +List<Spec.Bsr>>} & {Unb.hasStep(ks, idx, List.append(&2, Nat, pre, [n]), i, j) == False{} : Bool}

law end_in_false:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +idx: Nat
  for +pre: +List<Nat>
  for +n: Nat
  for +i: Nat
  for +j: Nat
  for e: {Unb.endIn(found, idx, pre, n, i, j) == Some{False{}} : Maybe<&2, Bool>}
  EndNo(found, idx, pre, n, i, j)

def end_in_false(found, idx, pre, n, i, j, e):
  match found:
    case Some{+ks}:
      (ks, ({==}, Equal.cong(Maybe<&2, Bool>, Bool, v => Sub.boolOr(v), Some{Unb.hasStep(ks, idx, List.append(&2, Nat, pre, [n]), i, j)}, Some{False{}}, e)))
    case None{}:
      Empty.absurd(EndNo(None{}, idx, pre, n, i, j), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Bool>, Bool, v => Sub.isNoneB(v), None{}, Some{False{}}, e)))

def PrunedIs(+found: Maybe<&2, +List<Spec.Bsr>>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +ks: +List<Spec.Bsr>) -> Type:
  &es: +List<Spec.Bsr> -> {found == Some{es} : Maybe<&2, +List<Spec.Bsr>>} & {Unb.closedOver(es, Unb.grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input), grammar, input) == True{} : Bool} & {Unb.grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input) == ks : +List<Spec.Bsr>}

law pruned_some:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +ks: +List<Spec.Bsr>
  for e: {Unb.prunedFrom(found, grammar, input) == Some{ks} : Maybe<&2, +List<Spec.Bsr>>}
  PrunedIs(found, grammar, input, ks)

def pruned_some(found, grammar, input, ks, e):
  match found:
    case Some{+es}:
      +g = Unb.grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input)
      (es, ({==}, Sub.prefer_pick_facts(Unb.closedOver(es, g, grammar, input), g, ks, e)))
    case None{}:
      Empty.absurd(PrunedIs(None{}, grammar, input, ks), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{ks}, e)))

def PlacedIs(+found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +idx: Nat, +pre: +List<Nat>, +i: Nat, +js: +List<Spec.Bsr>) -> Type:
  &cs: +List<Spec.Bsr> -> {found == Some{cs} : Maybe<&2, +List<Spec.Bsr>>} & {Guard.allKnown(Unb.placeAll(cs, List.length(&2, Spec.Production, grammar), idx, pre, i), fuel, grammar, gm, input) == True{} : Bool} & {Guard.guardKept(Unb.placeAll(cs, List.length(&2, Spec.Production, grammar), idx, pre, i), fuel, grammar, gm, input) == js : +List<Spec.Bsr>}

law placed_some:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +idx: Nat
  for +pre: +List<Nat>
  for +i: Nat
  for +js: +List<Spec.Bsr>
  for e: {Unb.placedFrom(found, fuel, grammar, gm, input, idx, pre, i) == Some{js} : Maybe<&2, +List<Spec.Bsr>>}
  PlacedIs(found, fuel, grammar, gm, input, idx, pre, i, js)

def placed_some(found, fuel, grammar, gm, input, idx, pre, i, js, e):
  match found:
    case Some{+cs}:
      +p = Unb.placeAll(cs, List.length(&2, Spec.Production, grammar), idx, pre, i)
      (cs, ({==}, Sub.prefer_pick_facts(Guard.allKnown(p, fuel, grammar, gm, input), Guard.guardKept(p, fuel, grammar, gm, input), js, e)))
    case None{}:
      Empty.absurd(PlacedIs(None{}, fuel, grammar, gm, input, idx, pre, i, js), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{js}, e)))

# If the admissible sub-parse says no, no admissible forest for the items, in place,
# spells the tokens. The forest gives a tree of the sub-parse; its steps, put back in
# place, are the forest's own walk; the guard oracle keeps them (PROOF_GUARD's walk), so
# they are judged; the pruning keeps them; and so the end of the sequence is there.
law adm_core:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +o: PG.Own
  for +idx: Nat
  for +pre: +List<Nat>
  for +pEq: {pre == Gll.reverseOnto(PG.ownRpath(o), []) : +List<Nat>}
  for +facts: PG.OwnFacts(o, grammar, idx)
  for +rem: {G.dropItems(0n, Gll.seqAt(grammar, idx, PG.ownRpath(o))) == PG.ownItems(o, grammar, idx) : +List<Spec.Item>}
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, PG.ownItems(o, grammar, idx)) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(f), after) == Lemma.dropN(k, input) : +List<Nat>}
  for holds: Spec.AllHold(grammar, PG.ownGuards(o, gm, idx), PG.ownItems(o, grammar, idx), f, List.append(&2, Nat, Spec.leaves(f), after))
  for adm: Spec.Admissible(grammar, gm, f, PG.ownItems(o, grammar, idx), idx, pre, 0n, after)
  for +cs: +List<Spec.Bsr>
  for +eC: {Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))) == Some{cs} : Maybe<&2, +List<Spec.Bsr>>}
  for +okP: {Guard.allKnown(Unb.placeAll(cs, List.length(&2, Spec.Production, grammar), idx, pre, k), fuel, grammar, gm, input) == True{} : Bool}
  for +js: +List<Spec.Bsr>
  for +keptEq: {Guard.guardKept(Unb.placeAll(cs, List.length(&2, Spec.Production, grammar), idx, pre, k), fuel, grammar, gm, input) == js : +List<Spec.Bsr>}
  for +closed: {Unb.closedOver(js, Unb.grow(1n+List.length(&2, Spec.Bsr, js), js, [], grammar, input), grammar, input) == True{} : Bool}
  for +ks: +List<Spec.Bsr>
  for +growEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, js), js, [], grammar, input) == ks : +List<Spec.Bsr>}
  for +noEnd: {Unb.hasStep(ks, idx, List.append(&2, Nat, pre, [List.length(&2, Spec.Item, PG.ownItems(o, grammar, idx))]), k, Nat.add(k, List.length(&2, Nat, w))) == False{} : Bool}
  Empty

def adm_core(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, cs, eC, okP, js, keptEq, closed, ks, growEq, noEnd):
  +items = PG.ownItems(o, grammar, idx)
  +j = Nat.add(k, List.length(&2, Nat, w))
  +toks = Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))
  +g2 = Prefer.extended(grammar, items)
  +fresh = Prefer.freshNt(grammar)
  +lg = List.length(&2, Spec.Production, grammar)
  +n = List.length(&2, Spec.Item, items)
  +tEq = Sub.tokens_spelled(input, k, w, sp)
  +lf = Spec.leaves(f)
  +fitsF2 = Equal.trans(Bool, Spec.fits(f, g2, Spec.rhsOf(g2, lg)), Spec.fits(f, g2, items), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f, g2, v), Spec.rhsOf(g2, lg), items, Sub.rhs_of_last(grammar, fresh, items)), Sub.fits_ext(f, grammar, [Spec.Production{fresh, items}], items, fitF))
  +fitT = Lemma.and_true_intro(Bool.and(Spec.lhsIs(g2, lg, fresh), Spec.fits(f, g2, Spec.rhsOf(g2, lg))), Spec.fits([], g2, []), Lemma.and_true_intro(Spec.lhsIs(g2, lg, fresh), Spec.fits(f, g2, Spec.rhsOf(g2, lg)), Sub.lhs_is_last(grammar, fresh, items), fitsF2), {==})
  +lfToks = Equal.trans(+List<Nat>, lf, w, toks, leavesF, Equal.sym(+List<Nat>, toks, w, tEq))
  +leavesT = Equal.trans(+List<Nat>, List.append(&2, Nat, lf, []), lf, toks, Lemma.append_nil_right(lf), lfToks)
  stepsIn = Sub.steps_in_found(Check.checkedSteps(fuel, g2, fresh, toks), g2, fresh, toks, cs, R.checked_found(fuel, g2, fresh, toks), eC)
  +allT = stepsIn(Spec.Node{lg, f}, fitT, leavesT)
  +P = Unb.placeAll(cs, lg, idx, pre, k)
  +wSub = Spec.walk(f, False{}, lg, [], 0n, 0n, 0n)
  +wHere = Spec.walk(f, False{}, idx, pre, 0n, k, k)
  +allP0 = all_in_place(wSub, cs, lg, idx, pre, k, allT)
  +pw = place_walk(f, False{}, True{}, lg, idx, pre, k, lg, [], 0n, 0n, 0n, Lemma.nat_eq_refl(lg), fits_below(f, grammar, items, fitF))
  +wEq = Equal.trans(+List<Spec.Bsr>, Spec.walk(f, False{}, idx, List.append(&2, Nat, pre, []), 0n, Nat.add(k, 0n), Nat.add(k, 0n)), Spec.walk(f, False{}, idx, pre, 0n, Nat.add(k, 0n), Nat.add(k, 0n)), wHere,
    Equal.cong(+List<Nat>, +List<Spec.Bsr>, v => Spec.walk(f, False{}, idx, v, 0n, Nat.add(k, 0n), Nat.add(k, 0n)), List.append(&2, Nat, pre, []), pre, Lemma.append_nil_right(pre)),
    Equal.cong(Nat, +List<Spec.Bsr>, v => Spec.walk(f, False{}, idx, pre, 0n, v, v), Nat.add(k, 0n), k, Lemma.add_zero_right(k)))
  +pwHere = Equal.trans(+List<Spec.Bsr>, Unb.placeAll(wSub, lg, idx, pre, k), Spec.walk(f, False{}, idx, List.append(&2, Nat, pre, []), 0n, Nat.add(k, 0n), Nat.add(k, 0n)), wHere, pw, wEq)
  +allS = Equal.trans(Bool, Spec.allIn(wHere, P), Spec.allIn(Unb.placeAll(wSub, lg, idx, pre, k), P), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, P), wHere, Unb.placeAll(wSub, lg, idx, pre, k), Equal.sym(+List<Spec.Bsr>, Unb.placeAll(wSub, lg, idx, pre, k), wHere, pwHere)), allP0)
  +ownK = PG.owner_kept(o, fuel, grammar, gm, input, idx, pre, pEq, facts, P, okP, f, k, after, pos, fitF, allS, holds)
  +kw = PG.keep_walk(f, False{}, grammar, gm, input, fuel, P, okP, idx, PG.ownRpath(o), pre, 0n, k, k, items, Spec.Group{}, [], after, pEq, pos, (rem, (fitF, (allS, (ownK, adm)))))
  +allJ = Equal.trans(Bool, Spec.allIn(wHere, js), Spec.allIn(wHere, Guard.guardKept(P, fuel, grammar, gm, input)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(wHere, v), js, Guard.guardKept(P, fuel, grammar, gm, input), Equal.sym(+List<Spec.Bsr>, Guard.guardKept(P, fuel, grammar, gm, input), js, keptEq)), kw)
  +gg = Unb.grow(1n+List.length(&2, Spec.Bsr, js), js, [], grammar, input)
  +sw = sw_walk(f, False{}, grammar, input, js, gg, closed, idx, PG.ownRpath(o), pre, 0n, k, k, items, Spec.Group{}, [], after, pEq, pos, (rem, (fitF, (allJ, start_here(PG.ownRpath(o), gg, grammar, idx, k)))))
  +countEq = Fits.fits_count(f, grammar, items, fitF)
  +hE = seq_end_kept(f, gg, idx, pre, k, k, n, countEq, sw)
  +pth = List.append(&2, Nat, pre, [n])
  +lenEq = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), w, lf, Equal.sym(+List<Nat>, lf, w, leavesF))
  +hE2 = Equal.trans(Bool, Unb.hasStep(ks, idx, pth, k, j), Unb.hasStep(gg, idx, pth, k, j), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Unb.hasStep(v, idx, pth, k, j), ks, gg, Equal.sym(+List<Spec.Bsr>, gg, ks, growEq)),
    Equal.trans(Bool, Unb.hasStep(gg, idx, pth, k, j), Unb.hasStep(gg, idx, pth, k, Nat.add(k, List.length(&2, Nat, lf))), True{}, Equal.cong(Nat, Bool, v => Unb.hasStep(gg, idx, pth, k, Nat.add(k, v)), List.length(&2, Nat, w), List.length(&2, Nat, lf), lenEq), hE))
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, Unb.hasStep(ks, idx, pth, k, j), False{}, Equal.sym(Bool, Unb.hasStep(ks, idx, pth, k, j), True{}, hE2), noEnd))

law adm_r3:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +o: PG.Own
  for +idx: Nat
  for +pre: +List<Nat>
  for +pEq: {pre == Gll.reverseOnto(PG.ownRpath(o), []) : +List<Nat>}
  for +facts: PG.OwnFacts(o, grammar, idx)
  for +rem: {G.dropItems(0n, Gll.seqAt(grammar, idx, PG.ownRpath(o))) == PG.ownItems(o, grammar, idx) : +List<Spec.Item>}
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, PG.ownItems(o, grammar, idx)) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(f), after) == Lemma.dropN(k, input) : +List<Nat>}
  for holds: Spec.AllHold(grammar, PG.ownGuards(o, gm, idx), PG.ownItems(o, grammar, idx), f, List.append(&2, Nat, Spec.leaves(f), after))
  for adm: Spec.Admissible(grammar, gm, f, PG.ownItems(o, grammar, idx), idx, pre, 0n, after)
  for +js: +List<Spec.Bsr>
  for +closed: {Unb.closedOver(js, Unb.grow(1n+List.length(&2, Spec.Bsr, js), js, [], grammar, input), grammar, input) == True{} : Bool}
  for +ks: +List<Spec.Bsr>
  for +growEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, js), js, [], grammar, input) == ks : +List<Spec.Bsr>}
  for +noEnd: {Unb.hasStep(ks, idx, List.append(&2, Nat, pre, [List.length(&2, Spec.Item, PG.ownItems(o, grammar, idx))]), k, Nat.add(k, List.length(&2, Nat, w))) == False{} : Bool}
  for pl: PlacedIs(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k, js)
  Empty

def adm_r3(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, js, closed, ks, growEq, noEnd, pl):
  match pl:
    case (cs0, rest0):
      match rest0:
        case (eC, (okP, keptEq)):
          +cs = {cs0 : +List<Spec.Bsr>}
          adm_core(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, cs, eC, okP, js, keptEq, closed, ks, growEq, noEnd)

law adm_r2:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +o: PG.Own
  for +idx: Nat
  for +pre: +List<Nat>
  for +pEq: {pre == Gll.reverseOnto(PG.ownRpath(o), []) : +List<Nat>}
  for +facts: PG.OwnFacts(o, grammar, idx)
  for +rem: {G.dropItems(0n, Gll.seqAt(grammar, idx, PG.ownRpath(o))) == PG.ownItems(o, grammar, idx) : +List<Spec.Item>}
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, PG.ownItems(o, grammar, idx)) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(f), after) == Lemma.dropN(k, input) : +List<Nat>}
  for holds: Spec.AllHold(grammar, PG.ownGuards(o, gm, idx), PG.ownItems(o, grammar, idx), f, List.append(&2, Nat, Spec.leaves(f), after))
  for adm: Spec.Admissible(grammar, gm, f, PG.ownItems(o, grammar, idx), idx, pre, 0n, after)
  for +ks: +List<Spec.Bsr>
  for +noEnd: {Unb.hasStep(ks, idx, List.append(&2, Nat, pre, [List.length(&2, Spec.Item, PG.ownItems(o, grammar, idx))]), k, Nat.add(k, List.length(&2, Nat, w))) == False{} : Bool}
  for pr: PrunedIs(Unb.placedFrom(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k), grammar, input, ks)
  Empty

def adm_r2(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, ks, noEnd, pr):
  match pr:
    case (js0, rest0):
      match rest0:
        case (eJ, (closed, growEq)):
          +js = {js0 : +List<Spec.Bsr>}
          adm_r3(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, js, closed, ks, growEq, noEnd, placed_some(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k, js, eJ))

law adm_r1:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +o: PG.Own
  for +idx: Nat
  for +pre: +List<Nat>
  for +pEq: {pre == Gll.reverseOnto(PG.ownRpath(o), []) : +List<Nat>}
  for +facts: PG.OwnFacts(o, grammar, idx)
  for +rem: {G.dropItems(0n, Gll.seqAt(grammar, idx, PG.ownRpath(o))) == PG.ownItems(o, grammar, idx) : +List<Spec.Item>}
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, PG.ownItems(o, grammar, idx)) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(f), after) == Lemma.dropN(k, input) : +List<Nat>}
  for holds: Spec.AllHold(grammar, PG.ownGuards(o, gm, idx), PG.ownItems(o, grammar, idx), f, List.append(&2, Nat, Spec.leaves(f), after))
  for adm: Spec.Admissible(grammar, gm, f, PG.ownItems(o, grammar, idx), idx, pre, 0n, after)
  for en: EndNo(Unb.prunedFrom(Unb.placedFrom(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k), grammar, input), idx, pre, List.length(&2, Spec.Item, PG.ownItems(o, grammar, idx)), k, Nat.add(k, List.length(&2, Nat, w)))
  Empty

def adm_r1(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, en):
  match en:
    case (ks0, rest0):
      match rest0:
        case (eK, noEnd):
          +ks = {ks0 : +List<Spec.Bsr>}
          adm_r2(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, ks, noEnd, pruned_some(Unb.placedFrom(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k), grammar, input, ks, eK))

law adm_refutes:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +o: PG.Own
  for +idx: Nat
  for +pre: +List<Nat>
  for +pEq: {pre == Gll.reverseOnto(PG.ownRpath(o), []) : +List<Nat>}
  for +facts: PG.OwnFacts(o, grammar, idx)
  for +rem: {G.dropItems(0n, Gll.seqAt(grammar, idx, PG.ownRpath(o))) == PG.ownItems(o, grammar, idx) : +List<Spec.Item>}
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, PG.ownItems(o, grammar, idx)) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(f), after) == Lemma.dropN(k, input) : +List<Nat>}
  for holds: Spec.AllHold(grammar, PG.ownGuards(o, gm, idx), PG.ownItems(o, grammar, idx), f, List.append(&2, Nat, Spec.leaves(f), after))
  for adm: Spec.Admissible(grammar, gm, f, PG.ownItems(o, grammar, idx), idx, pre, 0n, after)
  for dh: {Unb.derivesAdm(fuel, grammar, gm, PG.ownItems(o, grammar, idx), idx, pre, input, k, Nat.add(k, List.length(&2, Nat, w))) == Some{False{}} : Maybe<&2, Bool>}
  Empty

def adm_refutes(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, dh):
  adm_r1(fuel, grammar, gm, o, idx, pre, pEq, facts, rem, input, k, w, sp, f, fitF, leavesF, after, pos, holds, adm, end_in_false(Unb.prunedFrom(Unb.placedFrom(Check.checkedSteps(fuel, Prefer.extended(grammar, PG.ownItems(o, grammar, idx)), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), fuel, grammar, gm, input, idx, pre, k), grammar, input), idx, pre, List.length(&2, Spec.Item, PG.ownItems(o, grammar, idx)), k, Nat.add(k, List.length(&2, Nat, w)), dh))
