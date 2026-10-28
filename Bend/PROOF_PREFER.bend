import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_PRUNE.bend as P
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# @prefer AND @avoid CHOOSE EXACTLY THE SELECTED TREES: prefer_avoid_exact.
#
# Both halves walk a parse tree the way `Spec.walk` lists its steps, next to
# `Spec.Unbeaten`, which walks it the same way.
#
# A tree that uses only kept steps is unbeaten. At every node (and every pick) the
# step that completes it is kept, so the oracle's verdict on it was Keep: for every
# sibling of higher rank, the checked parser found no tree over the node's tokens. A
# rival would be such a tree, and `gll_every_parse_step` says the parser misses none.
#
# A selected tree uses only kept steps. A step that completes no choice is always kept.
# One that completes a node is in the exact set; were it removed, its certificate would
# be a rival of the node, which a selected tree has not. The certificate's forest avoids
# the set C; the nonterminals above the node over the same tokens are in C, because each
# of them has a step in the exact set that the rule growing C fires on, and C is closed.

# ======== SMALL FACTS ========

law lt_irrefl:
  for n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}

def lt_irrefl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

law outranks_self:
  for r: Spec.Rank
  {Spec.outranks(r, r) == False{} : Bool}

def outranks_self(r):
  lt_irrefl(Spec.rankNat(r))

law lt_one_zero:
  for a: Nat
  for e: {Nat.is_lt(a, 1n) == True{} : Bool}
  {a == 0n : Nat}

def lt_one_zero(a, e):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, Lemma.lt_zero_false(p, e))

law not_true_false:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_true_false(b, e):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(e))
    case False{}:
      {==}

law nats_eq_refl:
  for xs: +List<Nat>
  {Gll.natsEq(xs, xs) == True{} : Bool}

def nats_eq_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Nat.is_eq(x, x), Gll.natsEq(rest, rest), Lemma.nat_eq_refl(x), nats_eq_refl(rest))

# The tokens from k to the end of what is spelled at k are what is spelled.
law tokens_spelled:
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  {Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w))) == w : +List<Nat>}

def tokens_spelled(input, k, w, sp):
  %Equal.sym(Nat, Nat.sub(Nat.add(k, List.length(&2, Nat, w)), k), List.length(&2, Nat, w), Lemma.sub_add_left(k, List.length(&2, Nat, w))) : {Lemma.slice(input, k, _) == w : +List<Nat>}
  Equal.sym(+List<Nat>, w, Lemma.slice(input, k, List.length(&2, Nat, w)), sp)

law member_app_right:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  {Spec.bsrMember(e, List.append(&2, Spec.Bsr, xs, ys)) == True{} : Bool}

def member_app_right(xs, ys, e, m):
  match xs:
    case Nil{}:
      m
    case Con{+x, +rest}:
      R.bsr_member_cons(e, x, List.append(&2, Spec.Bsr, rest, ys), member_app_right(rest, ys, e, m))

law member_left_pick:
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Spec.bsrMember(e, List.append(&2, Spec.Bsr, rest, ys)) == True{} : Bool}
  {Spec.bsrMember(e, x <> List.append(&2, Spec.Bsr, rest, ys)) == True{} : Bool}

def member_left_pick(e, x, rest, ys, cases, searchRest):
  match cases:
    case Inl{same}:
      %same : {Spec.bsrMember(e, _ <> List.append(&2, Spec.Bsr, rest, ys)) == True{} : Bool}
      R.bsr_member_head(e, List.append(&2, Spec.Bsr, rest, ys))
    case Inr{later}:
      R.bsr_member_cons(e, x, List.append(&2, Spec.Bsr, rest, ys), searchRest(later))

law member_app_left:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, xs) == True{} : Bool}
  {Spec.bsrMember(e, List.append(&2, Spec.Bsr, xs, ys)) == True{} : Bool}

def member_app_left(xs, ys, e, m):
  match xs:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(e, ys) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      member_left_pick(e, x, rest, ys, G.ebnf_member_cases(e, x, rest, m), later => member_app_left(rest, ys, e, later))


# ======== WHAT THE ORACLE'S ANSWER SAYS ========

law prefer_pick_facts:
  for ok: Bool
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for got: {Prefer.preferPick(ok, ys) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {ok == True{} : Bool} & {ys == set : +List<Spec.Bsr>}

def prefer_pick_facts(ok, ys, set, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{ys}, Some{set}, got))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {ys == set : +List<Spec.Bsr>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# The oracle's answer: the exact set s, every step of it passed, and the answer is
# the kept part of s.
def PreferFacts(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Type:
  &s: +List<Spec.Bsr> -> {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>} & {Prefer.allStepsOk(s, fuel, grammar, marks, input, s) == True{} : Bool} & {Prefer.kept(s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}

law prefer_both:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +eqF: {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}
  for facts: {Prefer.allStepsOk(s, fuel, grammar, marks, input, s) == True{} : Bool} & {Prefer.kept(s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}
  PreferFacts(fuel, grammar, marks, start, input, set)

def prefer_both(fuel, grammar, marks, start, input, set, s, eqF, facts):
  match facts:
    case (ok, same):
      (s, (eqF, (ok, same)))

law prefer_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +eqF: {Exact.exactSteps(fuel, grammar, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Prefer.preferFrom(found, fuel, grammar, marks, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  PreferFacts(fuel, grammar, marks, start, input, set)

def prefer_found(found, fuel, grammar, marks, start, input, set, eqF, got):
  match found:
    case Some{+s}:
      prefer_both(fuel, grammar, marks, start, input, set, s, eqF, prefer_pick_facts(Prefer.allStepsOk(s, fuel, grammar, marks, input, s), Prefer.kept(s, fuel, grammar, marks, input), set, got))
    case None{}:
      Empty.absurd(PreferFacts(fuel, grammar, marks, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# ======== THE KEPT STEPS ========

law kept_sub_pick:
  for b: Bool
  for +e: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Spec.bsrMember(y, rest) == True{} : Bool}
  {Spec.bsrMember(y, e <> rest) == True{} : Bool}

def kept_sub_pick(b, e, rest, ks, y, m, searchRest):
  match b:
    case True{}:
      G.member_pick(y, e, ks, e <> rest, G.ebnf_member_cases(y, e, ks, m), R.bsr_member_head(e, rest), later => R.bsr_member_cons(y, e, rest, searchRest(later)))
    case False{}:
      R.bsr_member_cons(y, e, rest, searchRest(m))

# A kept step is a step of the set.
law kept_sub:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prefer.kept(es, fuel, grammar, marks, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def kept_sub(es, fuel, grammar, marks, input, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      kept_sub_pick(Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), e, rest, Prefer.kept(rest, fuel, grammar, marks, input), y, m,
        later => kept_sub(rest, fuel, grammar, marks, input, y, later))

law kept_keep_case:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for -ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, ks) == True{} : Bool}>
  for +isB: {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}
  {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}

def kept_keep_case(fuel, grammar, marks, input, e, ks, y, cases, isB, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, _)) == True{} : Bool}
      isB
    case Inr{later}:
      searchRest(later)

law kept_keep_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)) == b : Bool}
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}
  {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}

def kept_keep_pick(b, fuel, grammar, marks, input, e, isB, ks, y, m, searchRest):
  match b:
    case True{}:
      kept_keep_case(fuel, grammar, marks, input, e, ks, y, G.ebnf_member_cases(y, e, ks, m), isB, searchRest)
    case False{}:
      searchRest(m)

# A kept step's verdict was Keep.
law kept_keep:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prefer.kept(es, fuel, grammar, marks, input)) == True{} : Bool}
  {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}

def kept_keep(es, fuel, grammar, marks, input, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      kept_keep_pick(Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), fuel, grammar, marks, input, e, {==}, Prefer.kept(rest, fuel, grammar, marks, input), y, m,
        later => kept_keep(rest, fuel, grammar, marks, input, y, later))

law kept_of_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)) == b : Bool}
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +ok: {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Spec.bsrMember(y, ks) == True{} : Bool}
  {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}

def kept_of_pick(b, fuel, grammar, marks, input, e, isB, rest, ks, y, cases, ok, searchRest):
  match cases:
    case Inl{same0}:
      +same = {same0 : {y == e : Spec.Bsr}}
      +okE = Equal.trans(Bool, Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)), True{}, Equal.cong(Spec.Bsr, Bool, v => Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, v)), e, y, Equal.sym(Spec.Bsr, y, e, same)), ok)
      +isT = Equal.trans(Bool, b, Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), True{}, Equal.sym(Bool, Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), b, isB), okE)
      %Equal.sym(Spec.Bsr, y, e, same) : {Spec.bsrMember(_, Prune.keepPick(b, e, ks)) == True{} : Bool}
      R.keep_link_head(b, isT, e, ks)
    case Inr{later}:
      R.keep_link_later(b, e, ks, y, searchRest(later))

# A step of the set whose verdict was Keep is kept.
law kept_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  for +ok: {Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, y)) == True{} : Bool}
  {Spec.bsrMember(y, Prefer.kept(es, fuel, grammar, marks, input)) == True{} : Bool}

def kept_of(es, fuel, grammar, marks, input, y, m, ok):
  match es:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, []) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      kept_of_pick(Prefer.isKeep(Prefer.verdictOf(fuel, grammar, marks, input, e)), fuel, grammar, marks, input, e, {==}, rest, Prefer.kept(rest, fuel, grammar, marks, input), y, G.ebnf_member_cases(y, e, rest, m), ok,
        later => kept_of(rest, fuel, grammar, marks, input, y, later, ok))

law step_ok_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +e: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +okE: {Prefer.stepOk(fuel, grammar, marks, input, s, e) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Prefer.stepOk(fuel, grammar, marks, input, s, y) == True{} : Bool}
  {Prefer.stepOk(fuel, grammar, marks, input, s, y) == True{} : Bool}

def step_ok_pick(fuel, grammar, marks, input, s, y, e, rest, cases, okE, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Prefer.stepOk(fuel, grammar, marks, input, s, _) == True{} : Bool}
      okE
    case Inr{later}:
      searchRest(later)

# Every step of the set passed the oracle's checks.
law step_ok_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for all: {Prefer.allStepsOk(es, fuel, grammar, marks, input, s) == True{} : Bool}
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  {Prefer.stepOk(fuel, grammar, marks, input, s, y) == True{} : Bool}

def step_ok_of(es, fuel, grammar, marks, input, s, y, all, m):
  match es:
    case Nil{}:
      Empty.absurd({Prefer.stepOk(fuel, grammar, marks, input, s, y) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      +both = all
      step_ok_pick(fuel, grammar, marks, input, s, y, e, rest, G.ebnf_member_cases(y, e, rest, m),
        Lemma.and_true_left(Prefer.stepOk(fuel, grammar, marks, input, s, e), Prefer.allStepsOk(rest, fuel, grammar, marks, input, s), both),
        later => step_ok_of(rest, fuel, grammar, marks, input, s, y, Lemma.and_true_right_side(Prefer.stepOk(fuel, grammar, marks, input, s, e), Prefer.allStepsOk(rest, fuel, grammar, marks, input, s), both), later))
