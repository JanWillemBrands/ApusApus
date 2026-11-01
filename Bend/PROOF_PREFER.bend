import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./UNBEATEN.bend as Unb
import ./PROOF_GUARD.bend as PG
import ./PROOF_SUPPORT.bend as Sup
import ./PROOF_SUBPARSE.bend as Sub
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
# A unbeaten tree uses only kept steps. A step that completes no choice is always kept.
# One that completes a node is in the exact set; were it removed, its certificate would
# be a rival of the node, which a unbeaten tree has not. The certificate's forest avoids
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

# The oracle's answer: the exact set s, every step of it passed, and the answer is
# the kept part of s.
def PreferFacts(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Type:
  &s: +List<Spec.Bsr> -> {Guard.guardSteps(fuel, grammar, gm, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>} & {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool} & {Unb.kept(s, fuel, grammar, gm, marks, input) == set : +List<Spec.Bsr>}

law prefer_both:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +eqF: {Guard.guardSteps(fuel, grammar, gm, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}
  for facts: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool} & {Unb.kept(s, fuel, grammar, gm, marks, input) == set : +List<Spec.Bsr>}
  PreferFacts(fuel, grammar, gm, marks, start, input, set)

def prefer_both(fuel, grammar, gm, marks, start, input, set, s, eqF, facts):
  match facts:
    case (ok, same):
      (s, (eqF, (ok, same)))

law prefer_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +eqF: {Guard.guardSteps(fuel, grammar, gm, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Unb.unbeatenFrom(found, fuel, grammar, gm, marks, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  PreferFacts(fuel, grammar, gm, marks, start, input, set)

def prefer_found(found, fuel, grammar, gm, marks, start, input, set, eqF, got):
  match found:
    case Some{+s}:
      prefer_both(fuel, grammar, gm, marks, start, input, set, s, eqF, Sub.prefer_pick_facts(Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)), Unb.kept(s, fuel, grammar, gm, marks, input), set, got))
    case None{}:
      Empty.absurd(PreferFacts(fuel, grammar, gm, marks, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

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
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Unb.kept(es, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def kept_sub(es, fuel, grammar, gm, marks, input, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      kept_sub_pick(Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), e, rest, Unb.kept(rest, fuel, grammar, gm, marks, input), y, m,
        later => kept_sub(rest, fuel, grammar, gm, marks, input, y, later))

law kept_keep_case:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for -ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, ks) == True{} : Bool}>
  for +isB: {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}
  {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}

def kept_keep_case(fuel, grammar, gm, marks, input, e, ks, y, cases, isB, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, _)) == True{} : Bool}
      isB
    case Inr{later}:
      searchRest(later)

law kept_keep_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)) == b : Bool}
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}
  {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}

def kept_keep_pick(b, fuel, grammar, gm, marks, input, e, isB, ks, y, m, searchRest):
  match b:
    case True{}:
      kept_keep_case(fuel, grammar, gm, marks, input, e, ks, y, G.ebnf_member_cases(y, e, ks, m), isB, searchRest)
    case False{}:
      searchRest(m)

# A kept step's verdict was Keep.
law kept_keep:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Unb.kept(es, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}

def kept_keep(es, fuel, grammar, gm, marks, input, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      kept_keep_pick(Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), fuel, grammar, gm, marks, input, e, {==}, Unb.kept(rest, fuel, grammar, gm, marks, input), y, m,
        later => kept_keep(rest, fuel, grammar, gm, marks, input, y, later))

law kept_of_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)) == b : Bool}
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +ok: {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Spec.bsrMember(y, ks) == True{} : Bool}
  {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}

def kept_of_pick(b, fuel, grammar, gm, marks, input, e, isB, rest, ks, y, cases, ok, searchRest):
  match cases:
    case Inl{same0}:
      +same = {same0 : {y == e : Spec.Bsr}}
      +okE = Equal.trans(Bool, Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)), True{}, Equal.cong(Spec.Bsr, Bool, v => Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, v)), e, y, Equal.sym(Spec.Bsr, y, e, same)), ok)
      +isT = Equal.trans(Bool, b, Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), True{}, Equal.sym(Bool, Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), b, isB), okE)
      %Equal.sym(Spec.Bsr, y, e, same) : {Spec.bsrMember(_, Prune.keepPick(b, e, ks)) == True{} : Bool}
      R.keep_link_head(b, isT, e, ks)
    case Inr{later}:
      R.keep_link_later(b, e, ks, y, searchRest(later))

# A step of the set whose verdict was Keep is kept.
law kept_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  for +ok: {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, y)) == True{} : Bool}
  {Spec.bsrMember(y, Unb.kept(es, fuel, grammar, gm, marks, input)) == True{} : Bool}

def kept_of(es, fuel, grammar, gm, marks, input, y, m, ok):
  match es:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, []) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      kept_of_pick(Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, e)), fuel, grammar, gm, marks, input, e, {==}, rest, Unb.kept(rest, fuel, grammar, gm, marks, input), y, G.ebnf_member_cases(y, e, rest, m), ok,
        later => kept_of(rest, fuel, grammar, gm, marks, input, y, later, ok))

law step_ok_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +e: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +okE: {Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, e) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, y) == True{} : Bool}
  {Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, y) == True{} : Bool}

def step_ok_pick(fuel, grammar, gm, marks, input, s, ks, y, e, rest, cases, okE, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, _) == True{} : Bool}
      okE
    case Inr{later}:
      searchRest(later)

# Every step of the set passed the oracle's checks.
law step_ok_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for all: {Unb.allStepsOk(es, fuel, grammar, gm, marks, input, s, ks) == True{} : Bool}
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  {Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, y) == True{} : Bool}

def step_ok_of(es, fuel, grammar, gm, marks, input, s, ks, y, all, m):
  match es:
    case Nil{}:
      Empty.absurd({Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, y) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      +both = all
      step_ok_pick(fuel, grammar, gm, marks, input, s, ks, y, e, rest, G.ebnf_member_cases(y, e, rest, m),
        Lemma.and_true_left(Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, e), Unb.allStepsOk(rest, fuel, grammar, gm, marks, input, s, ks), both),
        later => step_ok_of(rest, fuel, grammar, gm, marks, input, s, ks, y, Lemma.and_true_right_side(Unb.stepOk(fuel, grammar, gm, marks, input, s, ks, e), Unb.allStepsOk(rest, fuel, grammar, gm, marks, input, s, ks), both), later))

# ======== WHICH CHOICE A STEP COMPLETES ========

law alt_not:
  for item: Maybe<&2, Spec.Item>
  for +index: Nat
  for +rb: +List<Nat>
  for +a: Nat
  for +d: Nat
  for ne: {Nat.is_eq(d, List.length(&2, Spec.Item, Gll.bracketAlt(item, a))) == False{} : Bool}
  {Prefer.altDone(item, index, rb, a, d) == Prefer.NotDone{} : Prefer.Done}

def alt_not(item, index, rb, a, d, ne):
  match item:
    case Some{Spec.Brack{+kind, +alts}}:
      %Equal.sym(Bool, Nat.is_eq(d, List.length(&2, Spec.Item, Spec.altOf(alts, a))), False{}, ne) : {Prefer.doneIf(_, Prefer.DoneAlt{index, rb, a, alts}) == Prefer.NotDone{} : Prefer.Done}
      {==}
    case Some{Spec.Sym{s}}:
      {==}
    case Some{Spec.Eps{}}:
      {==}
    case None{}:
      {==}

# A slot before the end of its sequence completes no choice.
law done_not:
  for +d: Nat
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for ne: {Nat.is_eq(d, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath))) == False{} : Bool}
  {Prefer.doneAt(d <> rpath, grammar, index) == Prefer.NotDone{} : Prefer.Done}

def done_not(d, rpath, grammar, index, ne):
  match rpath:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(d, List.length(&2, Spec.Item, Spec.rhsOf(grammar, index))), False{}, ne) : {Prefer.doneIf(_, Prefer.DoneProd{index}) == Prefer.NotDone{} : Prefer.Done}
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{+a, Con{+m, +outer}}:
      alt_not(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), index, m <> outer, a, d, ne)

# The end of a production's right side completes the production.
law done_prod:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +d: Nat
  for e: {d == List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)) : Nat}
  {Prefer.doneAt([d], grammar, q) == Prefer.DoneProd{q} : Prefer.Done}

def done_prod(grammar, q, d, e):
  +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
  %Equal.sym(Nat, d, n, e) : {Prefer.doneIf(Nat.is_eq(_, n), Prefer.DoneProd{q}) == Prefer.DoneProd{q} : Prefer.Done}
  %Equal.sym(Bool, Nat.is_eq(n, n), True{}, Lemma.nat_eq_refl(n)) : {Prefer.doneIf(_, Prefer.DoneProd{q}) == Prefer.DoneProd{q} : Prefer.Done}
  {==}

law alt_done_brack:
  for item: Maybe<&2, Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {item == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +index: Nat
  for +rb: +List<Nat>
  for +a: Nat
  for +d: Nat
  for e: {d == List.length(&2, Spec.Item, Spec.altOf(alts, a)) : Nat}
  {Prefer.altDone(item, index, rb, a, d) == Prefer.DoneAlt{index, rb, a, alts} : Prefer.Done}

def alt_done_brack(item, kind, alts, itemEq, index, rb, a, d, e):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  %Equal.sym(Maybe<&2, Spec.Item>, item, Some{Spec.Brack{kind, alts}}, itemEq) : {Prefer.altDone(_, index, rb, a, d) == Prefer.DoneAlt{index, rb, a, alts} : Prefer.Done}
  %Equal.sym(Nat, d, n, e) : {Prefer.doneIf(Nat.is_eq(_, n), Prefer.DoneAlt{index, rb, a, alts}) == Prefer.DoneAlt{index, rb, a, alts} : Prefer.Done}
  %Equal.sym(Bool, Nat.is_eq(n, n), True{}, Lemma.nat_eq_refl(n)) : {Prefer.doneIf(_, Prefer.DoneAlt{index, rb, a, alts}) == Prefer.DoneAlt{index, rb, a, alts} : Prefer.Done}
  {==}

# The end of alternative a of the bracket at item m completes that alternative.
law done_alt:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rp: +List<Nat>
  for +m: Nat
  for +a: Nat
  for +d: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rp), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for e: {d == List.length(&2, Spec.Item, Spec.altOf(alts, a)) : Nat}
  {Prefer.doneAt(d <> a <> m <> rp, grammar, index) == Prefer.DoneAlt{index, m <> rp, a, alts} : Prefer.Done}

def done_alt(grammar, index, rp, m, a, d, kind, alts, itemEq, e):
  alt_done_brack(Gll.nthItem(Gll.seqAt(grammar, index, rp), m), kind, alts, itemEq, index, m <> rp, a, d, e)

# ======== WHAT A VERDICT SAYS ========

def isRemove(v: Prefer.Verdict) -> Bool:
  match v:
    case Prefer.Keep{}:
      False{}
    case Prefer.Remove{who}:
      True{}
    case Prefer.Unsure{}:
      False{}

def isUnsure(v: Prefer.Verdict) -> Bool:
  match v:
    case Prefer.Keep{}:
      False{}
    case Prefer.Remove{who}:
      False{}
    case Prefer.Unsure{}:
      True{}

def whoOr(v: Prefer.Verdict) -> Nat:
  match v:
    case Prefer.Keep{}:
      0n
    case Prefer.Remove{+who}:
      who
    case Prefer.Unsure{}:
      0n

law verdict_keep_parts:
  for found: Maybe<&2, Bool>
  for +who: Nat
  for +next: Prefer.Verdict
  for e: {Prefer.verdictIf(found, who, next) == Prefer.Keep{} : Prefer.Verdict}
  {found == Some{False{}} : Maybe<&2, Bool>} & {next == Prefer.Keep{} : Prefer.Verdict}

def verdict_keep_parts(found, who, next, e):
  match found:
    case Some{b}:
      match b:
        case True{}:
          Empty.absurd({Some{True{}} == Some{False{}} : Maybe<&2, Bool>} & {next == Prefer.Keep{} : Prefer.Verdict}, Lemma.true_is_not_false(Equal.cong(Prefer.Verdict, Bool, v => isRemove(v), Prefer.Remove{who}, Prefer.Keep{}, e)))
        case False{}:
          ({==}, e)
    case None{}:
      Empty.absurd({None{} == Some{False{}} : Maybe<&2, Bool>} & {next == Prefer.Keep{} : Prefer.Verdict}, Lemma.true_is_not_false(Equal.cong(Prefer.Verdict, Bool, v => isUnsure(v), Prefer.Unsure{}, Prefer.Keep{}, e)))

law verdict_remove_parts:
  for found: Maybe<&2, Bool>
  for +p: Nat
  for +next: Prefer.Verdict
  for +who: Nat
  for e: {Prefer.verdictIf(found, p, next) == Prefer.Remove{who} : Prefer.Verdict}
  Either<({found == Some{True{}} : Maybe<&2, Bool>} & {p == who : Nat}), {next == Prefer.Remove{who} : Prefer.Verdict}>

def verdict_remove_parts(found, p, next, who, e):
  match found:
    case Some{b}:
      match b:
        case True{}:
          Inl{({==}, Equal.cong(Prefer.Verdict, Nat, v => whoOr(v), Prefer.Remove{p}, Prefer.Remove{who}, e))}
        case False{}:
          Inr{e}
    case None{}:
      Empty.absurd(Either<({None{} == Some{True{}} : Maybe<&2, Bool>} & {p == who : Nat}), {next == Prefer.Remove{who} : Prefer.Verdict}>, Lemma.true_is_not_false(Equal.cong(Prefer.Verdict, Bool, v => isUnsure(v), Prefer.Unsure{}, Prefer.Remove{who}, e)))

law derives_if_true:
  for cand: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +items: +List<Spec.Item>
  for +idx: Nat
  for +pre: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +j: Nat
  for e: {Unb.derivesIf(cand, fuel, grammar, gm, items, idx, pre, input, k, j) == Some{True{}} : Maybe<&2, Bool>}
  {cand == True{} : Bool}

def derives_if_true(cand, fuel, grammar, gm, items, idx, pre, input, k, j, e):
  match cand:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Bool>, Bool, v => Sub.boolOr(v), Some{False{}}, Some{True{}}, e)))

law lt_succ_self:
  for p: Nat
  {Nat.is_lt(p, 1n+p) == True{} : Bool}

def lt_succ_self(p):
  match p:
    case 0n:
      {==}
    case 1n+q:
      lt_succ_self(q)

law lt_succ_right:
  for a: Nat
  for b: Nat
  for e: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, 1n+b) == True{} : Bool}

def lt_succ_right(a, b, e):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 1n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case 1n+p 1n+q:
      lt_succ_right(p, q, e)

# ---- Productions ----

law prod_keep_at:
  for b: Bool
  for +p: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +k: Nat
  for +j: Nat
  for +m: Nat
  for +isB: {Nat.is_eq(p, m) == b : Bool}
  for +lt: {Nat.is_lt(m, 1n+p) == True{} : Bool}
  for +cand: {Prefer.prodCand(grammar, marks, x, q, m) == True{} : Bool}
  for parts: {Unb.derivesIf(Prefer.prodCand(grammar, marks, x, q, p), fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>} & {Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Keep{} : Prefer.Verdict}
  for ih: {Nat.is_lt(m, p) == True{} : Bool} -> {Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Keep{} : Prefer.Verdict} -> {Unb.derivesAdm(fuel, grammar, gm, Spec.rhsOf(grammar, m), m, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}
  {Unb.derivesAdm(fuel, grammar, gm, Spec.rhsOf(grammar, m), m, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}

def prod_keep_at(b, p, fuel, grammar, gm, marks, input, x, q, k, j, m, isB, lt, cand, parts, ih):
  match b:
    case True{}:
      match parts:
        case (found, rest):
          +mEq = Lemma.nat_eq_sound(p, m, isB)
          +candP = Equal.trans(Bool, Prefer.prodCand(grammar, marks, x, q, p), Prefer.prodCand(grammar, marks, x, q, m), True{}, Equal.cong(Nat, Bool, v => Prefer.prodCand(grammar, marks, x, q, v), p, m, mEq), cand)
          %mEq : {Unb.derivesAdm(fuel, grammar, gm, Spec.rhsOf(grammar, _), _, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}
          %candP : {Unb.derivesIf(_, fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}
          found
    case False{}:
      match parts:
        case (found, rest):
          ih(Lemma.lt_succ_ne(m, p, lt, isB), rest)

# A Keep on a production: no candidate below n derives the tokens.
law prod_keep:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +k: Nat
  for +j: Nat
  for keep: {Unb.prodVerdict(n, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Keep{} : Prefer.Verdict}
  for +m: Nat
  for +lt: {Nat.is_lt(m, n) == True{} : Bool}
  for +cand: {Prefer.prodCand(grammar, marks, x, q, m) == True{} : Bool}
  {Unb.derivesAdm(fuel, grammar, gm, Spec.rhsOf(grammar, m), m, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}

def prod_keep(n, fuel, grammar, gm, marks, input, x, q, k, j, keep, m, lt, cand):
  match n:
    case 0n:
      Empty.absurd({Unb.derivesAdm(fuel, grammar, gm, Spec.rhsOf(grammar, m), m, [], input, k, j) == Some{False{}} : Maybe<&2, Bool>}, Lemma.lt_zero_false(m, lt))
    case 1n+(+p):
      prod_keep_at(Nat.is_eq(p, m), p, fuel, grammar, gm, marks, input, x, q, k, j, m, {==}, lt, cand,
        verdict_keep_parts(Unb.derivesIf(Prefer.prodCand(grammar, marks, x, q, p), fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j), p, Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j), keep),
        lt2 => keep2 => prod_keep(p, fuel, grammar, gm, marks, input, x, q, k, j, keep2, m, lt2, cand))

law prod_remove_at:
  for +p: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +k: Nat
  for +j: Nat
  for +who: Nat
  for cases: Either<({Unb.derivesIf(Prefer.prodCand(grammar, marks, x, q, p), fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j) == Some{True{}} : Maybe<&2, Bool>} & {p == who : Nat}), {Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Remove{who} : Prefer.Verdict}>
  for ih: {Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Remove{who} : Prefer.Verdict} -> {Prefer.prodCand(grammar, marks, x, q, who) == True{} : Bool}
  {Prefer.prodCand(grammar, marks, x, q, who) == True{} : Bool}

def prod_remove_at(p, fuel, grammar, gm, marks, input, x, q, k, j, who, cases, ih):
  match cases:
    case Inl{pair}:
      match pair:
        case (found, pw):
          %pw : {Prefer.prodCand(grammar, marks, x, q, _) == True{} : Bool}
          derives_if_true(Prefer.prodCand(grammar, marks, x, q, p), fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j, found)
    case Inr{later}:
      ih(later)

# A Remove on a production names a candidate.
law prod_remove:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +k: Nat
  for +j: Nat
  for +who: Nat
  for e: {Unb.prodVerdict(n, fuel, grammar, gm, marks, input, x, q, k, j) == Prefer.Remove{who} : Prefer.Verdict}
  {Prefer.prodCand(grammar, marks, x, q, who) == True{} : Bool}

def prod_remove(n, fuel, grammar, gm, marks, input, x, q, k, j, who, e):
  match n:
    case 0n:
      Empty.absurd({Prefer.prodCand(grammar, marks, x, q, who) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Prefer.Verdict, Bool, v => isRemove(v), Prefer.Keep{}, Prefer.Remove{who}, e)))
    case 1n+(+p):
      prod_remove_at(p, fuel, grammar, gm, marks, input, x, q, k, j, who,
        verdict_remove_parts(Unb.derivesIf(Prefer.prodCand(grammar, marks, x, q, p), fuel, grammar, gm, Spec.rhsOf(grammar, p), p, [], input, k, j), p, Unb.prodVerdict(p, fuel, grammar, gm, marks, input, x, q, k, j), who, e),
        later => prod_remove(p, fuel, grammar, gm, marks, input, x, q, k, j, who, later))

# ---- Alternatives ----

law alt_keep_at:
  for b: Bool
  for +p: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +k: Nat
  for +j: Nat
  for +m: Nat
  for +isB: {Nat.is_eq(p, m) == b : Bool}
  for +lt: {Nat.is_lt(m, 1n+p) == True{} : Bool}
  for +cand: {Prefer.altCand(marks, index, path, a, m) == True{} : Bool}
  for parts: {Unb.derivesIf(Prefer.altCand(marks, index, path, a, p), fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j) == Some{False{}} : Maybe<&2, Bool>} & {Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Keep{} : Prefer.Verdict}
  for ih: {Nat.is_lt(m, p) == True{} : Bool} -> {Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Keep{} : Prefer.Verdict} -> {Unb.derivesAdm(fuel, grammar, gm, Spec.altOf(alts, m), index, List.append(&2, Nat, path, [m]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}
  {Unb.derivesAdm(fuel, grammar, gm, Spec.altOf(alts, m), index, List.append(&2, Nat, path, [m]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}

def alt_keep_at(b, p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, m, isB, lt, cand, parts, ih):
  match b:
    case True{}:
      match parts:
        case (found, rest):
          +mEq = Lemma.nat_eq_sound(p, m, isB)
          +candP = Equal.trans(Bool, Prefer.altCand(marks, index, path, a, p), Prefer.altCand(marks, index, path, a, m), True{}, Equal.cong(Nat, Bool, v => Prefer.altCand(marks, index, path, a, v), p, m, mEq), cand)
          %mEq : {Unb.derivesAdm(fuel, grammar, gm, Spec.altOf(alts, _), index, List.append(&2, Nat, path, [_]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}
          %candP : {Unb.derivesIf(_, fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}
          found
    case False{}:
      match parts:
        case (found, rest):
          ih(Lemma.lt_succ_ne(m, p, lt, isB), rest)

# A Keep on an alternative: no candidate below n derives the tokens.
law alt_keep:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +k: Nat
  for +j: Nat
  for keep: {Unb.altVerdict(n, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Keep{} : Prefer.Verdict}
  for +m: Nat
  for +lt: {Nat.is_lt(m, n) == True{} : Bool}
  for +cand: {Prefer.altCand(marks, index, path, a, m) == True{} : Bool}
  {Unb.derivesAdm(fuel, grammar, gm, Spec.altOf(alts, m), index, List.append(&2, Nat, path, [m]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}

def alt_keep(n, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, keep, m, lt, cand):
  match n:
    case 0n:
      Empty.absurd({Unb.derivesAdm(fuel, grammar, gm, Spec.altOf(alts, m), index, List.append(&2, Nat, path, [m]), input, k, j) == Some{False{}} : Maybe<&2, Bool>}, Lemma.lt_zero_false(m, lt))
    case 1n+(+p):
      alt_keep_at(Nat.is_eq(p, m), p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, m, {==}, lt, cand,
        verdict_keep_parts(Unb.derivesIf(Prefer.altCand(marks, index, path, a, p), fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j), p, Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j), keep),
        lt2 => keep2 => alt_keep(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, keep2, m, lt2, cand))

law alt_lift:
  for +marks: +List<Spec.Mark>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +who: Nat
  for +p: Nat
  for pair: {Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, p) == True{} : Bool}
  {Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, 1n+p) == True{} : Bool}

def alt_lift(marks, index, path, a, who, p, pair):
  match pair:
    case (c, lt):
      (c, lt_succ_right(who, p, lt))

law alt_remove_at:
  for +p: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +k: Nat
  for +j: Nat
  for +who: Nat
  for cases: Either<({Unb.derivesIf(Prefer.altCand(marks, index, path, a, p), fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j) == Some{True{}} : Maybe<&2, Bool>} & {p == who : Nat}), {Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Remove{who} : Prefer.Verdict}>
  for ih: {Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Remove{who} : Prefer.Verdict} -> ({Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, p) == True{} : Bool})
  {Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, 1n+p) == True{} : Bool}

def alt_remove_at(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, who, cases, ih):
  match cases:
    case Inl{pair}:
      match pair:
        case (found, pw):
          %pw : {Prefer.altCand(marks, index, path, a, _) == True{} : Bool} & {Nat.is_lt(_, 1n+p) == True{} : Bool}
          (derives_if_true(Prefer.altCand(marks, index, path, a, p), fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j, found), lt_succ_self(p))
    case Inr{later}:
      alt_lift(marks, index, path, a, who, p, ih(later))

# A Remove on an alternative names a candidate, one of the bracket's alternatives.
law alt_remove:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +k: Nat
  for +j: Nat
  for +who: Nat
  for e: {Unb.altVerdict(n, fuel, grammar, gm, marks, input, alts, index, path, a, k, j) == Prefer.Remove{who} : Prefer.Verdict}
  {Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, n) == True{} : Bool}

def alt_remove(n, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, who, e):
  match n:
    case 0n:
      Empty.absurd({Prefer.altCand(marks, index, path, a, who) == True{} : Bool} & {Nat.is_lt(who, 0n) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(Prefer.Verdict, Bool, v => isRemove(v), Prefer.Keep{}, Prefer.Remove{who}, e)))
    case 1n+(+p):
      alt_remove_at(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, who,
        verdict_remove_parts(Unb.derivesIf(Prefer.altCand(marks, index, path, a, p), fuel, grammar, gm, Spec.altOf(alts, p), index, List.append(&2, Nat, path, [p]), input, k, j), p, Unb.altVerdict(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j), who, e),
        later => alt_remove(p, fuel, grammar, gm, marks, input, alts, index, path, a, k, j, who, later))

# ======== A NO FROM THE SUB-PARSE LEAVES NO RIVAL ========

law spec_lhs_of_is:
  for +grammar: +List<Spec.Production>
  for p: Nat
  for +a: Nat
  for e: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  {Spec.lhsOf(grammar, p) == a : Nat}

def spec_lhs_of_is(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, rhs}, rest} 0n:
      Lemma.nat_eq_sound(lhs, a, e)
    case Con{Spec.Production{pl, pr}, +rest} 1n+q:
      spec_lhs_of_is(rest, q, a, e)

law lhs_is_lt:
  for +grammar: +List<Spec.Production>
  for p: Nat
  for +a: Nat
  for e: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  {Nat.is_lt(p, List.length(&2, Spec.Production, grammar)) == True{} : Bool}

def lhs_is_lt(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{lhs, rhs}, +rest} 0n:
      {==}
    case Con{Spec.Production{pl, pr}, +rest} 1n+q:
      lhs_is_lt(rest, q, a, e)

# ======== A KEPT NODE HAS NO RIVAL ========

law keep_of_is_keep:
  for v: Prefer.Verdict
  for e: {Prefer.isKeep(v) == True{} : Bool}
  {v == Prefer.Keep{} : Prefer.Verdict}

def keep_of_is_keep(v, e):
  match v:
    case Prefer.Keep{}:
      {==}
    case Prefer.Remove{who}:
      Empty.absurd({Prefer.Remove{who} == Prefer.Keep{} : Prefer.Verdict}, Lemma.false_is_not_true(e))
    case Prefer.Unsure{}:
      Empty.absurd({Prefer.Unsure{} == Prefer.Keep{} : Prefer.Verdict}, Lemma.false_is_not_true(e))

law no_prod_rival:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +keep: {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for rival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs)
  Empty

def no_prod_rival(fuel, grammar, gm, marks, input, x, q, ch, k, sp, lhsQ, keep, xs, after, pos, rival):
  match rival:
    case (q20, (cond0, (f0, (fit0, (lv0, (clean, (holds0, adm0))))))):
      +q2 = {q20 : Nat}
      +cond = {cond0 : {Bool.and(Spec.lhsIs(grammar, q2, x), Spec.outranks(Spec.prodRank(marks, q2), Spec.prodRank(marks, q))) == True{} : Bool}}
      +f = {f0 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(f, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}}
      +lv = {lv0 : {Spec.leaves(f) == Spec.leaves(ch) : +List<Nat>}}
      +lhsX = spec_lhs_of_is(grammar, q, x, lhsQ)
      +cand = Equal.trans(Bool, Prefer.prodCand(grammar, marks, Spec.lhsOf(grammar, q), q, q2), Prefer.prodCand(grammar, marks, x, q, q2), True{}, Equal.cong(Nat, Bool, v => Prefer.prodCand(grammar, marks, v, q, q2), Spec.lhsOf(grammar, q), x, lhsX), cond)
      +lt = lhs_is_lt(grammar, q2, x, Lemma.and_true_left(Spec.lhsIs(grammar, q2, x), Spec.outranks(Spec.prodRank(marks, q2), Spec.prodRank(marks, q)), cond))
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +dh = prod_keep(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end, keep, q2, lt, cand)
      +eqA = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f), Spec.leaves(ch), lv)
      +posF = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, Spec.leaves(ch), after), Lemma.dropN(k, input), eqA, pos)
      holdsF = PG.hold_back(grammar, Spec.prodGuards(gm, q2), Spec.rhsOf(grammar, q2), f, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, Spec.leaves(ch), after), eqA, holds0)
      Sup.adm_refutes(fuel, grammar, gm, PG.OProd{}, q2, [], {==}, {==}, {==}, input, k, Spec.leaves(ch), sp, f, fit, lv, after, posF, holdsF, adm0, dh)

law no_alt_rival:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +keep: {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, path, a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}
  for +xs: +List<Nat>
  for +r0: +List<Nat>
  for +dotB: Nat
  for +kind: Spec.Bracket
  for +facts: {Gll.nthItem(Gll.seqAt(grammar, index, r0), dotB) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +pathEq: {path == Gll.reverseOnto(dotB <> r0, []) : +List<Nat>}
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for rival: Spec.AltRival(grammar, gm, marks, alts, index, path, a, Spec.leaves(ch), after, xs)
  Empty

def no_alt_rival(fuel, grammar, gm, marks, input, alts, index, path, a, ch, k, sp, keep, xs, r0, dotB, kind, facts, pathEq, after, pos, rival):
  match rival:
    case (a20, (cond0, (f0, (fit0, (lv0, (clean, (holds0, adm0))))))):
      +a2 = {a20 : Nat}
      +cond = {cond0 : {Bool.and(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a))) == True{} : Bool}}
      +f = {f0 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(f, grammar, Spec.altOf(alts, a2)) == True{} : Bool}}
      +lv = {lv0 : {Spec.leaves(f) == Spec.leaves(ch) : +List<Nat>}}
      +lt = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a)), cond)
      +cand = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a)), cond)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +dh = alt_keep(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, path, a, k, end, keep, a2, lt, cand)
      +pre = List.append(&2, Nat, path, [a2])
      +pEqO = G.prefix_ext(dotB <> r0, path, [a2], pathEq)
      +remO = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a2), Gll.nthItem(Gll.seqAt(grammar, index, r0), dotB), Some{Spec.Brack{kind, alts}}, facts)
      +eqA = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f), Spec.leaves(ch), lv)
      +posF = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, Spec.leaves(ch), after), Lemma.dropN(k, input), eqA, pos)
      +p2 = Gll.reverseOnto(dotB <> r0, [])
      holds1 = PG.guards_path_back(grammar, gm, index, path, p2, pathEq, a2, Spec.altOf(alts, a2), f, List.append(&2, Nat, Spec.leaves(ch), after), holds0)
      holdsF = PG.hold_back(grammar, Spec.altGuards(gm, index, p2, a2), Spec.altOf(alts, a2), f, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, Spec.leaves(ch), after), eqA, holds1)
      Sup.adm_refutes(fuel, grammar, gm, PG.OAlt{r0, dotB, a2, kind, alts}, index, pre, pEqO, facts, remO, input, k, Spec.leaves(ch), sp, f, fit, lv, after, posF, holdsF, adm0, dh)

# ======== A KEPT COMPLETION WAS KEPT BY A KEEP ========

law node_keep_last:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +fit: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for last: Sub.LastIn(ch, q, [], 0n, k, k)
  {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}

def node_keep_last(fuel, grammar, gm, marks, input, s, q, ch, k, fit, allK, last):
  match last:
    case (piv0, m):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +y = Spec.at(q, [], n, k, piv, end)
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +mK = G.ebnf_all_in_member(Spec.walk(ch, False{}, q, [], 0n, k, k), kept, y, allK, m)
      +ik = kept_keep(s, fuel, grammar, gm, marks, input, y, mK)
      +dp = done_prod(grammar, q, n, Fits.fits_count(ch, grammar, Spec.rhsOf(grammar, q), fit))
      +ik2 = Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.DoneProd{q}, fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(Unb.verdictFor(Prefer.doneAt([n], grammar, q), fuel, grammar, gm, marks, input, k, end)), True{}, Equal.cong(Prefer.Done, Bool, v => Prefer.isKeep(Unb.verdictFor(v, fuel, grammar, gm, marks, input, k, end)), Prefer.DoneProd{q}, Prefer.doneAt([n], grammar, q), Equal.sym(Prefer.Done, Prefer.doneAt([n], grammar, q), Prefer.DoneProd{q}, dp)), ik)
      keep_of_is_keep(Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end), ik2)

# The completion of a node in a tree of kept steps was kept by a Keep.
law node_keep:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +fit: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}

def node_keep(fuel, grammar, gm, marks, input, s, q, ch, k, fit, allK):
  node_keep_last(fuel, grammar, gm, marks, input, s, q, ch, k, fit, allK, Sub.last_any(ch, q, [], k, k))

law pick_keep_last:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +fit: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for last: Sub.LastIn(ch, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
  {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, List.append(&2, Nat, prefix, [dot]), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}

def pick_keep_last(fuel, grammar, gm, marks, input, s, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, fit, allK, last):
  match last:
    case (piv0, m):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pre = List.append(&2, Nat, prefix, [dot, a])
      +y = Spec.at(index, pre, n, k, piv, end)
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +mK = G.ebnf_all_in_member(Spec.walk(ch, False{}, index, pre, 0n, k, k), kept, y, allK, m)
      +ik = kept_keep(s, fuel, grammar, gm, marks, input, y, mK)
      +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
      +revEq = R.step_rev(a <> dot <> rpath, pre, n, G.prefix_ext(rpath, prefix, [dot, a], pEq))
      +da = done_alt(grammar, index, rpath, dot, a, n, kind, alts, itemEq, Fits.fits_count(ch, grammar, Spec.altOf(alts, a), fit))
      +done = {Prefer.DoneAlt{index, dot <> rpath, a, alts} : Prefer.Done}
      +dEq = Equal.trans(Prefer.Done, Prefer.doneAt(rev, grammar, index), Prefer.doneAt(n <> a <> dot <> rpath, grammar, index), done, Equal.cong(+List<Nat>, Prefer.Done, v => Prefer.doneAt(v, grammar, index), rev, n <> a <> dot <> rpath, revEq), da)
      +ik2 = Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(done, fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(Unb.verdictFor(Prefer.doneAt(rev, grammar, index), fuel, grammar, gm, marks, input, k, end)), True{}, Equal.cong(Prefer.Done, Bool, v => Prefer.isKeep(Unb.verdictFor(v, fuel, grammar, gm, marks, input, k, end)), done, Prefer.doneAt(rev, grammar, index), Equal.sym(Prefer.Done, Prefer.doneAt(rev, grammar, index), done, dEq)), ik)
      +path = List.append(&2, Nat, prefix, [dot])
      +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
      +nAlts = List.length(&2, +List<Spec.Item>, alts)
      +ik3 = Equal.trans(Bool, Prefer.isKeep(Unb.altVerdict(nAlts, fuel, grammar, gm, marks, input, alts, index, path, a, k, end)), Prefer.isKeep(Unb.altVerdict(nAlts, fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(rpath, [dot]), a, k, end)), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.isKeep(Unb.altVerdict(nAlts, fuel, grammar, gm, marks, input, alts, index, v, a, k, end)), path, Gll.reverseOnto(rpath, [dot]), pathEq), ik2)
      keep_of_is_keep(Unb.altVerdict(nAlts, fuel, grammar, gm, marks, input, alts, index, path, a, k, end), ik3)

# The completion of a pick in a tree of kept steps was kept by a Keep.
law pick_keep:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +fit: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, List.append(&2, Nat, prefix, [dot]), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == Prefer.Keep{} : Prefer.Verdict}

def pick_keep(fuel, grammar, gm, marks, input, s, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, fit, allK):
  pick_keep_last(fuel, grammar, gm, marks, input, s, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, fit, allK, Sub.last_any(ch, index, List.append(&2, Nat, prefix, [dot, a]), k, k))

# ======== THE ROUNDS OF A LOOP HAVE ONE ALTERNATIVE ========

law one_group_len:
  for alts: +List<+List<Spec.Item>>
  for e: {Prefer.oneGroup(alts) == True{} : Bool}
  {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}

def one_group_len(alts, e):
  match alts:
    case Nil{}:
      Empty.absurd({0n == 1n : Nat}, Lemma.false_is_not_true(e))
    case Con{alt, rest}:
      match alt:
        case Nil{}:
          Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
        case Con{it, more}:
          match it:
            case Spec.Sym{sy}:
              Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
            case Spec.Eps{}:
              Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
            case Spec.Brack{kind, galts}:
              match kind:
                case Spec.Group{}:
                  match more:
                    case Nil{}:
                      match rest:
                        case Nil{}:
                          {==}
                        case Con{r, rs}:
                          Empty.absurd({1n+1n+List.length(&2, +List<Spec.Item>, rs) == 1n : Nat}, Lemma.false_is_not_true(e))
                    case Con{m2, ms}:
                      Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
                case Spec.Optional{}:
                  Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
                case Spec.Closure{}:
                  Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))
                case Spec.Positive{}:
                  Empty.absurd({1n+List.length(&2, +List<Spec.Item>, rest) == 1n : Nat}, Lemma.false_is_not_true(e))

law one_alt_zero:
  for +alts: +List<+List<Spec.Item>>
  for +one: {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}
  for +a: Nat
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  {a == 0n : Nat}

def one_alt_zero(alts, one, a, isA):
  lt_one_zero(a, Equal.trans(Bool, Nat.is_lt(a, 1n), Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(a, v), 1n, List.length(&2, +List<Spec.Item>, alts), Equal.sym(Nat, List.length(&2, +List<Spec.Item>, alts), 1n, one)), isA))

# A round has no rival: its loop has one alternative.
law no_round_rival:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +one: {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +w: +List<Nat>
  for +after: +List<Nat>
  for +xs: +List<Nat>
  for rival: Spec.AltRival(grammar, gm, marks, alts, index, path, a, w, after, xs)
  Empty

def no_round_rival(grammar, gm, marks, alts, one, index, path, a, isA, w, after, xs, rival):
  match rival:
    case (a20, (cond0, der)):
      +a2 = {a20 : Nat}
      +cond = {cond0 : {Bool.and(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a))) == True{} : Bool}}
      +z2 = one_alt_zero(alts, one, a2, Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a)), cond))
      +z = one_alt_zero(alts, one, a, isA)
      +up = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a)), cond)
      +same = Equal.trans(Nat, a2, 0n, a, z2, Equal.sym(Nat, a, 0n, z))
      +up2 = Equal.trans(Bool, Spec.outranks(Spec.altRank(marks, index, path, a), Spec.altRank(marks, index, path, a)), Spec.outranks(Spec.altRank(marks, index, path, a2), Spec.altRank(marks, index, path, a)), True{}, Equal.cong(Nat, Bool, v => Spec.outranks(Spec.altRank(marks, index, path, v), Spec.altRank(marks, index, path, a)), a, a2, Equal.sym(Nat, a2, a, same)), up)
      Lemma.true_is_not_false(Equal.trans(Bool, True{}, Spec.outranks(Spec.altRank(marks, index, path, a), Spec.altRank(marks, index, path, a)), False{}, Equal.sym(Bool, Spec.outranks(Spec.altRank(marks, index, path, a), Spec.altRank(marks, index, path, a)), True{}, up2), outranks_self(Spec.altRank(marks, index, path, a))))

law loop_ok_group:
  for kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for isL: {Gll.isLoop(kind) == True{} : Bool}
  for gr: {Prefer.loopOk(Some{Spec.Brack{kind, alts}}) == True{} : Bool}
  {Prefer.oneGroup(alts) == True{} : Bool}

def loop_ok_group(kind, alts, isL, gr):
  match kind:
    case Spec.Group{}:
      Empty.absurd({Prefer.oneGroup(alts) == True{} : Bool}, Lemma.false_is_not_true(isL))
    case Spec.Optional{}:
      Empty.absurd({Prefer.oneGroup(alts) == True{} : Bool}, Lemma.false_is_not_true(isL))
    case Spec.Closure{}:
      gr
    case Spec.Positive{}:
      gr

law round_group_last:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for last: Sub.LastIn(ch, index, List.append(&2, Nat, prefix, [a]), 0n, i, k)
  {Prefer.oneGroup(alts) == True{} : Bool}

def round_group_last(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, allK, last):
  match last:
    case (piv0, mem):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pre = List.append(&2, Nat, prefix, [a])
      +y = Spec.at(index, pre, n, i, piv, end)
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +mK = G.ebnf_all_in_member(Spec.walk(ch, False{}, index, pre, 0n, i, k), kept, y, allK, mem)
      +mS = kept_sub(s, fuel, grammar, gm, marks, input, y, mK)
      +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
      +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
      +d = Prefer.doneAt(rev, grammar, index)
      +gr = Lemma.and_true_left(Prefer.groupedAt(rev, grammar, index), Prefer.verdictOk(Unb.verdictFor(d, fuel, grammar, gm, marks, input, i, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d, i, end), ok)
      +revEq = R.step_rev(a <> m <> outer, pre, n, G.prefix_ext(m <> outer, prefix, [a], pEq))
      +gr2 = Equal.trans(Bool, Prefer.groupedAt(n <> a <> m <> outer, grammar, index), Prefer.groupedAt(rev, grammar, index), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.groupedAt(v, grammar, index), n <> a <> m <> outer, rev, Equal.sym(+List<Nat>, rev, n <> a <> m <> outer, revEq)), gr)
      +gr3 = Equal.trans(Bool, Prefer.loopOk(Some{Spec.Brack{kind, alts}}), Prefer.loopOk(G.loopItem(grammar, index, m <> outer)), True{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Prefer.loopOk(v), Some{Spec.Brack{kind, alts}}, G.loopItem(grammar, index, m <> outer), Equal.sym(Maybe<&2, Spec.Item>, G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)), gr2)
      loop_ok_group(kind, alts, isL, gr3)

# A loop with a round of kept steps is written { ( τ ) }: the oracle checked it.
law round_group:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  for +allK: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}

def round_group(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, allK):
  one_group_len(alts, round_group_last(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, allK, Sub.last_any(ch, index, List.append(&2, Nat, prefix, [a]), i, k)))

# ======== A TREE OF KEPT STEPS IS UNBEATEN ========

# What the walk needs: in a sequence, the forest fits the items from the dot on, and
# its steps are kept; in the rounds of a loop, the loop's bracket and that each round
# fits it, and the steps are kept.
def SurvReady(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def SurvDone(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match rounds:
    case False{}:
      Spec.Unbeaten(grammar, gm, marks, forest, items, index, prefix, dot, above, span, after)
    case True{}:
      Spec.RoundsUnbeaten(grammar, gm, marks, forest, alts, index, prefix, above, span, after)

def SurvIH(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @above: +List<Nat> -> @span: +List<Nat> -> @after: +List<Nat> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> G.Spells(forest, input, k) -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> SurvReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts) -> SurvDone(rounds, grammar, gm, marks, forest, items, index, prefix, dot, alts, above, span, after)

law surv_nil:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  Spec.Unbeaten(grammar, gm, marks, [], items, index, prefix, dot, above, span, after)

def surv_nil(items, grammar, gm, marks, index, prefix, dot, above, span, after):
  match items:
    case Nil{}:
      Unit{}
    case Con{it, rest}:
      Unit{}

law surv_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SurvIH(grammar, gm, marks, input, fuel, s, ch)
  for ihTs: SurvIH(grammar, gm, marks, input, fuel, s, ts)
  SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after)

def surv_node(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, q, ch, ts, pEq, sp, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
          +keep = node_keep(fuel, grammar, gm, marks, input, s, q, ch, k, fitCh, allCh)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +xs = {x <> Spec.sameAbove(above, span, w) : +List<Nat>}
          (r => no_prod_rival(fuel, grammar, gm, marks, input, x, q, ch, k, spCh, lhsQ, keep, xs, next, posCh, r),
            (ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, xs, w, next, {==}, spCh, posCh, ({==}, (fitCh, allCh))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, pEq, spTs, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law surv_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SurvIH(grammar, gm, marks, input, fuel, s, ch)
  for ihTs: SurvIH(grammar, gm, marks, input, fuel, s, ts)
  SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after)

def surv_pick(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, a, ch, ts, pEq, sp, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +keep = pick_keep(fuel, grammar, gm, marks, input, s, index, rpath, prefix, pEq, dot, a, Spec.Group{}, balts, itemEq, ch, k, fitCh, allCh)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, G.prefix_ext(rpath, prefix, [dot, a], pEq))
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
          +same = Spec.sameAbove(above, span, w)
          +xs = {Spec.lhsOf(grammar, index) <> same : +List<Nat>}
          (r => no_alt_rival(fuel, grammar, gm, marks, input, balts, index, path, a, ch, k, spCh, keep, xs, rpath, dot, Spec.Group{}, itemEq, G.prefix_ext(rpath, prefix, [dot], pEq), next, posCh, r),
            (ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, same, w, next, pEq2, spCh, posCh, (itemsEq2, (fitCh, allCh2))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, pEq, spTs, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +keep = pick_keep(fuel, grammar, gm, marks, input, s, index, rpath, prefix, pEq, dot, a, Spec.Optional{}, balts, itemEq, ch, k, fitCh, allCh)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, G.prefix_ext(rpath, prefix, [dot, a], pEq))
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
          +same = Spec.sameAbove(above, span, w)
          +xs = {Spec.lhsOf(grammar, index) <> same : +List<Nat>}
          (r => no_alt_rival(fuel, grammar, gm, marks, input, balts, index, path, a, ch, k, spCh, keep, xs, rpath, dot, Spec.Optional{}, itemEq, G.prefix_ext(rpath, prefix, [dot], pEq), next, posCh, r),
            (ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, same, w, next, pEq2, spCh, posCh, (itemsEq2, (fitCh, allCh2))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, pEq, spTs, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law surv_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Leaf{k0} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: SurvIH(grammar, gm, marks, input, fuel, s, ts)
  SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after)

def surv_leaf(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, k0, ts, pEq, sp, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), Unb.kept(s, fuel, grammar, gm, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, above, span, after, pEq, G.leaf_rest(input, k, k0, Spec.leaves(ts), sp), PG.pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law surv_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Skip{} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Skip{} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: SurvIH(grammar, gm, marks, input, fuel, s, ts)
  SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after)

def surv_skip(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, ts, pEq, sp, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, above, span, after, pEq, sp, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, above, span, after, pEq, sp, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))

law surv_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihRs: SurvIH(grammar, gm, marks, input, fuel, s, rs)
  for ihTs: SurvIH(grammar, gm, marks, input, fuel, s, ts)
  SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after)

def surv_loop(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, rs, ts, pEq, sp, pos, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wRs, wTs), kept, allW)
          +allRs = R.in_app_left(wRs, wTs, kept, allIn2)
          +allTs = R.in_app_right(wRs, wTs, kept, allIn2)
          +spRs = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, above, span, next, pEqL, spRs, posRs, (itemEq, ({==}, (fitRs, allRs)))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, pEq, spTs, posTs, (restEq, (fitTs, allTs))))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wRs, wTs), kept, allW)
          +allRs = R.in_app_left(wRs, wTs, kept, allIn2)
          +allTs = R.in_app_right(wRs, wTs, kept, allIn2)
          +spRs = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, above, span, next, pEqL, spRs, posRs, (itemEq, ({==}, (fitRs, allRs)))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, pEq, spTs, posTs, (restEq, (fitTs, allTs))))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(SurvDone(False{}, grammar, gm, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law surv_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(True{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: SurvIH(grammar, gm, marks, input, fuel, s, ch)
  for ihRest: SurvIH(grammar, gm, marks, input, fuel, s, rest)
  SurvDone(True{}, grammar, gm, marks, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, above, span, after)

def surv_round(rpath, grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, above, span, after, a, ch, rest, pEq, sp, pos, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(SurvDone(True{}, grammar, gm, marks, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, all0))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +allCh = R.in_app_left(wCh, wRest, kept, allW)
          +allRest = R.in_app_right(wCh, wRest, kept, allW)
          +spCh = G.spells_first(input, k, w, lr, sp)
          +spRest = G.spells_second(input, k, w, lr, sp)
          +next = List.append(&2, Nat, lr, after)
          +posCh = PG.pos_children(w, lr, after, input, k, pos)
          +posRest = PG.pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
          +one = round_group(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, allCh)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +same = Spec.sameAbove(above, span, w)
          +xs = {Spec.lhsOf(grammar, index) <> same : +List<Nat>}
          (r => no_round_rival(grammar, gm, marks, alts, one, index, prefix, a, isA, w, next, xs, r),
            (ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, same, w, next, pEqA, spCh, posCh, (itemsEqR, (fitCh, allCh))),
              ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, above, span, after, pEq, spRest, posRest, (loopIt, (isL, (fitRest, allRest))))))

law surv_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SurvReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts)
  SurvDone(rounds, grammar, gm, marks, forest, items, index, prefix, dot, alts, above, span, after)

def surv_walk(forest, rounds, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, pEq, sp, pos, ready):
  match forest rounds:
    case Nil{} False{}:
      surv_nil(items, grammar, gm, marks, index, prefix, dot, above, span, after)
    case Nil{} True{}:
      Unit{}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      surv_leaf(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, k0, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      surv_node(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, q, ch, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      surv_pick(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, a, ch, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      surv_skip(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      surv_loop(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, rs, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(rs, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      surv_round(rpath, grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, above, span, after, a, ch, rest, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => pe => spx => po => rd => surv_walk(rest, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, pe, spx, po, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(SurvDone(True{}, grammar, gm, marks, Spec.Leaf{k0} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(SurvDone(True{}, grammar, gm, marks, Spec.Node{q, ch} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(SurvDone(True{}, grammar, gm, marks, Spec.Skip{} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(SurvDone(True{}, grammar, gm, marks, Spec.Loop{rs} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

# A parse tree that uses only kept steps is unbeaten.
law survivors:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for allT: {Spec.allIn(Spec.steps(tree, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  Spec.Unbeaten(grammar, gm, marks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])

def survivors(grammar, gm, marks, start, input, fuel, s, okAll, tree, fitting, spelled, allT):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd(Spec.Unbeaten(grammar, gm, marks, [Spec.Leaf{k}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      +both = fitting
      +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, both)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +w = Spec.leaves(ch)
      +spCh = G.root_spells(input, q, ch, spelled)
      +all = {allT : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
      +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
      +keep = node_keep(fuel, grammar, gm, marks, input, s, q, ch, 0n, fitCh, all)
      +xs = {start <> Spec.sameAbove([], [], w) : +List<Nat>}
      (r => no_prod_rival(fuel, grammar, gm, marks, input, start, q, ch, 0n, spCh, lhsQ, keep, xs, [], pos, r),
        (surv_walk(ch, False{}, grammar, gm, marks, input, fuel, s, okAll, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], xs, w, [], {==}, spCh, pos, ({==}, (fitCh, all))), Unit{}))
    case Spec.Pick{a, ch}:
      Empty.absurd(Spec.Unbeaten(grammar, gm, marks, [Spec.Pick{a, ch}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd(Spec.Unbeaten(grammar, gm, marks, [Spec.Skip{}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd(Spec.Unbeaten(grammar, gm, marks, [Spec.Loop{rs}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))

# ======== THE NONTERMINALS ABOVE A NODE ARE IN C ========

# A link from z1 up to z2: a step of the set says z1 is the first item of a sequence of
# z2 over the tokens w, with nothing before it.
def linkStep(+grammar: +List<Spec.Production>, +input: +List<Nat>, +z1: Nat, +z2: Nat, +w: +List<Nat>, +e: Spec.Bsr) -> Bool:
  Bool.and(Prefer.triggers(grammar, input, [z1], w, e), Nat.is_eq(Prefer.ownerOf(grammar, e), z2))

def anyLink(set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +z1: Nat, +z2: Nat, +w: +List<Nat>) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{+e, rest}:
      Bool.or(linkStep(grammar, input, z1, z2, w, e), anyLink(rest, grammar, input, z1, z2, w))

# Every two neighbours of the list are linked.
def linkedFrom(rest: +List<Nat>, +z: Nat, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +w: +List<Nat>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case Con{+z2, more}:
      Bool.and(anyLink(set, grammar, input, z, z2, w), linkedFrom(more, z2, set, grammar, input, w))

def linked(above: +List<Nat>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +w: +List<Nat>) -> Bool:
  match above:
    case Nil{}:
      True{}
    case Con{+z, rest}:
      linkedFrom(rest, z, set, grammar, input, w)

def headOk(above: +List<Nat>, +owner: Nat) -> Bool:
  match above:
    case Nil{}:
      True{}
    case Con{z, rest}:
      Nat.is_eq(z, owner)

def allNatIn(xs: +List<Nat>, +c: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Prefer.natIn(x, c), allNatIn(rest, c))

law nat_in_one:
  for +y: Nat
  for +z: Nat
  for e: {Prefer.natIn(y, [z]) == True{} : Bool}
  {y == z : Nat}

def nat_in_one(y, z, e):
  Lemma.nat_eq_sound(y, z, Lemma.or_false_right(Nat.is_eq(y, z), e))

law nt_in_mono:
  for item: Maybe<&2, Spec.Item>
  for +z: Nat
  for +c: +List<Nat>
  for +inC: {Prefer.natIn(z, c) == True{} : Bool}
  for e: {Prefer.ntIn(item, [z]) == True{} : Bool}
  {Prefer.ntIn(item, c) == True{} : Bool}

def nt_in_mono(item, z, c, inC, e):
  match item:
    case Some{Spec.Sym{Spec.Nonterminal{+y}}}:
      %Equal.sym(Nat, y, z, nat_in_one(y, z, e)) : {Prefer.natIn(_, c) == True{} : Bool}
      inC
    case Some{Spec.Sym{Spec.Terminal{t}}}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))
    case Some{Spec.Brack{kind, alts}}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))
    case Some{Spec.Eps{}}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))

law triggers_mono:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +z: Nat
  for +c: +List<Nat>
  for +w: +List<Nat>
  for e: Spec.Bsr
  for +inC: {Prefer.natIn(z, c) == True{} : Bool}
  for t: {Prefer.triggers(grammar, input, [z], w, e) == True{} : Bool}
  {Prefer.triggers(grammar, input, c, w, e) == True{} : Bool}

def triggers_mono(grammar, input, z, c, w, e, inC, t):
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, +k, +j}:
      +a = Nat.is_eq(i, k)
      +b = Gll.natsEq(Prefer.tokensFrom(input, k, j), w)
      +item = Prefer.itemBefore(Gll.reverseOnto(path, []), grammar, index)
      +both = t
      +rest = Lemma.and_true_right_side(a, Bool.and(b, Prefer.ntIn(item, [z])), both)
      Lemma.and_true_intro(a, Bool.and(b, Prefer.ntIn(item, c)), Lemma.and_true_left(a, Bool.and(b, Prefer.ntIn(item, [z])), both),
        Lemma.and_true_intro(b, Prefer.ntIn(item, c), Lemma.and_true_left(b, Prefer.ntIn(item, [z]), rest), nt_in_mono(item, z, c, inC, Lemma.and_true_right_side(b, Prefer.ntIn(item, [z]), rest))))

law owner_in:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for ok: {Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}
  for t: {Prefer.triggers(grammar, input, c, w, e) == True{} : Bool}
  {Prefer.natIn(Prefer.ownerOf(grammar, e), c) == True{} : Bool}

def owner_in(grammar, input, c, w, e, ok, t):
  +tr = Prefer.triggers(grammar, input, c, w, e)
  +nt = Equal.cong(Bool, Bool, v => Bool.not(v), tr, True{}, t)
  Lemma.or_false_left(Bool.not(tr), Prefer.natIn(Prefer.ownerOf(grammar, e), c), nt, ok)

law link_pick:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +z1: Nat
  for +z2: Nat
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for +inC: {Prefer.natIn(z1, c) == True{} : Bool}
  for +ok: {Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}
  for -rest: +List<Spec.Bsr>
  for cases: Either<{linkStep(grammar, input, z1, z2, w, e) == True{} : Bool}, {anyLink(rest, grammar, input, z1, z2, w) == True{} : Bool}>
  for searchRest: {anyLink(rest, grammar, input, z1, z2, w) == True{} : Bool} -> {Prefer.natIn(z2, c) == True{} : Bool}
  {Prefer.natIn(z2, c) == True{} : Bool}

def link_pick(grammar, input, z1, z2, c, w, e, inC, ok, rest, cases, searchRest):
  match cases:
    case Inl{here0}:
      +here = {here0 : {linkStep(grammar, input, z1, z2, w, e) == True{} : Bool}}
      +tz = Prefer.triggers(grammar, input, [z1], w, e)
      +oz = Nat.is_eq(Prefer.ownerOf(grammar, e), z2)
      +tc = triggers_mono(grammar, input, z1, c, w, e, inC, Lemma.and_true_left(tz, oz, here))
      +eqO = Lemma.nat_eq_sound(Prefer.ownerOf(grammar, e), z2, Lemma.and_true_right_side(tz, oz, here))
      %eqO : {Prefer.natIn(_, c) == True{} : Bool}
      owner_in(grammar, input, c, w, e, ok, tc)
    case Inr{later}:
      searchRest(later)

# In a closed C, a link up from a member of C leads to a member of C.
law link_closed:
  for set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +z1: Nat
  for +z2: Nat
  for +c: +List<Nat>
  for +w: +List<Nat>
  for closed: {Prefer.closedFor(set, grammar, input, c, w) == True{} : Bool}
  for +inC: {Prefer.natIn(z1, c) == True{} : Bool}
  for link: {anyLink(set, grammar, input, z1, z2, w) == True{} : Bool}
  {Prefer.natIn(z2, c) == True{} : Bool}

def link_closed(set, grammar, input, z1, z2, c, w, closed, inC, link):
  match set:
    case Nil{}:
      Empty.absurd({Prefer.natIn(z2, c) == True{} : Bool}, Lemma.false_is_not_true(link))
    case Con{+e, +rest}:
      +both = closed
      link_pick(grammar, input, z1, z2, c, w, e, inC, Lemma.and_true_left(Prefer.ruleOk(grammar, input, c, w, e), Prefer.closedFor(rest, grammar, input, c, w), both),
        rest, Lemma.or_true_cases(linkStep(grammar, input, z1, z2, w, e), anyLink(rest, grammar, input, z1, z2, w), link),
        later => link_closed(rest, grammar, input, z1, z2, c, w, Lemma.and_true_right_side(Prefer.ruleOk(grammar, input, c, w, e), Prefer.closedFor(rest, grammar, input, c, w), both), inC, later))

# A linked chain that starts in a closed C stays in C.
law chain_in:
  for rest: +List<Nat>
  for +z: Nat
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +closed: {Prefer.closedFor(set, grammar, input, c, w) == True{} : Bool}
  for +inC: {Prefer.natIn(z, c) == True{} : Bool}
  for lk: {linkedFrom(rest, z, set, grammar, input, w) == True{} : Bool}
  {allNatIn(z <> rest, c) == True{} : Bool}

def chain_in(rest, z, set, grammar, input, c, w, closed, inC, lk):
  match rest:
    case Nil{}:
      Lemma.and_true_intro(Prefer.natIn(z, c), True{}, inC, {==})
    case Con{+z2, +more}:
      +both = lk
      +in2 = link_closed(set, grammar, input, z, z2, c, w, closed, inC, Lemma.and_true_left(anyLink(set, grammar, input, z, z2, w), linkedFrom(more, z2, set, grammar, input, w), both))
      Lemma.and_true_intro(Prefer.natIn(z, c), allNatIn(z2 <> more, c), inC, chain_in(more, z2, set, grammar, input, c, w, closed, in2, Lemma.and_true_right_side(anyLink(set, grammar, input, z, z2, w), linkedFrom(more, z2, set, grammar, input, w), both)))

# The nonterminals above, when the owner is in a closed C, are in C.
law above_in:
  for above: +List<Nat>
  for +owner: Nat
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +closed: {Prefer.closedFor(set, grammar, input, c, w) == True{} : Bool}
  for +ownerIn: {Prefer.natIn(owner, c) == True{} : Bool}
  for head: {headOk(above, owner) == True{} : Bool}
  for lk: {linked(above, set, grammar, input, w) == True{} : Bool}
  {allNatIn(above, c) == True{} : Bool}

def above_in(above, owner, set, grammar, input, c, w, closed, ownerIn, head, lk):
  match above:
    case Nil{}:
      {==}
    case Con{+z, +rest}:
      +zEq = Lemma.nat_eq_sound(z, owner, head)
      +zIn = Equal.trans(Bool, Prefer.natIn(z, c), Prefer.natIn(owner, c), True{}, Equal.cong(Nat, Bool, v => Prefer.natIn(v, c), z, owner, zEq), ownerIn)
      chain_in(rest, z, set, grammar, input, c, w, closed, zIn, lk)

# ======== REVISITS GROWS WITH THE SET ========

law nat_in_pick:
  for +x: Nat
  for +y: Nat
  for -rest: +List<Nat>
  for +c: +List<Nat>
  for cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Prefer.natIn(x, rest) == True{} : Bool}>
  for +yIn: {Prefer.natIn(y, c) == True{} : Bool}
  for searchRest: {Prefer.natIn(x, rest) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool}
  {Prefer.natIn(x, c) == True{} : Bool}

def nat_in_pick(x, y, rest, c, cases, yIn, searchRest):
  match cases:
    case Inl{eq}:
      %Equal.sym(Nat, x, y, Lemma.nat_eq_sound(x, y, eq)) : {Prefer.natIn(_, c) == True{} : Bool}
      yIn
    case Inr{later}:
      searchRest(later)

law nat_in_of_all:
  for xs: +List<Nat>
  for +x: Nat
  for +c: +List<Nat>
  for sub: {allNatIn(xs, c) == True{} : Bool}
  for m: {Prefer.natIn(x, xs) == True{} : Bool}
  {Prefer.natIn(x, c) == True{} : Bool}

def nat_in_of_all(xs, x, c, sub, m):
  match xs:
    case Nil{}:
      Empty.absurd({Prefer.natIn(x, c) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +both = sub
      nat_in_pick(x, y, rest, c, Lemma.or_true_cases(Nat.is_eq(x, y), Prefer.natIn(x, rest), m), Lemma.and_true_left(Prefer.natIn(y, c), allNatIn(rest, c), both),
        later => nat_in_of_all(rest, x, c, Lemma.and_true_right_side(Prefer.natIn(y, c), allNatIn(rest, c), both), later))

law lhs_among_pick:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for +y: Nat
  for -rest: +List<Nat>
  for cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Prefer.natIn(x, rest) == True{} : Bool}>
  for +l: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for searchRest: {Prefer.natIn(x, rest) == True{} : Bool} -> {Spec.lhsAmong(grammar, q, rest) == True{} : Bool}
  {Spec.lhsAmong(grammar, q, y <> rest) == True{} : Bool}

def lhs_among_pick(grammar, q, x, y, rest, cases, l, searchRest):
  match cases:
    case Inl{eq}:
      +ly = Equal.trans(Bool, Spec.lhsIs(grammar, q, y), Spec.lhsIs(grammar, q, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, q, v), y, x, Equal.sym(Nat, x, y, Lemma.nat_eq_sound(x, y, eq))), l)
      Lemma.or_true_left_intro(Spec.lhsIs(grammar, q, y), Spec.lhsAmong(grammar, q, rest), ly)
    case Inr{later}:
      Lemma.or_true_right_intro(Spec.lhsIs(grammar, q, y), Spec.lhsAmong(grammar, q, rest), searchRest(later))

law lhs_among_in:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for c: +List<Nat>
  for inC: {Prefer.natIn(x, c) == True{} : Bool}
  for +l: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {Spec.lhsAmong(grammar, q, c) == True{} : Bool}

def lhs_among_in(grammar, q, x, c, inC, l):
  match c:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(inC))
    case Con{+y, +rest}:
      lhs_among_pick(grammar, q, x, y, rest, Lemma.or_true_cases(Nat.is_eq(x, y), Prefer.natIn(x, rest), inC), l,
        later => lhs_among_in(grammar, q, x, rest, later, l))

law among_pick:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +x: Nat
  for -rest: +List<Nat>
  for +c: +List<Nat>
  for cases: Either<{Spec.lhsIs(grammar, q, x) == True{} : Bool}, {Spec.lhsAmong(grammar, q, rest) == True{} : Bool}>
  for +xIn: {Prefer.natIn(x, c) == True{} : Bool}
  for searchRest: {Spec.lhsAmong(grammar, q, rest) == True{} : Bool} -> {Spec.lhsAmong(grammar, q, c) == True{} : Bool}
  {Spec.lhsAmong(grammar, q, c) == True{} : Bool}

def among_pick(grammar, q, x, rest, c, cases, xIn, searchRest):
  match cases:
    case Inl{l}:
      lhs_among_in(grammar, q, x, c, xIn, l)
    case Inr{later}:
      searchRest(later)

law lhs_among_mono:
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for xs: +List<Nat>
  for +c: +List<Nat>
  for +sub: {allNatIn(xs, c) == True{} : Bool}
  for e: {Spec.lhsAmong(grammar, q, xs) == True{} : Bool}
  {Spec.lhsAmong(grammar, q, c) == True{} : Bool}

def lhs_among_mono(grammar, q, xs, c, sub, e):
  match xs:
    case Nil{}:
      Empty.absurd({Spec.lhsAmong(grammar, q, c) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{+x, +rest}:
      +both = sub
      among_pick(grammar, q, x, rest, c, Lemma.or_true_cases(Spec.lhsIs(grammar, q, x), Spec.lhsAmong(grammar, q, rest), e), Lemma.and_true_left(Prefer.natIn(x, c), allNatIn(rest, c), both),
        later => lhs_among_mono(grammar, q, rest, c, Lemma.and_true_right_side(Prefer.natIn(x, c), allNatIn(rest, c), both), later))

law or_map:
  for x: Bool
  for -y: Bool
  for +x2: Bool
  for +y2: Bool
  for e: {Bool.or(x, y) == True{} : Bool}
  for f: {x == True{} : Bool} -> {x2 == True{} : Bool}
  for g: {y == True{} : Bool} -> {y2 == True{} : Bool}
  {Bool.or(x2, y2) == True{} : Bool}

def or_map(x, y, x2, y2, e, f, g):
  match x:
    case True{}:
      Lemma.or_true_left_intro(x2, y2, f({==}))
    case False{}:
      Lemma.or_true_right_intro(x2, y2, g(e))

law and_mono_left:
  for a: Bool
  for +b: Bool
  for +a2: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  for f: {a == True{} : Bool} -> {a2 == True{} : Bool}
  {Bool.and(a2, b) == True{} : Bool}

def and_mono_left(a, b, a2, e, f):
  match a:
    case True{}:
      Lemma.and_true_intro(a2, b, f({==}), e)
    case False{}:
      Empty.absurd({Bool.and(a2, b) == True{} : Bool}, Lemma.false_is_not_true(e))

law revisits_mono:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +xs: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +sub: {allNatIn(xs, c) == True{} : Bool}
  for e: {Spec.revisits(grammar, forest, xs, w) == True{} : Bool}
  {Spec.revisits(grammar, forest, c, w) == True{} : Bool}

def revisits_mono(forest, grammar, xs, c, w, sub, e):
  match forest:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts}:
      +p = Spec.pathEq(Spec.leaves(ch), w)
      or_map(Bool.or(Bool.and(Spec.lhsAmong(grammar, q, xs), p), Spec.revisits(grammar, ch, xs, w)), Spec.revisits(grammar, ts, xs, w), Bool.or(Bool.and(Spec.lhsAmong(grammar, q, c), p), Spec.revisits(grammar, ch, c, w)), Spec.revisits(grammar, ts, c, w), e,
        h => or_map(Bool.and(Spec.lhsAmong(grammar, q, xs), p), Spec.revisits(grammar, ch, xs, w), Bool.and(Spec.lhsAmong(grammar, q, c), p), Spec.revisits(grammar, ch, c, w), h,
          h2 => and_mono_left(Spec.lhsAmong(grammar, q, xs), p, Spec.lhsAmong(grammar, q, c), h2, l => lhs_among_mono(grammar, q, xs, c, sub, l)),
          h3 => revisits_mono(ch, grammar, xs, c, w, sub, h3)),
        h4 => revisits_mono(ts, grammar, xs, c, w, sub, h4))
    case Con{Spec.Pick{+a, +ch}, +ts}:
      or_map(Spec.revisits(grammar, ch, xs, w), Spec.revisits(grammar, ts, xs, w), Spec.revisits(grammar, ch, c, w), Spec.revisits(grammar, ts, c, w), e,
        h => revisits_mono(ch, grammar, xs, c, w, sub, h), h2 => revisits_mono(ts, grammar, xs, c, w, sub, h2))
    case Con{Spec.Loop{+rs}, +ts}:
      or_map(Spec.revisits(grammar, rs, xs, w), Spec.revisits(grammar, ts, xs, w), Spec.revisits(grammar, rs, c, w), Spec.revisits(grammar, ts, c, w), e,
        h => revisits_mono(rs, grammar, xs, c, w, sub, h), h2 => revisits_mono(ts, grammar, xs, c, w, sub, h2))
    case Con{Spec.Leaf{+k}, +ts}:
      revisits_mono(ts, grammar, xs, c, w, sub, e)
    case Con{Spec.Skip{}, +ts}:
      revisits_mono(ts, grammar, xs, c, w, sub, e)

law clean_pick:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +forest: +List<Spec.Tree>
  for +xs: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +isB: {Spec.revisits(grammar, forest, xs, w) == b : Bool}
  for +sub: {allNatIn(xs, c) == True{} : Bool}
  for clean: {Spec.revisits(grammar, forest, c, w) == False{} : Bool}
  {Spec.revisits(grammar, forest, xs, w) == False{} : Bool}

def clean_pick(b, grammar, forest, xs, c, w, isB, sub, clean):
  match b:
    case True{}:
      Empty.absurd({Spec.revisits(grammar, forest, xs, w) == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Spec.revisits(grammar, forest, c, w), False{}, Equal.sym(Bool, Spec.revisits(grammar, forest, c, w), True{}, revisits_mono(forest, grammar, xs, c, w, sub, isB)), clean)))
    case False{}:
      isB

# A forest with no node of C over the tokens has none of a part of C either.
law revisits_clean:
  for +grammar: +List<Spec.Production>
  for +forest: +List<Spec.Tree>
  for +xs: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +sub: {allNatIn(xs, c) == True{} : Bool}
  for clean: {Spec.revisits(grammar, forest, c, w) == False{} : Bool}
  {Spec.revisits(grammar, forest, xs, w) == False{} : Bool}

def revisits_clean(grammar, forest, xs, c, w, sub, clean):
  clean_pick(Spec.revisits(grammar, forest, xs, w), grammar, forest, xs, c, w, {==}, sub, clean)

# ======== A CERTIFICATE IS A RIVAL ========

# The set C of a certificate.
def certC(+grammar: +List<Spec.Production>, +input: +List<Nat>, +s: +List<Spec.Bsr>, +d: Prefer.Done, +i: Nat, +j: Nat) -> +List<Nat>:
  Prefer.grow(List.length(&2, Spec.Production, grammar), s, grammar, input, [Prefer.choiceNt(d, grammar)], Prefer.tokensFrom(input, i, j))

# A rival forest that passes the certificate's check.
def RivalFor(+d: Prefer.Done, +grammar: +List<Spec.Production>, +ks: +List<Spec.Bsr>, +who: Nat, +i: Nat, +items: +List<Spec.Item>, +c: +List<Nat>, +w: +List<Nat>) -> Type:
  &f: +List<Spec.Tree> -> {Prefer.rivalOk(d, grammar, ks, who, i, items, c, w, f) == True{} : Bool}

def CertParts(+fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: +List<Spec.Bsr>, +ks: +List<Spec.Bsr>, +d: Prefer.Done, +who: Nat, +i: Nat, +j: Nat) -> Type:
  {Prefer.natIn(Prefer.choiceNt(d, grammar), certC(grammar, input, s, d, i, j)) == True{} : Bool} & {Prefer.closedFor(s, grammar, input, certC(grammar, input, s, d, i, j), Prefer.tokensFrom(input, i, j)) == True{} : Bool} &
    RivalFor(d, grammar, ks, who, i, Prefer.rivalItems(d, grammar, who), certC(grammar, input, s, d, i, j), Prefer.tokensFrom(input, i, j))

law rival_pick:
  for +d: Prefer.Done
  for +grammar: +List<Spec.Production>
  for +ks: +List<Spec.Bsr>
  for +who: Nat
  for +i: Nat
  for +items: +List<Spec.Item>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +f: +List<Spec.Tree>
  for -rest: +List<+List<Spec.Tree>>
  for cases: Either<{Prefer.rivalOk(d, grammar, ks, who, i, items, c, w, f) == True{} : Bool}, {Prefer.anyRivalOk(rest, d, grammar, ks, who, i, items, c, w) == True{} : Bool}>
  for searchRest: {Prefer.anyRivalOk(rest, d, grammar, ks, who, i, items, c, w) == True{} : Bool} -> RivalFor(d, grammar, ks, who, i, items, c, w)
  RivalFor(d, grammar, ks, who, i, items, c, w)

def rival_pick(d, grammar, ks, who, i, items, c, w, f, rest, cases, searchRest):
  match cases:
    case Inl{here}:
      (f, here)
    case Inr{later}:
      searchRest(later)

law rival_of_any:
  for fs: +List<+List<Spec.Tree>>
  for +d: Prefer.Done
  for +grammar: +List<Spec.Production>
  for +ks: +List<Spec.Bsr>
  for +who: Nat
  for +i: Nat
  for +items: +List<Spec.Item>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for e: {Prefer.anyRivalOk(fs, d, grammar, ks, who, i, items, c, w) == True{} : Bool}
  RivalFor(d, grammar, ks, who, i, items, c, w)

def rival_of_any(fs, d, grammar, ks, who, i, items, c, w, e):
  match fs:
    case Nil{}:
      Empty.absurd(RivalFor(d, grammar, ks, who, i, items, c, w), Lemma.false_is_not_true(e))
    case Con{+f, +rest}:
      rival_pick(d, grammar, ks, who, i, items, c, w, f, rest, Lemma.or_true_cases(Prefer.rivalOk(d, grammar, ks, who, i, items, c, w, f), Prefer.anyRivalOk(rest, d, grammar, ks, who, i, items, c, w), e),
        later => rival_of_any(rest, d, grammar, ks, who, i, items, c, w, later))

law cert_parts:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +d: Prefer.Done
  for +who: Nat
  for +i: Nat
  for +j: Nat
  for e: {Prefer.certOk(fuel, grammar, input, s, ks, d, who, i, j) == True{} : Bool}
  CertParts(fuel, grammar, input, s, ks, d, who, i, j)

def cert_parts(fuel, grammar, input, s, ks, d, who, i, j, e):
  +w = Prefer.tokensFrom(input, i, j)
  +c = certC(grammar, input, s, d, i, j)
  +x = Prefer.choiceNt(d, grammar)
  +fs = Prefer.rivalForests(d, fuel, grammar, input, ks, who, i, j)
  +items = Prefer.rivalItems(d, grammar, who)
  +both = e
  +left = Lemma.and_true_left(Bool.and(Prefer.natIn(x, c), Prefer.closedFor(s, grammar, input, c, w)), Prefer.anyRivalOk(fs, d, grammar, ks, who, i, items, c, w), both)
  (Lemma.and_true_left(Prefer.natIn(x, c), Prefer.closedFor(s, grammar, input, c, w), left),
    (Lemma.and_true_right_side(Prefer.natIn(x, c), Prefer.closedFor(s, grammar, input, c, w), left),
      rival_of_any(fs, d, grammar, ks, who, i, items, c, w, Lemma.and_true_right_side(Bool.and(Prefer.natIn(x, c), Prefer.closedFor(s, grammar, input, c, w)), Prefer.anyRivalOk(fs, d, grammar, ks, who, i, items, c, w), both))))

# A forest of a certificate, over the node's tokens, avoiding C, derives them once for
# any part of C.
law derives_once_of:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +items: +List<Spec.Item>
  for +c: +List<Nat>
  for +wTok: +List<Nat>
  for +w: +List<Nat>
  for +xs: +List<Nat>
  for +f: +List<Spec.Tree>
  for +ok: {Prefer.forestOk(grammar, items, c, wTok, f) == True{} : Bool}
  for +tEq: {wTok == w : +List<Nat>}
  for +sub: {allNatIn(xs, c) == True{} : Bool}
  for +own: +List<Spec.Guard>
  for +idx: Nat
  for +pre: +List<Nat>
  for +after: +List<Nat>
  for holds: Spec.AllHold(grammar, own, items, f, List.append(&2, Nat, w, after))
  for adm: Spec.Admissible(grammar, gm, f, items, idx, pre, 0n, after)
  Spec.DerivesOnce(grammar, gm, items, own, idx, pre, w, after, xs)

def derives_once_of(grammar, gm, items, c, wTok, w, xs, f, ok, tEq, sub, own, idx, pre, after, holds, adm):
  +fitsF = Spec.fits(f, grammar, items)
  +eqL = Gll.natsEq(Spec.leaves(f), wTok)
  +rv = Spec.revisits(grammar, f, c, wTok)
  +rest = Lemma.and_true_right_side(fitsF, Bool.and(eqL, Bool.not(rv)), ok)
  +lv = Equal.trans(+List<Nat>, Spec.leaves(f), wTok, w, G.nats_eq_sound(Spec.leaves(f), wTok, Lemma.and_true_left(eqL, Bool.not(rv), rest)), tEq)
  +nr = not_true_false(rv, Lemma.and_true_right_side(eqL, Bool.not(rv), rest))
  +nr2 = Equal.trans(Bool, Spec.revisits(grammar, f, c, w), rv, False{}, Equal.cong(+List<Nat>, Bool, v => Spec.revisits(grammar, f, c, v), w, wTok, Equal.sym(+List<Nat>, wTok, w, tEq)), nr)
  (f, (Lemma.and_true_left(fitsF, Bool.and(eqL, Bool.not(rv)), ok), (lv, (revisits_clean(grammar, f, xs, c, w, sub, nr2), (holds, adm)))))

# ======== POSITIONS ========

law add_comm:
  for a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Lemma.add_zero_right(b))
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, v => 1n+v, Nat.add(p, b), Nat.add(b, p), add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Lemma.add_succ_right(b, p)))

law add_cancel_right:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {Nat.add(a, c) == Nat.add(b, c) : Nat}
  {a == b : Nat}

def add_cancel_right(a, b, c, e):
  Lemma.add_cancel_left(c, a, b, Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(c, b), add_comm(c, a), Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(c, b), e, add_comm(b, c))))

law le_add_self:
  for p: Nat
  for l: Nat
  for e: {Nat.is_le(Nat.add(p, l), p) == True{} : Bool}
  {l == 0n : Nat}

def le_add_self(p, l, e):
  match p:
    case 0n:
      match l:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({1n+m == 0n : Nat}, Lemma.false_is_not_true(e))
    case 1n+q:
      le_add_self(q, l, e)

# A sequence whose part from k reads as much as the whole sequence starts at k.
law start_here:
  for +i: Nat
  for +k: Nat
  for +span: +List<Nat>
  for +w: +List<Nat>
  for +lts: +List<Nat>
  for eq: {Nat.add(i, List.length(&2, Nat, span)) == Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))) : Nat}
  for +le: {Nat.is_le(i, k) == True{} : Bool}
  for same: {Spec.pathEq(w, span) == True{} : Bool}
  {Nat.is_eq(i, k) == True{} : Bool}

def start_here(i, k, span, w, lts, eq, le, same):
  +lw = List.length(&2, Nat, w)
  +ll = List.length(&2, Nat, lts)
  +wSpan = G.path_eq_sound(w, span, same)
  +e1 = Equal.trans(Nat, Nat.add(i, lw), Nat.add(i, List.length(&2, Nat, span)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Equal.cong(+List<Nat>, Nat, v => Nat.add(i, List.length(&2, Nat, v)), w, span, wSpan), eq)
  +e2 = Equal.trans(Nat, Nat.add(i, lw), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(k, Nat.add(lw, ll)), e1, Equal.cong(Nat, Nat, v => Nat.add(k, v), List.length(&2, Nat, List.append(&2, Nat, w, lts)), Nat.add(lw, ll), Lemma.length_append(w, lts)))
  +e3 = Equal.trans(Nat, Nat.add(i, lw), Nat.add(k, Nat.add(lw, ll)), Nat.add(Nat.add(k, ll), lw), e2, Equal.trans(Nat, Nat.add(k, Nat.add(lw, ll)), Nat.add(k, Nat.add(ll, lw)), Nat.add(Nat.add(k, ll), lw), Equal.cong(Nat, Nat, v => Nat.add(k, v), Nat.add(lw, ll), Nat.add(ll, lw), add_comm(lw, ll)), Equal.sym(Nat, Nat.add(Nat.add(k, ll), lw), Nat.add(k, Nat.add(ll, lw)), Lemma.add_assoc(k, ll, lw))))
  +iEq = add_cancel_right(i, Nat.add(k, ll), lw, e3)
  +le2 = Equal.trans(Bool, Nat.is_le(Nat.add(k, ll), k), Nat.is_le(i, k), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(v, k), Nat.add(k, ll), i, Equal.sym(Nat, i, Nat.add(k, ll), iEq)), le)
  +l0 = le_add_self(k, ll, le2)
  +ik = Equal.trans(Nat, i, Nat.add(k, ll), k, iEq, Equal.trans(Nat, Nat.add(k, ll), Nat.add(k, 0n), k, Equal.cong(Nat, Nat, v => Nat.add(k, v), ll, 0n, l0), Lemma.add_zero_right(k)))
  %Equal.sym(Nat, i, k, ik) : {Nat.is_eq(_, k) == True{} : Bool}
  Lemma.nat_eq_refl(k)

# ======== STEPS BEFORE THE END OF A SEQUENCE ========

law drop_cons_len:
  for n: Nat
  for seq: +List<Spec.Item>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for e: {G.dropItems(n, seq) == it <> rest : +List<Spec.Item>}
  {List.length(&2, Spec.Item, seq) == Nat.add(n, 1n+List.length(&2, Spec.Item, rest)) : Nat}

def drop_cons_len(n, seq, it, rest, e):
  match n seq:
    case 0n Nil{}:
      Empty.absurd({0n == 1n+List.length(&2, Spec.Item, rest) : Nat}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => G.itemsEmpty(v), [], it <> rest, e)))
    case 0n Con{+x, +xs}:
      Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), x <> xs, it <> rest, e)
    case 1n+m Nil{}:
      Empty.absurd({0n == Nat.add(1n+m, 1n+List.length(&2, Spec.Item, rest)) : Nat}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Item>, Bool, v => G.itemsEmpty(v), [], it <> rest, e)))
    case 1n+(+m) Con{x, +xs}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Item, xs), Nat.add(m, 1n+List.length(&2, Spec.Item, rest)), drop_cons_len(m, xs, it, rest, e))

law ne_succ:
  for dot: Nat
  for +m: Nat
  {Nat.is_eq(1n+dot, Nat.add(dot, 1n+1n+m)) == False{} : Bool}

def ne_succ(dot, m):
  match dot:
    case 0n:
      {==}
    case 1n+p:
      ne_succ(p, m)

law fits_nil_items:
  for +grammar: +List<Spec.Production>
  for items: +List<Spec.Item>
  for e: {Spec.fits([], grammar, items) == True{} : Bool}
  {items == [] : +List<Spec.Item>}

def fits_nil_items(grammar, items, e):
  match items:
    case Nil{}:
      {==}
    case Con{it, rest}:
      Empty.absurd({it <> rest == [] : +List<Spec.Item>}, Lemma.false_is_not_true(e))

law verdict_not_done:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for ne: {Nat.is_eq(d, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath))) == False{} : Bool}
  {Prefer.isKeep(Unb.verdictOf(fuel, grammar, gm, marks, input, Spec.at(index, prefix, d, i, k, j))) == True{} : Bool}

def verdict_not_done(fuel, grammar, gm, marks, input, index, rpath, prefix, pEq, d, i, k, j, ne):
  +rev = Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), [])
  +revEq = R.step_rev(rpath, prefix, d, pEq)
  +nd = done_not(d, rpath, grammar, index, ne)
  +dEq = Equal.trans(Prefer.Done, Prefer.doneAt(rev, grammar, index), Prefer.doneAt(d <> rpath, grammar, index), Prefer.NotDone{}, Equal.cong(+List<Nat>, Prefer.Done, v => Prefer.doneAt(v, grammar, index), rev, d <> rpath, revEq), nd)
  Equal.cong(Prefer.Done, Bool, v => Prefer.isKeep(Unb.verdictFor(v, fuel, grammar, gm, marks, input, i, j)), Prefer.doneAt(rev, grammar, index), Prefer.NotDone{}, dEq)

# The completion of a sequence is kept, when its step is in the exact set.
def Encl(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +n: Nat, +i: Nat, +j: Nat) -> Type:
  @piv: Nat -> {Spec.bsrMember(Spec.at(index, prefix, n, i, piv, j), s) == True{} : Bool} -> {Spec.bsrMember(Spec.at(index, prefix, n, i, piv, j), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

# The step of a child is kept: before the end it completes no choice, and at the end it
# is the completion of the sequence.
law child_last:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +t: Spec.Tree
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +n: Nat
  for +nEq: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}
  for +j: Nat
  for +jEq: {j == Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))) : Nat}
  for +rem: {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == it <> rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits([], grammar, rest) == True{} : Bool}
  for +mS: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), s) == True{} : Bool}
  for encl: Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
  {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def child_last(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, n, nEq, j, jEq, rem, fitTs, mS, encl):
  +seq = Gll.seqAt(grammar, index, rpath)
  +restNil = fits_nil_items(grammar, rest, fitTs)
  +lenSeq = drop_cons_len(dot, seq, it, rest, rem)
  +lenRest = Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), rest, [], restNil)
  +nD = Equal.trans(Nat, n, List.length(&2, Spec.Item, seq), 1n+dot, Equal.sym(Nat, List.length(&2, Spec.Item, seq), n, nEq), Equal.trans(Nat, List.length(&2, Spec.Item, seq), Nat.add(dot, 1n+List.length(&2, Spec.Item, rest)), 1n+dot, lenSeq, Equal.trans(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Item, rest)), Nat.add(dot, 1n), 1n+dot, Equal.cong(Nat, Nat, v => Nat.add(dot, 1n+v), List.length(&2, Spec.Item, rest), 0n, lenRest), Lemma.add_one_right(dot))))
  +jE = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), Sub.endOf(t, k), jEq, Equal.sym(Nat, Sub.endOf(t, k), Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), Sub.end_of_one(t, k)))
  +y = Spec.at(index, prefix, n, i, k, j)
  +yEq = Equal.trans(Spec.Bsr, y, Spec.at(index, prefix, 1n+dot, i, k, j), Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, v, i, k, j), n, 1n+dot, nD), Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, 1n+dot, i, k, v), j, Sub.endOf(t, k), jE))
  +mS2 = Equal.trans(Bool, Spec.bsrMember(y, s), Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), s), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, s), y, Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), yEq), mS)
  +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
  +mK = encl(k, mS2)
  Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), kept), Spec.bsrMember(y, kept), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, kept), Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), y, Equal.sym(Spec.Bsr, y, Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), yEq)), mK)

law child_mid:
  for +t2: Spec.Tree
  for +ts2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +t: Spec.Tree
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +rem: {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == it <> rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(t2 <> ts2, grammar, rest) == True{} : Bool}
  for +mS: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), s) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def child_mid(t2, ts2, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, rem, fitTs, mS):
  +seq = Gll.seqAt(grammar, index, rpath)
  +lenSeq = drop_cons_len(dot, seq, it, rest, rem)
  +cnt = Fits.fits_count(t2 <> ts2, grammar, rest, fitTs)
  +lenSeq2 = Equal.trans(Nat, List.length(&2, Spec.Item, seq), Nat.add(dot, 1n+List.length(&2, Spec.Item, rest)), Nat.add(dot, 1n+1n+List.length(&2, Spec.Tree, ts2)), lenSeq, Equal.cong(Nat, Nat, v => Nat.add(dot, 1n+v), List.length(&2, Spec.Item, rest), 1n+List.length(&2, Spec.Tree, ts2), Equal.sym(Nat, 1n+List.length(&2, Spec.Tree, ts2), List.length(&2, Spec.Item, rest), cnt)))
  +ne = Equal.trans(Bool, Nat.is_eq(1n+dot, List.length(&2, Spec.Item, seq)), Nat.is_eq(1n+dot, Nat.add(dot, 1n+1n+List.length(&2, Spec.Tree, ts2))), False{}, Equal.cong(Nat, Bool, v => Nat.is_eq(1n+dot, v), List.length(&2, Spec.Item, seq), Nat.add(dot, 1n+1n+List.length(&2, Spec.Tree, ts2)), lenSeq2), ne_succ(dot, List.length(&2, Spec.Tree, ts2)))
  kept_of(s, fuel, grammar, gm, marks, input, Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), mS, verdict_not_done(fuel, grammar, gm, marks, input, index, rpath, prefix, pEq, 1n+dot, i, k, Sub.endOf(t, k), ne))

# ======== A NODE OVER ALL OF ITS SEQUENCE LINPrefer.kept(s, fuel, grammar, marks, input) UP TO ITS OWNER ========

law closed_pick:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +okX: {Prefer.ruleOk(grammar, input, c, w, x) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}
  {Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}

def closed_pick(grammar, gm, input, c, w, e, x, rest, cases, okX, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, e, x, same) : {Prefer.ruleOk(grammar, input, c, w, _) == True{} : Bool}
      okX
    case Inr{later}:
      searchRest(later)

# Every step of a closed set passes the rule.
law closed_member:
  for set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +c: +List<Nat>
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for closed: {Prefer.closedFor(set, grammar, input, c, w) == True{} : Bool}
  for m: {Spec.bsrMember(e, set) == True{} : Bool}
  {Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}

def closed_member(set, grammar, gm, input, c, w, e, closed, m):
  match set:
    case Nil{}:
      Empty.absurd({Prefer.ruleOk(grammar, input, c, w, e) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      +both = closed
      closed_pick(grammar, gm, input, c, w, e, x, rest, G.ebnf_member_cases(e, x, rest, m), Lemma.and_true_left(Prefer.ruleOk(grammar, input, c, w, x), Prefer.closedFor(rest, grammar, input, c, w), both),
        later => closed_member(rest, grammar, gm, input, c, w, e, Lemma.and_true_right_side(Prefer.ruleOk(grammar, input, c, w, x), Prefer.closedFor(rest, grammar, input, c, w), both), later))

law any_link_pick:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +z1: Nat
  for +z2: Nat
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +l: {linkStep(grammar, input, z1, z2, w, e) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {anyLink(rest, grammar, input, z1, z2, w) == True{} : Bool}
  {anyLink(x <> rest, grammar, input, z1, z2, w) == True{} : Bool}

def any_link_pick(grammar, input, z1, z2, w, e, x, rest, cases, l, searchRest):
  match cases:
    case Inl{same}:
      +lx = Equal.trans(Bool, linkStep(grammar, input, z1, z2, w, x), linkStep(grammar, input, z1, z2, w, e), True{}, Equal.cong(Spec.Bsr, Bool, v => linkStep(grammar, input, z1, z2, w, v), x, e, Equal.sym(Spec.Bsr, e, x, same)), l)
      Lemma.or_true_left_intro(linkStep(grammar, input, z1, z2, w, x), anyLink(rest, grammar, input, z1, z2, w), lx)
    case Inr{later}:
      Lemma.or_true_right_intro(linkStep(grammar, input, z1, z2, w, x), anyLink(rest, grammar, input, z1, z2, w), searchRest(later))

law any_link_of_member:
  for set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +z1: Nat
  for +z2: Nat
  for +w: +List<Nat>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, set) == True{} : Bool}
  for +l: {linkStep(grammar, input, z1, z2, w, e) == True{} : Bool}
  {anyLink(set, grammar, input, z1, z2, w) == True{} : Bool}

def any_link_of_member(set, grammar, input, z1, z2, w, e, m, l):
  match set:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      any_link_pick(grammar, input, z1, z2, w, e, x, rest, G.ebnf_member_cases(e, x, rest, m), l,
        later => any_link_of_member(rest, grammar, input, z1, z2, w, e, later, l))

# The step of a nonterminal x that starts its sequence triggers the rule for any C with x.
law x_triggers:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +end: Nat
  for +x: Nat
  for +c: +List<Nat>
  for +wT: +List<Nat>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +ik: {Nat.is_eq(i, k) == True{} : Bool}
  for +tW: {Prefer.tokensFrom(input, k, end) == wT : +List<Nat>}
  for +inC: {Prefer.natIn(x, c) == True{} : Bool}
  {Prefer.triggers(grammar, input, c, wT, Spec.at(index, prefix, 1n+dot, i, k, end)) == True{} : Bool}

def x_triggers(grammar, input, index, rpath, prefix, pEq, dot, i, k, end, x, c, wT, itemEq, ik, tW, inC):
  +rev = Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+dot]), [])
  +revEq = R.step_rev(rpath, prefix, 1n+dot, pEq)
  +itEq = Equal.trans(Maybe<&2, Spec.Item>, Prefer.itemBefore(rev, grammar, index), Prefer.itemBefore((1n+dot) <> rpath, grammar, index), Some{Spec.Sym{Spec.Nonterminal{x}}}, Equal.cong(+List<Nat>, Maybe<&2, Spec.Item>, v => Prefer.itemBefore(v, grammar, index), rev, (1n+dot) <> rpath, revEq), itemEq)
  +nt = Equal.trans(Bool, Prefer.ntIn(Prefer.itemBefore(rev, grammar, index), c), Prefer.ntIn(Some{Spec.Sym{Spec.Nonterminal{x}}}, c), True{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Prefer.ntIn(v, c), Prefer.itemBefore(rev, grammar, index), Some{Spec.Sym{Spec.Nonterminal{x}}}, itEq), inC)
  +toks = Prefer.tokensFrom(input, k, end)
  +ne = Equal.trans(Bool, Gll.natsEq(toks, wT), Gll.natsEq(wT, wT), True{}, Equal.cong(+List<Nat>, Bool, v => Gll.natsEq(v, wT), toks, wT, tW), Sub.nats_eq_refl(wT))
  Lemma.and_true_intro(Nat.is_eq(i, k), Bool.and(Gll.natsEq(toks, wT), Prefer.ntIn(Prefer.itemBefore(rev, grammar, index), c)), ik,
    Lemma.and_true_intro(Gll.natsEq(toks, wT), Prefer.ntIn(Prefer.itemBefore(rev, grammar, index), c), ne, nt))

def notNt(it: Spec.Item) -> Bool:
  match it:
    case Spec.Sym{Spec.Nonterminal{x}}:
      False{}
    case Spec.Sym{Spec.Terminal{t}}:
      True{}
    case Spec.Brack{kind, alts}:
      True{}
    case Spec.Eps{}:
      True{}

def noNt(items: +List<Spec.Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{+it, rest}:
      Bool.and(notNt(it), noNt(rest))

# Where the sequence starts: for a sequence of a node or a pick, at the start of what
# is left plus what was read before; for the sequence of a round, which starts where
# the loop starts, nothing but brackets in its items.
def StartOk(start: Bool, +i: Nat, +k: Nat, +span: +List<Nat>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>) -> Type:
  match start:
    case True{}:
      {Nat.add(i, List.length(&2, Nat, span)) == Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) : Nat} & {Nat.is_le(i, k) == True{} : Bool}
    case False{}:
      {noNt(items) == True{} : Bool}

# At a node: when it reads as much as its sequence, the sequence starts where it does.
law ik_pick:
  for b: Bool
  for +i: Nat
  for +k: Nat
  for +span: +List<Nat>
  for +w: +List<Nat>
  for +lts: +List<Nat>
  for +isB: {Spec.pathEq(w, span) == b : Bool}
  for +eq: {Nat.add(i, List.length(&2, Nat, span)) == Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))) : Nat}
  for +le: {Nat.is_le(i, k) == True{} : Bool}
  {Bool.or(Bool.not(b), Nat.is_eq(i, k)) == True{} : Bool}

def ik_pick(b, i, k, span, w, lts, isB, eq, le):
  match b:
    case True{}:
      start_here(i, k, span, w, lts, eq, le, isB)
    case False{}:
      {==}

law node_ik:
  for start: Bool
  for +i: Nat
  for +k: Nat
  for +span: +List<Nat>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for st: StartOk(start, i, k, span, Spec.Node{q, ch} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest)
  {Bool.or(Bool.not(Spec.pathEq(Spec.leaves(ch), span)), Nat.is_eq(i, k)) == True{} : Bool}

def node_ik(start, i, k, span, q, ch, ts, x, rest, st):
  match start:
    case True{}:
      match st:
        case (eq, le):
          ik_pick(Spec.pathEq(Spec.leaves(ch), span), i, k, span, Spec.leaves(ch), Spec.leaves(ts), {==}, eq, le)
    case False{}:
      Empty.absurd({Bool.or(Bool.not(Spec.pathEq(Spec.leaves(ch), span)), Nat.is_eq(i, k)) == True{} : Bool}, Lemma.false_is_not_true(st))

law node_xs_in:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +end: Nat
  for +x: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +w: +List<Nat>
  for +isB: {Spec.pathEq(w, span) == b : Bool}
  for +ikIf: {Bool.or(Bool.not(Spec.pathEq(w, span)), Nat.is_eq(i, k)) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +tW: {Prefer.tokensFrom(input, k, end) == w : +List<Nat>}
  for +mX: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, end), s) == True{} : Bool}
  for +head: {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  for +c: +List<Nat>
  for +closed: {Prefer.closedFor(s, grammar, input, c, w) == True{} : Bool}
  for +natX: {Prefer.natIn(x, c) == True{} : Bool}
  {allNatIn(x <> Spec.keepAbove(b, above), c) == True{} : Bool}

def node_xs_in(b, grammar, gm, input, s, index, rpath, prefix, pEq, dot, i, k, end, x, above, span, w, isB, ikIf, itemEq, tW, mX, head, lk, c, closed, natX):
  match b:
    case True{}:
      +ik = Lemma.or_false_left(Bool.not(Spec.pathEq(w, span)), Nat.is_eq(i, k), Equal.cong(Bool, Bool, v => Bool.not(v), Spec.pathEq(w, span), True{}, isB), ikIf)
      +ex = Spec.at(index, prefix, 1n+dot, i, k, end)
      +trig = x_triggers(grammar, input, index, rpath, prefix, pEq, dot, i, k, end, x, c, w, itemEq, ik, tW, natX)
      +ownIn = owner_in(grammar, input, c, w, ex, closed_member(s, grammar, gm, input, c, w, ex, closed, mX), trig)
      +wSpan = G.path_eq_sound(w, span, isB)
      +lk2 = Equal.trans(Bool, linked(above, s, grammar, input, w), linked(above, s, grammar, input, span), True{}, Equal.cong(+List<Nat>, Bool, v => linked(above, s, grammar, input, v), w, span, wSpan), lk)
      Lemma.and_true_intro(Prefer.natIn(x, c), allNatIn(above, c), natX, above_in(above, Spec.lhsOf(grammar, index), s, grammar, input, c, w, closed, ownIn, head, lk2))
    case False{}:
      Lemma.and_true_intro(Prefer.natIn(x, c), True{}, natX, {==})

law node_links:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +end: Nat
  for +x: Nat
  for above: +List<Nat>
  for +span: +List<Nat>
  for +w: +List<Nat>
  for +isB: {Spec.pathEq(w, span) == b : Bool}
  for +ikIf: {Bool.or(Bool.not(Spec.pathEq(w, span)), Nat.is_eq(i, k)) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +tW: {Prefer.tokensFrom(input, k, end) == w : +List<Nat>}
  for +mX: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, end), s) == True{} : Bool}
  for +head: {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  {linked(x <> Spec.keepAbove(b, above), s, grammar, input, w) == True{} : Bool}

def node_links(b, grammar, input, s, index, rpath, prefix, pEq, dot, i, k, end, x, above, span, w, isB, ikIf, itemEq, tW, mX, head, lk):
  match b above:
    case True{} Nil{}:
      {==}
    case True{} Con{+z, +rest}:
      +ik = Lemma.or_false_left(Bool.not(Spec.pathEq(w, span)), Nat.is_eq(i, k), Equal.cong(Bool, Bool, v => Bool.not(v), Spec.pathEq(w, span), True{}, isB), ikIf)
      +ex = Spec.at(index, prefix, 1n+dot, i, k, end)
      +inOne = Lemma.or_true_left_intro(Nat.is_eq(x, x), False{}, Lemma.nat_eq_refl(x))
      +trig = x_triggers(grammar, input, index, rpath, prefix, pEq, dot, i, k, end, x, [x], w, itemEq, ik, tW, inOne)
      +zEq = Lemma.nat_eq_sound(z, Spec.lhsOf(grammar, index), head)
      +own = Equal.trans(Bool, Nat.is_eq(Spec.lhsOf(grammar, index), z), Nat.is_eq(z, z), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(v, z), Spec.lhsOf(grammar, index), z, Equal.sym(Nat, z, Spec.lhsOf(grammar, index), zEq)), Lemma.nat_eq_refl(z))
      +l = Lemma.and_true_intro(Prefer.triggers(grammar, input, [x], w, ex), Nat.is_eq(Prefer.ownerOf(grammar, ex), z), trig, own)
      +wSpan = G.path_eq_sound(w, span, isB)
      +lk2 = Equal.trans(Bool, linkedFrom(rest, z, s, grammar, input, w), linkedFrom(rest, z, s, grammar, input, span), True{}, Equal.cong(+List<Nat>, Bool, v => linkedFrom(rest, z, s, grammar, input, v), w, span, wSpan), lk)
      Lemma.and_true_intro(anyLink(s, grammar, input, x, z, w), linkedFrom(rest, z, s, grammar, input, w), any_link_of_member(s, grammar, input, x, z, w, ex, mX, l), lk2)
    case False{} _:
      {==}

# ======== THE COMPLETION OF A SELECTED NODE IS KEPT ========

# The sibling a removal's check found, with its certificate.
def ProdCert(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +s: +List<Spec.Bsr>, +ks: +List<Spec.Bsr>, +x: Nat, +q: Nat, +i: Nat, +j: Nat) -> Type:
  &m: Nat -> {Prefer.prodCand(grammar, marks, x, q, m) == True{} : Bool} & {Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j) == True{} : Bool}

def AltCert(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +s: +List<Spec.Bsr>, +ks: +List<Spec.Bsr>, +index: Nat, +rb: +List<Nat>, +a: Nat, +alts: +List<+List<Spec.Item>>, +i: Nat, +j: Nat, +n: Nat) -> Type:
  &m: Nat -> {Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m) == True{} : Bool} & {Nat.is_lt(m, n) == True{} : Bool} & {Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j) == True{} : Bool}

law prod_cert_pick:
  for +m: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +x: Nat
  for +q: Nat
  for +i: Nat
  for +j: Nat
  for cases: Either<{Bool.and(Prefer.prodCand(grammar, marks, x, q, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j)) == True{} : Bool}, {Prefer.certAnyProd(m, fuel, grammar, marks, input, s, ks, x, q, i, j) == True{} : Bool}>
  for ih: {Prefer.certAnyProd(m, fuel, grammar, marks, input, s, ks, x, q, i, j) == True{} : Bool} -> ProdCert(fuel, grammar, marks, input, s, ks, x, q, i, j)
  ProdCert(fuel, grammar, marks, input, s, ks, x, q, i, j)

def prod_cert_pick(m, fuel, grammar, marks, input, s, ks, x, q, i, j, cases, ih):
  match cases:
    case Inl{both0}:
      +both = {both0 : {Bool.and(Prefer.prodCand(grammar, marks, x, q, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j)) == True{} : Bool}}
      (m, (Lemma.and_true_left(Prefer.prodCand(grammar, marks, x, q, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j), both), Lemma.and_true_right_side(Prefer.prodCand(grammar, marks, x, q, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j), both)))
    case Inr{later}:
      ih(later)

law cert_any_prod:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +x: Nat
  for +q: Nat
  for +i: Nat
  for +j: Nat
  for e: {Prefer.certAnyProd(n, fuel, grammar, marks, input, s, ks, x, q, i, j) == True{} : Bool}
  ProdCert(fuel, grammar, marks, input, s, ks, x, q, i, j)

def cert_any_prod(n, fuel, grammar, marks, input, s, ks, x, q, i, j, e):
  match n:
    case 0n:
      Empty.absurd(ProdCert(fuel, grammar, marks, input, s, ks, x, q, i, j), Lemma.false_is_not_true(e))
    case 1n+(+m):
      prod_cert_pick(m, fuel, grammar, marks, input, s, ks, x, q, i, j, Lemma.or_true_cases(Bool.and(Prefer.prodCand(grammar, marks, x, q, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneProd{q}, m, i, j)), Prefer.certAnyProd(m, fuel, grammar, marks, input, s, ks, x, q, i, j), e),
        later => cert_any_prod(m, fuel, grammar, marks, input, s, ks, x, q, i, j, later))

law alt_cert_lift:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +index: Nat
  for +rb: +List<Nat>
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +j: Nat
  for +m: Nat
  for pc: AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, m)
  AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, 1n+m)

def alt_cert_lift(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, m, pc):
  match pc:
    case (w0, (cand, (lt, cOk))):
      +w = {w0 : Nat}
      (w, (cand, (lt_succ_right(w, m, lt), cOk)))

law alt_cert_pick:
  for +m: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +index: Nat
  for +rb: +List<Nat>
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +j: Nat
  for cases: Either<{Bool.and(Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j)) == True{} : Bool}, {Prefer.certAnyAlt(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j) == True{} : Bool}>
  for ih: {Prefer.certAnyAlt(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j) == True{} : Bool} -> AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, m)
  AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, 1n+m)

def alt_cert_pick(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, cases, ih):
  match cases:
    case Inl{both0}:
      +both = {both0 : {Bool.and(Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j)) == True{} : Bool}}
      (m, (Lemma.and_true_left(Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j), both), (lt_succ_self(m), Lemma.and_true_right_side(Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j), both))))
    case Inr{later}:
      alt_cert_lift(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, m, ih(later))

law cert_any_alt:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +index: Nat
  for +rb: +List<Nat>
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +i: Nat
  for +j: Nat
  for e: {Prefer.certAnyAlt(n, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j) == True{} : Bool}
  AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, n)

def cert_any_alt(n, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, e):
  match n:
    case 0n:
      Empty.absurd(AltCert(fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, 0n), Lemma.false_is_not_true(e))
    case 1n+(+m):
      alt_cert_pick(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, Lemma.or_true_cases(Bool.and(Prefer.altCand(marks, index, Gll.reverseOnto(rb, []), a, m), Prefer.certOk(fuel, grammar, input, s, ks, Prefer.DoneAlt{index, rb, a, alts}, m, i, j)), Prefer.certAnyAlt(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j), e),
        later => cert_any_alt(m, fuel, grammar, marks, input, s, ks, index, rb, a, alts, i, j, later))

# ======== A CERTIFICATE'S FOREST IS ADMISSIBLE ========

law kept_all_sub:
  for xs: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +h: {Spec.allIn(xs, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Spec.allIn(xs, s) == True{} : Bool}

def kept_all_sub(xs, s, fuel, grammar, gm, marks, input, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +ks = Unb.kept(s, fuel, grammar, gm, marks, input)
      Lemma.and_true_intro(Spec.bsrMember(x, s), Spec.allIn(rest, s), kept_sub(s, fuel, grammar, gm, marks, input, x, Lemma.and_true_left(Spec.bsrMember(x, ks), Spec.allIn(rest, ks), h)), kept_all_sub(rest, s, fuel, grammar, gm, marks, input, Lemma.and_true_right_side(Spec.bsrMember(x, ks), Spec.allIn(rest, ks), h)))

# Steps of the kept set are judged by the guard oracle: they are in its set.
law kept_guarded:
  for +xs: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +h: {Spec.allIn(xs, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Spec.allIn(xs, Guard.guardKept(s0, fuel, grammar, gm, input)) == True{} : Bool}

def kept_guarded(xs, s, s0, fuel, grammar, gm, marks, input, gEq, h):
  Equal.trans(Bool, Spec.allIn(xs, Guard.guardKept(s0, fuel, grammar, gm, input)), Spec.allIn(xs, s), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(xs, v), Guard.guardKept(s0, fuel, grammar, gm, input), s, gEq), kept_all_sub(xs, s, fuel, grammar, gm, marks, input, h))

law leaves_of_ok:
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +c: +List<Nat>
  for +wTok: +List<Nat>
  for +w: +List<Nat>
  for +f: +List<Spec.Tree>
  for +ok: {Prefer.forestOk(grammar, items, c, wTok, f) == True{} : Bool}
  for +tEq: {wTok == w : +List<Nat>}
  {Spec.leaves(f) == w : +List<Nat>}

def leaves_of_ok(grammar, items, c, wTok, w, f, ok, tEq):
  +eqL = Gll.natsEq(Spec.leaves(f), wTok)
  +rv = Spec.revisits(grammar, f, c, wTok)
  +rest = Lemma.and_true_right_side(Spec.fits(f, grammar, items), Bool.and(eqL, Bool.not(rv)), ok)
  Equal.trans(+List<Nat>, Spec.leaves(f), wTok, w, G.nats_eq_sound(Spec.leaves(f), wTok, Lemma.and_true_left(eqL, Bool.not(rv), rest)), tEq)

law node_cert:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +who: Nat
  for parts: CertParts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for +cand: {Prefer.prodCand(grammar, marks, Spec.lhsOf(grammar, q), q, who) == True{} : Bool}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs) -> Empty
  Empty

def node_cert(fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, who, parts, cand, xsIn, notRival):
  match parts:
    case (natX0, (closed0, (f0, fOk0))):
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +f = {f0 : +List<Spec.Tree>}
      +c = certC(grammar, input, s, Prefer.DoneProd{q}, k, end)
      +wT = Prefer.tokensFrom(input, k, end)
      +fOkA = {fOk0 : {Prefer.rivalOk(Prefer.DoneProd{q}, grammar, Unb.kept(s, fuel, grammar, gm, marks, input), who, k, Spec.rhsOf(grammar, who), c, wT, f) == True{} : Bool}}
      +w = Spec.leaves(ch)
      +tEq = Sub.tokens_spelled(input, k, w, sp)
      +lhsX = spec_lhs_of_is(grammar, q, x, lhsQ)
      +natX = Equal.trans(Bool, Prefer.natIn(x, c), Prefer.natIn(Spec.lhsOf(grammar, q), c), True{}, Equal.cong(Nat, Bool, v => Prefer.natIn(v, c), x, Spec.lhsOf(grammar, q), Equal.sym(Nat, Spec.lhsOf(grammar, q), x, lhsX)), natX0)
      +closedW = Equal.trans(Bool, Prefer.closedFor(s, grammar, input, c, w), Prefer.closedFor(s, grammar, input, c, wT), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.closedFor(s, grammar, input, c, v), w, wT, Equal.sym(+List<Nat>, wT, w, tEq)), closed0)
      +sub = xsIn(c, closedW, natX)
      +fOk = Lemma.and_true_left(Prefer.forestOk(grammar, Spec.rhsOf(grammar, who), c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneProd{q}, who, k, f), Unb.kept(s, fuel, grammar, gm, marks, input)), fOkA)
      +ks = Unb.kept(s, fuel, grammar, gm, marks, input)
      +items = Spec.rhsOf(grammar, who)
      +allK = Lemma.and_true_right_side(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Spec.walk(f, False{}, who, [], 0n, k, k), ks), fOkA)
      +allG = kept_guarded(Spec.walk(f, False{}, who, [], 0n, k, k), s, s0, fuel, grammar, gm, marks, input, gEq, allK)
      +fitF = Lemma.and_true_left(Spec.fits(f, grammar, items), Bool.and(Gll.natsEq(Spec.leaves(f), wT), Bool.not(Spec.revisits(grammar, f, c, wT))), fOk)
      +lv = leaves_of_ok(grammar, items, c, wT, w, f, fOk, tEq)
      +eqA = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f), w, lv)
      +posF = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, w, after), Lemma.dropN(k, input), eqA, pos)
      adm = PG.adm_walk(f, False{}, grammar, gm, input, fuel, s0, who, [], [], 0n, k, k, items, Spec.Group{}, [], after, {==}, posF, ({==}, (fitF, allG)))
      holds0 = PG.owner_holds(PG.OProd{}, fuel, grammar, gm, input, who, [], {==}, {==}, s0, f, k, after, posF, fitF, allG)
      holds = PG.hold_fwd(grammar, Spec.prodGuards(gm, who), items, f, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, w, after), eqA, holds0)
      der = derives_once_of(grammar, gm, items, c, wT, w, xs, f, fOk, tEq, sub, Spec.prodGuards(gm, who), who, [], after, holds, adm)
      +cond = Equal.trans(Bool, Prefer.prodCand(grammar, marks, x, q, who), Prefer.prodCand(grammar, marks, Spec.lhsOf(grammar, q), q, who), True{}, Equal.cong(Nat, Bool, v => Prefer.prodCand(grammar, marks, v, q, who), x, Spec.lhsOf(grammar, q), Equal.sym(Nat, Spec.lhsOf(grammar, q), x, lhsX)), cand)
      notRival((who, (cond, der)))

law node_cert_any:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for pc: ProdCert(fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs) -> Empty
  Empty

def node_cert_any(fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, pc, xsIn, notRival):
  match pc:
    case (m0, (cand, cOk)):
      +m = {m0 : Nat}
      node_cert(fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, m, cert_parts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, m, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), cOk), cand, xsIn, notRival)

law node_encl_case:
  for v: Prefer.Verdict
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +piv: Nat
  for +mS: {Spec.bsrMember(Spec.at(q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), s) == True{} : Bool}
  for +isV: {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == v : Prefer.Verdict}
  for +vOk2: {Prefer.verdictOk(Unb.verdictFor(Prefer.DoneProd{q}, fuel, grammar, gm, marks, input, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs) -> Empty
  {Spec.bsrMember(Spec.at(q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def node_encl_case(v, fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, piv, mS, isV, vOk2, xsIn, notRival):
  match v:
    case Prefer.Keep{}:
    +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
    +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
    +y = Spec.at(q, [], n, k, piv, end)
    +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
      +dp = done_prod(grammar, q, n, {==})
      +e1 = Equal.cong(Prefer.Done, Bool, vv => Prefer.isKeep(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end)), Prefer.doneAt([n], grammar, q), Prefer.DoneProd{q}, dp)
      +e2 = Equal.cong(Prefer.Verdict, Bool, vv => Prefer.isKeep(vv), pv, Prefer.Keep{}, isV)
      kept_of(s, fuel, grammar, gm, marks, input, y, mS, Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.doneAt([n], grammar, q), fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(pv), True{}, e1, e2))
    case Prefer.Remove{+who}:
    +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
    +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
    +y = Spec.at(q, [], n, k, piv, end)
    +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
      +vc = Equal.trans(Bool, Prefer.verdictOk(Prefer.Remove{who}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(pv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.Remove{who}, pv, Equal.sym(Prefer.Verdict, pv, Prefer.Remove{who}, isV)), vOk2)
      Empty.absurd({Spec.bsrMember(y, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, node_cert_any(fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, cert_any_prod(List.length(&2, Spec.Production, grammar), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Spec.lhsOf(grammar, q), q, k, end, vc), xsIn, notRival))
    case Prefer.Unsure{}:
    +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
    +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
    +y = Spec.at(q, [], n, k, piv, end)
    +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
      +vu = Equal.trans(Bool, Prefer.verdictOk(Prefer.Unsure{}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(pv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.Unsure{}, pv, Equal.sym(Prefer.Verdict, pv, Prefer.Unsure{}, isV)), vOk2)
      Empty.absurd({Spec.bsrMember(y, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(vu))

law node_encl_at:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +piv: Nat
  for +mS: {Spec.bsrMember(Spec.at(q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), s) == True{} : Bool}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs) -> Empty
  {Spec.bsrMember(Spec.at(q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def node_encl_at(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, x, q, ch, k, lhsQ, sp, xs, after, pos, piv, mS, xsIn, notRival):
  +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
  +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
  +y = Spec.at(q, [], n, k, piv, end)
  +d0 = Prefer.doneAt([n], grammar, q)
  +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
  +vOk = Lemma.and_true_right_side(Prefer.groupedAt([n], grammar, q), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), ok)
  +dp = done_prod(grammar, q, n, {==})
  +vOk2 = Equal.trans(Bool, Prefer.verdictOk(Unb.verdictFor(Prefer.DoneProd{q}, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), True{}, Equal.cong(Prefer.Done, Bool, vv => Prefer.verdictOk(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), vv, k, end), Prefer.DoneProd{q}, d0, Equal.sym(Prefer.Done, d0, Prefer.DoneProd{q}, dp)), vOk)
  node_encl_case(Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end), fuel, grammar, gm, marks, input, s, s0, gEq, x, q, ch, k, lhsQ, sp, xs, after, pos, piv, mS, {==}, vOk2, xsIn, notRival)

# The completion of a node with no rival is kept.
law node_encl:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(x, c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.ProdRival(grammar, gm, marks, x, q, Spec.leaves(ch), after, xs) -> Empty
  Encl(grammar, gm, marks, input, fuel, s, q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))

def node_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, x, q, ch, k, lhsQ, sp, xs, after, pos, xsIn, notRival):
  +piv => +mS => node_encl_at(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, x, q, ch, k, lhsQ, sp, xs, after, pos, piv, mS, xsIn, notRival)

law adm_pre_tr:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +f: +List<Spec.Tree>
  for +items: +List<Spec.Item>
  for +idx: Nat
  for +p1: +List<Nat>
  for +p2: +List<Nat>
  for +eq: {p1 == p2 : +List<Nat>}
  for +after: +List<Nat>
  for h: Spec.Admissible(grammar, gm, f, items, idx, p2, 0n, after)
  Spec.Admissible(grammar, gm, f, items, idx, p1, 0n, after)

def adm_pre_tr(grammar, gm, f, items, idx, p1, p2, eq, after, h):
  %Equal.sym(+List<Nat>, p1, p2, eq) : Spec.Admissible(grammar, gm, f, items, idx, _, 0n, after)
  h

law pick_cert:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +who: Nat
  for parts: CertParts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for +cand: {Prefer.altCand(marks, index, Gll.reverseOnto(dot <> rpath, []), a, who) == True{} : Bool}
  for +lt: {Nat.is_lt(who, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(Spec.lhsOf(grammar, index), c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.AltRival(grammar, gm, marks, alts, index, List.append(&2, Nat, prefix, [dot]), a, Spec.leaves(ch), after, xs) -> Empty
  Empty

def pick_cert(fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, who, parts, cand, lt, xsIn, notRival):
  match parts:
    case (natX0, (closed0, (f0, fOk0))):
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +f = {f0 : +List<Spec.Tree>}
      +c = certC(grammar, input, s, Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end)
      +wT = Prefer.tokensFrom(input, k, end)
      +fOkA = {fOk0 : {Prefer.rivalOk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, grammar, Unb.kept(s, fuel, grammar, gm, marks, input), who, k, Spec.altOf(alts, who), c, wT, f) == True{} : Bool}}
      +w = Spec.leaves(ch)
      +tEq = Sub.tokens_spelled(input, k, w, sp)
      +closedW = Equal.trans(Bool, Prefer.closedFor(s, grammar, input, c, w), Prefer.closedFor(s, grammar, input, c, wT), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.closedFor(s, grammar, input, c, v), w, wT, Equal.sym(+List<Nat>, wT, w, tEq)), closed0)
      +sub = xsIn(c, closedW, natX0)
      +fOk = Lemma.and_true_left(Prefer.forestOk(grammar, Spec.altOf(alts, who), c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, f), Unb.kept(s, fuel, grammar, gm, marks, input)), fOkA)
      +path = List.append(&2, Nat, prefix, [dot])
      +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
      +ks = Unb.kept(s, fuel, grammar, gm, marks, input)
      +items = Spec.altOf(alts, who)
      +p2 = Gll.reverseOnto(dot <> rpath, [])
      +preW = List.append(&2, Nat, p2, [who])
      +wk = Spec.walk(f, False{}, index, preW, 0n, k, k)
      +allK = Lemma.and_true_right_side(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(wk, ks), fOkA)
      +allG = kept_guarded(wk, s, s0, fuel, grammar, gm, marks, input, gEq, allK)
      +fitF = Lemma.and_true_left(Spec.fits(f, grammar, items), Bool.and(Gll.natsEq(Spec.leaves(f), wT), Bool.not(Spec.revisits(grammar, f, c, wT))), fOk)
      +lv = leaves_of_ok(grammar, items, c, wT, w, f, fOk, tEq)
      +eqA = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f), w, lv)
      +posF = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, w, after), Lemma.dropN(k, input), eqA, pos)
      +pEqW = G.prefix_ext(dot <> rpath, p2, [who], {==})
      +remW = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, who), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{kind, alts}}, itemEq)
      adm0 = PG.adm_walk(f, False{}, grammar, gm, input, fuel, s0, index, who <> dot <> rpath, preW, 0n, k, k, items, Spec.Group{}, [], after, pEqW, posF, (remW, (fitF, allG)))
      +preEq = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [who]), path, p2, pathEq)
      adm = adm_pre_tr(grammar, gm, f, items, index, List.append(&2, Nat, path, [who]), preW, preEq, after, adm0)
      holds0 = PG.owner_holds(PG.OAlt{rpath, dot, who, kind, alts}, fuel, grammar, gm, input, index, preW, pEqW, itemEq, s0, f, k, after, posF, fitF, allG)
      holds1 = PG.hold_fwd(grammar, Spec.altGuards(gm, index, p2, who), items, f, List.append(&2, Nat, Spec.leaves(f), after), List.append(&2, Nat, w, after), eqA, holds0)
      holds = PG.guards_path(grammar, gm, index, path, p2, pathEq, who, items, f, List.append(&2, Nat, w, after), holds1)
      der = derives_once_of(grammar, gm, items, c, wT, w, xs, f, fOk, tEq, sub, Spec.altGuards(gm, index, path, who), index, List.append(&2, Nat, path, [who]), after, holds, adm)
      +cand2 = Equal.trans(Bool, Prefer.altCand(marks, index, path, a, who), Prefer.altCand(marks, index, Gll.reverseOnto(dot <> rpath, []), a, who), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.altCand(marks, index, v, a, who), path, Gll.reverseOnto(dot <> rpath, []), pathEq), cand)
      notRival((who, (Lemma.and_true_intro(Spec.isAlt(alts, who), Prefer.altCand(marks, index, path, a, who), lt, cand2), der)))

law pick_remove:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +piv: Nat
  for pc: AltCert(fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, +List<Spec.Item>, alts))
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(Spec.lhsOf(grammar, index), c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.AltRival(grammar, gm, marks, alts, index, List.append(&2, Nat, prefix, [dot]), a, Spec.leaves(ch), after, xs) -> Empty
  {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def pick_remove(fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, pc, xsIn, notRival):
  match pc:
    case (who0, (cand, (lt, vc))):
      +who = {who0 : Nat}
      Empty.absurd({Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, pick_cert(fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, who, cert_parts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), vc), cand, lt, xsIn, notRival))

law pick_encl_case:
  for v: Prefer.Verdict
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +piv: Nat
  for +mS: {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), s) == True{} : Bool}
  for +isV: {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == v : Prefer.Verdict}
  for +vOk2: {Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for +dEq: {Prefer.doneAt(Gll.reverseOnto(List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), [List.length(&2, Spec.Item, Spec.altOf(alts, a))]), []), grammar, index) == Prefer.DoneAlt{index, dot <> rpath, a, alts} : Prefer.Done}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(Spec.lhsOf(grammar, index), c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.AltRival(grammar, gm, marks, alts, index, List.append(&2, Nat, prefix, [dot]), a, Spec.leaves(ch), after, xs) -> Empty
  {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def pick_encl_case(v, fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, mS, isV, vOk2, dEq, xsIn, notRival):
  match v:
    case Prefer.Keep{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +y = Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, end)
      +rev = Gll.reverseOnto(List.append(&2, Nat, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), [List.length(&2, Spec.Item, Spec.altOf(alts, a))]), [])
      +e1 = Equal.cong(Prefer.Done, Bool, vv => Prefer.isKeep(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end)), Prefer.doneAt(rev, grammar, index), Prefer.DoneAlt{index, dot <> rpath, a, alts}, dEq)
      +e2 = Equal.cong(Prefer.Verdict, Bool, vv => Prefer.isKeep(vv), Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Keep{}, isV)
      kept_of(s, fuel, grammar, gm, marks, input, y, mS, Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.doneAt(rev, grammar, index), fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), True{}, e1, e2))
    case Prefer.Remove{+who}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vc = Equal.trans(Bool, Prefer.verdictOk(Prefer.Remove{who}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Remove{who}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Remove{who}, isV)), vOk2)
      pick_remove(fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, cert_any_alt(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, end, vc), xsIn, notRival)
    case Prefer.Unsure{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vu = Equal.trans(Bool, Prefer.verdictOk(Prefer.Unsure{}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Unsure{}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Unsure{}, isV)), vOk2)
      Empty.absurd({Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(vu))

law pick_encl_at:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +piv: Nat
  for +mS: {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), s) == True{} : Bool}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(Spec.lhsOf(grammar, index), c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.AltRival(grammar, gm, marks, alts, index, List.append(&2, Nat, prefix, [dot]), a, Spec.leaves(ch), after, xs) -> Empty
  {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def pick_encl_at(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, mS, xsIn, notRival):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
  +pre2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])
  +y = Spec.at(index, pre2, n, k, piv, end)
  +rev = Gll.reverseOnto(List.append(&2, Nat, pre2, [n]), [])
  +d0 = Prefer.doneAt(rev, grammar, index)
  +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
  +vOk = Lemma.and_true_right_side(Prefer.groupedAt(rev, grammar, index), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), ok)
  +assoc = G.nat_append_assoc(prefix, [dot], [a])
  +pEq2 = Equal.trans(+List<Nat>, pre2, List.append(&2, Nat, prefix, [dot, a]), Gll.reverseOnto(rpath, [dot, a]), assoc, G.prefix_ext(rpath, prefix, [dot, a], pEq))
  +revEq = R.step_rev(a <> dot <> rpath, pre2, n, pEq2)
  +da = done_alt(grammar, index, rpath, dot, a, n, kind, alts, itemEq, {==})
  +dEq = Equal.trans(Prefer.Done, d0, Prefer.doneAt(n <> a <> dot <> rpath, grammar, index), Prefer.DoneAlt{index, dot <> rpath, a, alts}, Equal.cong(+List<Nat>, Prefer.Done, vv => Prefer.doneAt(vv, grammar, index), rev, n <> a <> dot <> rpath, revEq), da)
  +vOk2 = Equal.trans(Bool, Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), True{}, Equal.cong(Prefer.Done, Bool, vv => Prefer.verdictOk(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), vv, k, end), Prefer.DoneAlt{index, dot <> rpath, a, alts}, d0, Equal.sym(Prefer.Done, d0, Prefer.DoneAlt{index, dot <> rpath, a, alts}, dEq)), vOk)
  pick_encl_case(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, gm, marks, input, s, s0, gEq, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, mS, {==}, vOk2, dEq, xsIn, notRival)

# The completion of a pick with no rival is kept.
law pick_encl:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +sp: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +xs: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for xsIn: @c: +List<Nat> -> {Prefer.closedFor(s, grammar, input, c, Spec.leaves(ch)) == True{} : Bool} -> {Prefer.natIn(Spec.lhsOf(grammar, index), c) == True{} : Bool} -> {allNatIn(xs, c) == True{} : Bool}
  for notRival: Spec.AltRival(grammar, gm, marks, alts, index, List.append(&2, Nat, prefix, [dot]), a, Spec.leaves(ch), after, xs) -> Empty
  Encl(grammar, gm, marks, input, fuel, s, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))

def pick_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, xsIn, notRival):
  +piv => +mS => pick_encl_at(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, ch, k, sp, xs, after, pos, piv, mS, xsIn, notRival)

law alt_one_keep:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +i: Nat
  for +j: Nat
  {Prefer.isKeep(Unb.altVerdict(1n, fuel, grammar, gm, marks, input, alts, index, path, 0n, i, j)) == True{} : Bool}

def alt_one_keep(fuel, grammar, gm, marks, input, alts, index, path, i, j):
  +r = Spec.altRank(marks, index, path, 0n)
  %Equal.sym(Bool, Spec.outranks(r, r), False{}, outranks_self(r)) : {Prefer.isKeep(Prefer.verdictIf(Unb.derivesIf(_, fuel, grammar, gm, Spec.altOf(alts, 0n), index, List.append(&2, Nat, path, [0n]), input, i, j), 0n, Prefer.Keep{})) == True{} : Bool}
  {==}

law round_encl_at:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +one: {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}
  for +a: Nat
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  for +piv: Nat
  for +mS: {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, prefix, [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), s) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, List.append(&2, Nat, prefix, [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def round_encl_at(fuel, grammar, gm, marks, input, s, index, m, outer, prefix, pEq, kind, alts, loopIt, one, a, isA, ch, i, k, piv, mS):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
  +pre = List.append(&2, Nat, prefix, [a])
  +y = Spec.at(index, pre, n, i, piv, end)
  +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
  +revEq = R.step_rev(a <> m <> outer, pre, n, G.prefix_ext(m <> outer, prefix, [a], pEq))
  +done = {Prefer.DoneAlt{index, m <> outer, a, alts} : Prefer.Done}
  +da = done_alt(grammar, index, outer, m, a, n, kind, alts, loopIt, {==})
  +dEq = Equal.trans(Prefer.Done, Prefer.doneAt(rev, grammar, index), Prefer.doneAt(n <> a <> m <> outer, grammar, index), done, Equal.cong(+List<Nat>, Prefer.Done, vv => Prefer.doneAt(vv, grammar, index), rev, n <> a <> m <> outer, revEq), da)
  +rp = Gll.reverseOnto(m <> outer, [])
  +la = List.length(&2, +List<Spec.Item>, alts)
  +a0 = one_alt_zero(alts, one, a, isA)
  +e1 = Equal.cong(Prefer.Done, Bool, vv => Prefer.isKeep(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, i, end)), Prefer.doneAt(rev, grammar, index), done, dEq)
  +e2 = Equal.cong(Nat, Bool, vv => Prefer.isKeep(Unb.altVerdict(vv, fuel, grammar, gm, marks, input, alts, index, rp, a, i, end)), la, 1n, one)
  +e3 = Equal.cong(Nat, Bool, vv => Prefer.isKeep(Unb.altVerdict(1n, fuel, grammar, gm, marks, input, alts, index, rp, vv, i, end)), a, 0n, a0)
  +ik = Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.doneAt(rev, grammar, index), fuel, grammar, gm, marks, input, i, end)), Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, rp, a, i, end)), True{}, e1,
    Equal.trans(Bool, Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, rp, a, i, end)), Prefer.isKeep(Unb.altVerdict(1n, fuel, grammar, gm, marks, input, alts, index, rp, a, i, end)), True{}, e2,
      Equal.trans(Bool, Prefer.isKeep(Unb.altVerdict(1n, fuel, grammar, gm, marks, input, alts, index, rp, a, i, end)), Prefer.isKeep(Unb.altVerdict(1n, fuel, grammar, gm, marks, input, alts, index, rp, 0n, i, end)), True{}, e3, alt_one_keep(fuel, grammar, gm, marks, input, alts, index, rp, i, end))))
  kept_of(s, fuel, grammar, gm, marks, input, y, mS, ik)

# The completion of a round is kept: a loop's one alternative has no rival.
law round_encl:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +one: {List.length(&2, +List<Spec.Item>, alts) == 1n : Nat}
  for +a: Nat
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  Encl(grammar, gm, marks, input, fuel, s, index, List.append(&2, Nat, prefix, [a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))

def round_encl(fuel, grammar, gm, marks, input, s, index, m, outer, prefix, pEq, kind, alts, loopIt, one, a, isA, ch, i, k):
  +piv => +mS => round_encl_at(fuel, grammar, gm, marks, input, s, index, m, outer, prefix, pEq, kind, alts, loopIt, one, a, isA, ch, i, k, piv, mS)

law one_group_nont:
  for alts: +List<+List<Spec.Item>>
  for e: {Prefer.oneGroup(alts) == True{} : Bool}
  for a: Nat
  {noNt(Spec.altOf(alts, a)) == True{} : Bool}

def one_group_nont(alts, e, a):
  match alts:
    case Nil{}:
      Empty.absurd({noNt(Spec.altOf([], a)) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{alt, rest}:
      match alt:
        case Nil{}:
          Empty.absurd({noNt(Spec.altOf([] <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Con{it, more}:
          match it:
            case Spec.Sym{sy}:
              Empty.absurd({noNt(Spec.altOf((Spec.Sym{sy} <> more) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
            case Spec.Eps{}:
              Empty.absurd({noNt(Spec.altOf((Spec.Eps{} <> more) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
            case Spec.Brack{kind, +galts}:
              match kind:
                case Spec.Group{}:
                  match more:
                    case Nil{}:
                      match rest:
                        case Nil{}:
                          match a:
                            case 0n:
                              {==}
                            case 1n+b:
                              {==}
                        case Con{r, rs}:
                          Empty.absurd({noNt(Spec.altOf([Spec.Brack{Spec.Group{}, galts}] <> r <> rs, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
                    case Con{m2, ms}:
                      Empty.absurd({noNt(Spec.altOf((Spec.Brack{Spec.Group{}, galts} <> m2 <> ms) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
                case Spec.Optional{}:
                  Empty.absurd({noNt(Spec.altOf((Spec.Brack{Spec.Optional{}, galts} <> more) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
                case Spec.Closure{}:
                  Empty.absurd({noNt(Spec.altOf((Spec.Brack{Spec.Closure{}, galts} <> more) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))
                case Spec.Positive{}:
                  Empty.absurd({noNt(Spec.altOf((Spec.Brack{Spec.Positive{}, galts} <> more) <> rest, a)) == True{} : Bool}, Lemma.false_is_not_true(e))

# ======== WHAT GOES ON TO THE REST OF A SEQUENCE ========

law tail_start:
  for start: Bool
  for +i: Nat
  for +k: Nat
  for +end: Nat
  for +span: +List<Nat>
  for +forest: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +hEnd: {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))) : Nat}
  for +hLe: {Nat.is_le(k, end) == True{} : Bool}
  for st: StartOk(start, i, k, span, forest, it <> rest)
  StartOk(start, i, end, span, ts, rest)

def tail_start(start, i, k, end, span, forest, ts, it, rest, hEnd, hLe, st):
  match start:
    case True{}:
      match st:
        case (eq, le):
          (Equal.trans(Nat, Nat.add(i, List.length(&2, Nat, span)), Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))), Nat.add(end, List.length(&2, Nat, Spec.leaves(ts))), eq, hEnd), Lemma.le_trans(i, k, end, le, hLe))
    case False{}:
      Lemma.and_true_right_side(notNt(it), noNt(rest), st)

def NodeStarts(start: Bool, +i: Nat, +k: Nat, +span: +List<Nat>, +q: Nat, +ch: +List<Spec.Tree>, +ts: +List<Spec.Tree>, +x: Nat, +rest: +List<Spec.Item>) -> Type:
  {Bool.or(Bool.not(Spec.pathEq(Spec.leaves(ch), span)), Nat.is_eq(i, k)) == True{} : Bool} & StartOk(start, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), span, ts, rest)

law node_starts:
  for start: Bool
  for +i: Nat
  for +k: Nat
  for +span: +List<Nat>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for st: StartOk(start, i, k, span, Spec.Node{q, ch} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest)
  NodeStarts(start, i, k, span, q, ch, ts, x, rest)

def node_starts(start, i, k, span, q, ch, ts, x, rest, st):
  match start:
    case True{}:
      match st:
        case (eq0, le0):
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +eq = {eq0 : {Nat.add(i, List.length(&2, Nat, span)) == Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))) : Nat}}
          +le = {le0 : {Nat.is_le(i, k) == True{} : Bool}}
          +hEnd = Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts))
          (ik_pick(Spec.pathEq(w, span), i, k, span, w, lts, {==}, eq, le),
            (Equal.trans(Nat, Nat.add(i, List.length(&2, Nat, span)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), eq, hEnd), Lemma.le_trans(i, k, end, le, Lemma.le_add_right(k, List.length(&2, Nat, w)))))
    case False{}:
      Empty.absurd(NodeStarts(False{}, i, k, span, q, ch, ts, x, rest), Lemma.false_is_not_true(st))

def SameFacts(+b: Bool, +above: +List<Nat>, +owner: Nat, +s: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +w: +List<Nat>) -> Type:
  {linked(Spec.keepAbove(b, above), s, grammar, input, w) == True{} : Bool} & {headOk(Spec.keepAbove(b, above), owner) == True{} : Bool}

# The nonterminals above a pick or a round, when it reads as much as its sequence.
law same_facts:
  for b: Bool
  for +above: +List<Nat>
  for +owner: Nat
  for +s: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +w: +List<Nat>
  for +span: +List<Nat>
  for +isB: {Spec.pathEq(w, span) == b : Bool}
  for +head: {headOk(above, owner) == True{} : Bool}
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  SameFacts(b, above, owner, s, grammar, input, w)

def same_facts(b, above, owner, s, grammar, input, w, span, isB, head, lk):
  match b:
    case True{}:
      +wSpan = G.path_eq_sound(w, span, isB)
      (Equal.trans(Bool, linked(above, s, grammar, input, w), linked(above, s, grammar, input, span), True{}, Equal.cong(+List<Nat>, Bool, v => linked(above, s, grammar, input, v), w, span, wSpan), lk), head)
    case False{}:
      ({==}, {==})

law pick_xs_in:
  for b: Bool
  for +above: +List<Nat>
  for +owner: Nat
  for +s: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +w: +List<Nat>
  for +span: +List<Nat>
  for +isB: {Spec.pathEq(w, span) == b : Bool}
  for +head: {headOk(above, owner) == True{} : Bool}
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  for +c: +List<Nat>
  for +closed: {Prefer.closedFor(s, grammar, input, c, w) == True{} : Bool}
  for +natO: {Prefer.natIn(owner, c) == True{} : Bool}
  {allNatIn(owner <> Spec.keepAbove(b, above), c) == True{} : Bool}

def pick_xs_in(b, above, owner, s, grammar, input, w, span, isB, head, lk, c, closed, natO):
  match b:
    case True{}:
      +wSpan = G.path_eq_sound(w, span, isB)
      +lk2 = Equal.trans(Bool, linked(above, s, grammar, input, w), linked(above, s, grammar, input, span), True{}, Equal.cong(+List<Nat>, Bool, v => linked(above, s, grammar, input, v), w, span, wSpan), lk)
      Lemma.and_true_intro(Prefer.natIn(owner, c), allNatIn(above, c), natO, above_in(above, owner, s, grammar, input, c, w, closed, natO, head, lk2))
    case False{}:
      Lemma.and_true_intro(Prefer.natIn(owner, c), True{}, natO, {==})

law round_group_s_last:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(m <> outer, []) : +List<Nat>}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +k: Nat
  for +allS: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), s) == True{} : Bool}
  for last: Sub.LastIn(ch, index, List.append(&2, Nat, prefix, [a]), 0n, i, k)
  {Prefer.oneGroup(alts) == True{} : Bool}

def round_group_s_last(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, allS, last):
  match last:
    case (piv0, mem):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pre = List.append(&2, Nat, prefix, [a])
      +y = Spec.at(index, pre, n, i, piv, end)
      +mS = G.ebnf_all_in_member(Spec.walk(ch, False{}, index, pre, 0n, i, k), s, y, allS, mem)
      +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
      +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
      +d = Prefer.doneAt(rev, grammar, index)
      +gr = Lemma.and_true_left(Prefer.groupedAt(rev, grammar, index), Prefer.verdictOk(Unb.verdictFor(d, fuel, grammar, gm, marks, input, i, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d, i, end), ok)
      +revEq = R.step_rev(a <> m <> outer, pre, n, G.prefix_ext(m <> outer, prefix, [a], pEq))
      +gr2 = Equal.trans(Bool, Prefer.groupedAt(n <> a <> m <> outer, grammar, index), Prefer.groupedAt(rev, grammar, index), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.groupedAt(v, grammar, index), n <> a <> m <> outer, rev, Equal.sym(+List<Nat>, rev, n <> a <> m <> outer, revEq)), gr)
      +gr3 = Equal.trans(Bool, Prefer.loopOk(Some{Spec.Brack{kind, alts}}), Prefer.loopOk(G.loopItem(grammar, index, m <> outer)), True{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Prefer.loopOk(v), Some{Spec.Brack{kind, alts}}, G.loopItem(grammar, index, m <> outer), Equal.sym(Maybe<&2, Spec.Item>, G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)), gr2)
      loop_ok_group(kind, alts, isL, gr3)

# ======== A SELECTED TREE USES ONLY KEPT STEPS ========

# What the walk needs: in a sequence, as for the other walk, and also: the forest is
# unbeaten; the nonterminals above are linked up to the owner of the sequence; where
# the sequence starts; and that the completion of the sequence is kept. In the rounds
# of a loop, the loop, its rounds unbeaten, and the nonterminals above.
def SelReady(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>, start: Bool, +n: Nat, +j: Nat) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), s) == True{} : Bool} &
        Spec.Unbeaten(grammar, gm, marks, forest, items, index, prefix, dot, above, span, after) & {linked(above, s, grammar, input, span) == True{} : Bool} & {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool} &
        StartOk(start, i, k, span, forest, items) & {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat} & {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) : Nat} & Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), s) == True{} : Bool} &
        Spec.RoundsUnbeaten(grammar, gm, marks, forest, alts, index, prefix, above, span, after) & {linked(above, s, grammar, input, span) == True{} : Bool} & {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}

def SelDone(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Type:
  {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def SelIH(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +s0: +List<Spec.Bsr>, +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @above: +List<Nat> -> @span: +List<Nat> -> @after: +List<Nat> -> @start: Bool -> @n: Nat -> @j: Nat ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> G.Spells(forest, input, k) -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> SelReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j) -> SelDone(rounds, grammar, gm, marks, input, fuel, s, forest, index, prefix, dot, i, k)

# The step of a child and the rest of the sequence: the last child hands the sequence's
# completion to `child_last`, any other goes on to the rest with it.
law seq_tail:
  for ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +t: Spec.Tree
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +hw: +List<Spec.Bsr>
  for +hwOk: {Spec.allIn(hw, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +rem: {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == it <> rest : +List<Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +mS: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), s) == True{} : Bool}
  for +spTs: G.Spells(ts, input, Sub.endOf(t, k))
  for +posTs: {List.append(&2, Nat, Spec.leaves(ts), after) == Lemma.dropN(Sub.endOf(t, k), input) : +List<Nat>}
  for +inSTs: {Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k)), s) == True{} : Bool}
  for unbTs: Spec.Unbeaten(grammar, gm, marks, ts, rest, index, prefix, 1n+dot, above, span, after)
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  for +hd: {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}
  for stTs: StartOk(start, i, Sub.endOf(t, k), span, ts, rest)
  for +nEq: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}
  for +jEq: {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))) : Nat}
  for +jEqTs: {j == Nat.add(Sub.endOf(t, k), List.length(&2, Nat, Spec.leaves(ts))) : Nat}
  for encl: Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  {Spec.allIn(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)) <> List.append(&2, Spec.Bsr, hw, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, t, it, rest, hw, hwOk, rem, restEq, fitTs, mS, spTs, posTs, inSTs, unbTs, lk, hd, stTs, nEq, jEq, jEqTs, encl, ihTs):
  match ts:
    case Nil{}:
      +y = Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k))
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +ky = child_last(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, n, nEq, j, jEq, rem, fitTs, mS, encl)
      Lemma.and_true_intro(Spec.bsrMember(y, kept), Spec.allIn(List.append(&2, Spec.Bsr, hw, []), kept), ky, G.all_in_app(hw, [], kept, hwOk, {==}))
    case Con{+t2, +ts2}:
      +end = Sub.endOf(t, k)
      +y = Spec.at(index, prefix, 1n+dot, i, k, end)
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +wTs = Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, end)
      +ky = child_mid(t2, ts2, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, rem, fitTs, mS)
      tsOk = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, above, span, after, start, n, j, pEq, spTs, posTs, (restEq, (fitTs, (inSTs, (unbTs, (lk, (hd, (stTs, (nEq, (jEqTs, encl))))))))))
      Lemma.and_true_intro(Spec.bsrMember(y, kept), Spec.allIn(List.append(&2, Spec.Bsr, hw, wTs), kept), ky, G.all_in_app(hw, wTs, kept, hwOk, tsOk))

law sel_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Leaf{k0} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k)

def sel_leaf(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, k0, ts, pEq, sp, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +y = Spec.at(index, prefix, 1n+dot, i, k, 1n+k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k)
          +mS = R.in_head(y, wTs, s, inS)
          +inSTs = R.in_tail(y, wTs, s, inS)
          +lts = Spec.leaves(ts)
          +hEnd = Equal.sym(Nat, Nat.add(1n+k, List.length(&2, Nat, lts)), Nat.add(k, 1n+List.length(&2, Nat, lts)), Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, lts)), 1n+Nat.add(k, List.length(&2, Nat, lts)), Lemma.add_succ_right(k, List.length(&2, Nat, lts))))
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts))), Nat.add(1n+k, List.length(&2, Nat, lts)), jEq, hEnd)
          stTs = tail_start(start, i, k, 1n+k, span, Spec.Leaf{k0} <> ts, ts, Spec.Sym{Spec.Terminal{t0}}, rest, hEnd, Lemma.le_succ_right(k, k, Lemma.le_refl(k)), st)
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Leaf{k0}, Spec.Sym{Spec.Terminal{t0}}, rest, [], {==}, rem, restEq, fitTs, mS, G.leaf_rest(input, k, k0, Spec.leaves(ts), sp), PG.pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), inSTs, unb, lk, hd, stTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sel_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Skip{} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Skip{} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k)

def sel_skip(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, ts, pEq, sp, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +y = Spec.at(index, prefix, 1n+dot, i, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k)
          +mS = R.in_head(y, wTs, s, inS)
          +inSTs = R.in_tail(y, wTs, s, inS)
          +lts = Spec.leaves(ts)
          +hEnd = {{==} : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) == Nat.add(k, List.length(&2, Nat, lts)) : Nat}}
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))), Nat.add(k, List.length(&2, Nat, lts)), jEq, hEnd)
          stTs = tail_start(start, i, k, k, span, Spec.Skip{} <> ts, ts, Spec.Brack{Spec.Optional{}, balts}, rest, hEnd, Lemma.le_refl(k), st)
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Skip{}, Spec.Brack{Spec.Optional{}, balts}, rest, [], {==}, rem, restEq, fitTs, mS, sp, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), inSTs, unb, lk, hd, stTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +y = Spec.at(index, prefix, 1n+dot, i, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k)
          +mS = R.in_head(y, wTs, s, inS)
          +inSTs = R.in_tail(y, wTs, s, inS)
          +lts = Spec.leaves(ts)
          +hEnd = {{==} : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) == Nat.add(k, List.length(&2, Nat, lts)) : Nat}}
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))), Nat.add(k, List.length(&2, Nat, lts)), jEq, hEnd)
          stTs = tail_start(start, i, k, k, span, Spec.Skip{} <> ts, ts, Spec.Eps{}, rest, hEnd, Lemma.le_refl(k), st)
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Skip{}, Spec.Eps{}, rest, [], {==}, rem, restEq, fitTs, mS, sp, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), inSTs, unb, lk, hd, stTs, nEq, jEq, jEqTs, encl, ihTs)

law sel_node_go:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +rem: {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
  for +inS: {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}
  for unb: Spec.Unbeaten(grammar, gm, marks, Spec.Node{q, ch} <> ts, Spec.Sym{Spec.Nonterminal{x}} <> rest, index, prefix, dot, above, span, after)
  for +lk: {linked(above, s, grammar, input, span) == True{} : Bool}
  for +hd: {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}
  for +nEq: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}
  for +jEq: {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts))) : Nat}
  for encl: Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
  for ns: NodeStarts(start, i, k, span, q, ch, ts, x, rest)
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k)

def sel_node_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, q, ch, ts, x, rest, sp, pos, rem, fit, inS, unb, lk, hd, nEq, jEq, encl, ns, ihCh, ihTs):
  match unb:
    case (nr, (unbCh, unbTs)):
      match ns:
        case (ikIf0, stTs):
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +ikIf = {ikIf0 : {Bool.or(Bool.not(Spec.pathEq(w, span)), Nat.is_eq(i, k)) == True{} : Bool}}
          +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inSCh = R.in_app_left(wCh, wTs, s, inS2)
          +inSTs = R.in_app_right(wCh, wTs, s, inS2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +tW = Sub.tokens_spelled(input, k, w, spCh)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +lhsX = spec_lhs_of_is(grammar, q, x, lhsQ)
          +b = Spec.pathEq(w, span)
          +xs = {x <> Spec.sameAbove(above, span, w) : +List<Nat>}
          enclCh = node_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, x, q, ch, k, lhsQ, spCh, xs, next, posCh,
            (+c => +cl => +nx => node_xs_in(b, grammar, gm, input, s, index, rpath, prefix, pEq, dot, i, k, end, x, above, span, w, {==}, ikIf, itemEq, tW, mS, hd, lk, c, cl, nx)), nr)
          +lkCh = node_links(b, grammar, input, s, index, rpath, prefix, pEq, dot, i, k, end, x, above, span, w, {==}, ikIf, itemEq, tW, mS, hd, lk)
          +hdCh = Equal.trans(Bool, Nat.is_eq(x, Spec.lhsOf(grammar, q)), Nat.is_eq(x, x), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(x, v), Spec.lhsOf(grammar, q), x, lhsX), Lemma.nat_eq_refl(x))
          chOk = ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, xs, w, next, True{}, List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), end, {==}, spCh, posCh, ({==}, (fitCh, (inSCh, (unbCh, (lkCh, (hdCh, (({==}, Lemma.le_refl(k)), ({==}, ({==}, enclCh))))))))))
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts)))
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, rest, wCh, chOk, rem, restEq, fitTs, mS, spTs, PG.pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos), inSTs, unbTs, lk, hd, stTs, nEq, jEq, jEqTs, encl, ihTs)

law sel_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k)

def sel_node(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, q, ch, ts, pEq, sp, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          sel_node_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, q, ch, ts, x, rest, sp, pos, rem0, fit0, inS0, unb, lk0, hd0, nEq0, jEq0, encl, node_starts(start, i, k, span, q, ch, ts, x, rest, st), ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sel_pick_go:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +item: Spec.Item
  for +rest: +List<Spec.Item>
  for +balts: +List<+List<Spec.Item>>
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +inSCh2: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, k, k), s) == True{} : Bool}
  for unbCh: Spec.Unbeaten(grammar, gm, marks, ch, Spec.altOf(balts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after))
  for +pEq2: {List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]) == Gll.reverseOnto(a <> dot <> rpath, []) : +List<Nat>}
  for +itemsEq2: {G.dropItems(0n, Gll.seqAt(grammar, index, a <> dot <> rpath)) == Spec.altOf(balts, a) : +List<Spec.Item>}
  for +nEqCh: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, a <> dot <> rpath)) == List.length(&2, Spec.Item, Spec.altOf(balts, a)) : Nat}
  for +spCh: G.Spells(ch, input, k)
  for +posCh: {List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)) == Lemma.dropN(k, input) : +List<Nat>}
  for enclCh: Encl(grammar, gm, marks, input, fuel, s, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.length(&2, Spec.Item, Spec.altOf(balts, a)), k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for sf: SameFacts(Spec.pathEq(Spec.leaves(ch), span), above, Spec.lhsOf(grammar, index), s, grammar, input, Spec.leaves(ch))
  for tail: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool} -> SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)

def sel_pick_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, a, ch, ts, item, rest, balts, fitCh, inSCh2, unbCh, pEq2, itemsEq2, nEqCh, spCh, posCh, enclCh, ihCh, sf, tail):
  match sf:
    case (lkS, hdS):
      +w = Spec.leaves(ch)
      +pre2 = List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +same = Spec.sameAbove(above, span, w)
      +next = List.append(&2, Nat, Spec.leaves(ts), after)
      chOk = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, same, w, next, True{}, List.length(&2, Spec.Item, Spec.altOf(balts, a)), end, pEq2, spCh, posCh, (itemsEq2, (fitCh, (inSCh2, (unbCh, (lkS, (hdS, (({==}, Lemma.le_refl(k)), (nEqCh, ({==}, enclCh))))))))))
      +assoc = G.nat_append_assoc(prefix, [dot], [a])
      tail(Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), kept), Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), List.append(&2, Nat, prefix, [dot, a]), pre2, Equal.sym(+List<Nat>, pre2, List.append(&2, Nat, prefix, [dot, a]), assoc)), chOk))

law sel_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)

def sel_pick(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, a, ch, ts, pEq, sp, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, ((nr, (unbCh, unbTs)), (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inSCh = R.in_app_left(wCh, wTs, s, inS2)
          +inSTs = R.in_app_right(wCh, wTs, s, inS2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +inSCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), inSCh)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, G.prefix_ext(rpath, prefix, [dot, a], pEq))
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
          +nEqCh = Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Spec.altOf(balts, a), itemsEq2)
          +b = Spec.pathEq(w, span)
          +owner = Spec.lhsOf(grammar, index)
          +same = Spec.sameAbove(above, span, w)
          +xs = {owner <> same : +List<Nat>}
          enclCh = pick_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, index, rpath, prefix, pEq, dot, a, Spec.Group{}, balts, itemEq, ch, k, spCh, xs, next, posCh,
            (+c => +cl => +nx => pick_xs_in(b, above, owner, s, grammar, input, w, span, {==}, hd, lk, c, cl, nx)), nr)
          sel_pick_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, a, ch, ts, Spec.Brack{Spec.Group{}, balts}, rest, balts, fitCh, inSCh2, unbCh, pEq2, itemsEq2, nEqCh, spCh, PG.pos_children(Spec.leaves(ch), Spec.leaves(ts), after, input, k, pos), enclCh, ihCh, same_facts(b, above, owner, s, grammar, input, w, span, {==}, hd, lk),
            seq_tail_args => seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, balts}, rest, wCh, seq_tail_args, rem, restEq, fitTs, mS, spTs, PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos), inSTs, unbTs, lk, hd,
              tail_start(start, i, k, end, span, Spec.Pick{a, ch} <> ts, ts, Spec.Brack{Spec.Group{}, balts}, rest, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts)), Lemma.le_add_right(k, List.length(&2, Nat, w)), st),
              nEq, jEq, Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts))), encl, ihTs))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, ((nr, (unbCh, unbTs)), (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wCh, wTs), s, inS)
          +inSCh = R.in_app_left(wCh, wTs, s, inS2)
          +inSTs = R.in_app_right(wCh, wTs, s, inS2)
          +spCh = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +inSCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), inSCh)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, G.prefix_ext(rpath, prefix, [dot, a], pEq))
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
          +nEqCh = Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Spec.altOf(balts, a), itemsEq2)
          +b = Spec.pathEq(w, span)
          +owner = Spec.lhsOf(grammar, index)
          +same = Spec.sameAbove(above, span, w)
          +xs = {owner <> same : +List<Nat>}
          enclCh = pick_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, index, rpath, prefix, pEq, dot, a, Spec.Optional{}, balts, itemEq, ch, k, spCh, xs, next, posCh,
            (+c => +cl => +nx => pick_xs_in(b, above, owner, s, grammar, input, w, span, {==}, hd, lk, c, cl, nx)), nr)
          sel_pick_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, a, ch, ts, Spec.Brack{Spec.Optional{}, balts}, rest, balts, fitCh, inSCh2, unbCh, pEq2, itemsEq2, nEqCh, spCh, PG.pos_children(Spec.leaves(ch), Spec.leaves(ts), after, input, k, pos), enclCh, ihCh, same_facts(b, above, owner, s, grammar, input, w, span, {==}, hd, lk),
            seq_tail_args => seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, balts}, rest, wCh, seq_tail_args, rem, restEq, fitTs, mS, spTs, PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos), inSTs, unbTs, lk, hd,
              tail_start(start, i, k, end, span, Spec.Pick{a, ch} <> ts, ts, Spec.Brack{Spec.Optional{}, balts}, rest, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts)), Lemma.le_add_right(k, List.length(&2, Nat, w)), st),
              nEq, jEq, Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts))), encl, ihTs))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sel_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihRs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, rs)
  for ihTs: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ts)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k)

def sel_loop(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, rs, ts, pEq, sp, pos, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, ((unbRs, unbTs), (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wRs, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wRs, wTs), s, inS)
          +inSRs = R.in_app_left(wRs, wTs, s, inS2)
          +inSTs = R.in_app_right(wRs, wTs, s, inS2)
          +spRs = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          rsOk = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, above, span, next, True{}, 0n, 0n, pEqL, spRs, posCh, (itemEq, ({==}, (fitRs, (inSRs, (unbRs, (lk, hd)))))))
          +hEnd = Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts))
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, hEnd)
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Loop{rs}, Spec.Brack{Spec.Closure{}, balts}, rest, wRs, rsOk, rem, restEq, fitTs, mS, spTs, PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos), inSTs, unbTs, lk, hd,
            tail_start(start, i, k, end, span, Spec.Loop{rs} <> ts, ts, Spec.Brack{Spec.Closure{}, balts}, rest, hEnd, Lemma.le_add_right(k, List.length(&2, Nat, w)), st), nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, ((unbRs, unbTs), (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) : Nat}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wRs, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wRs, wTs), s, inS)
          +inSRs = R.in_app_left(wRs, wTs, s, inS2)
          +inSTs = R.in_app_right(wRs, wTs, s, inS2)
          +spRs = G.spells_first(input, k, w, lts, sp)
          +spTs = G.spells_second(input, k, w, lts, sp)
          +next = List.append(&2, Nat, lts, after)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          rsOk = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, above, span, next, True{}, 0n, 0n, pEqL, spRs, posCh, (itemEq, ({==}, (fitRs, (inSRs, (unbRs, (lk, hd)))))))
          +hEnd = Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), G.end_split(k, w, lts))
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, w, lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, hEnd)
          seq_tail(ts, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, pEq, Spec.Loop{rs}, Spec.Brack{Spec.Positive{}, balts}, rest, wRs, rsOk, rem, restEq, fitTs, mS, spTs, PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos), inSTs, unbTs, lk, hd,
            tail_start(start, i, k, end, span, Spec.Loop{rs} <> ts, ts, Spec.Brack{Spec.Positive{}, balts}, rest, hEnd, Lemma.le_add_right(k, List.length(&2, Nat, w)), st), nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          Empty.absurd(SelDone(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law sel_nil:
  for dot: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for ready: SelReady(False{}, grammar, gm, marks, input, fuel, s, [], index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  SelDone(False{}, grammar, gm, marks, input, fuel, s, [], index, prefix, dot, i, k)

def sel_nil(dot, items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, i, k, kind, alts, above, span, after, start, n, j, ready):
  match dot:
    case 0n:
      match ready:
        case (rem0, (fit0, (inS0, (unb, (lk0, (hd0, (st, (nEq0, (jEq0, encl))))))))):
          +rem = {rem0 : {Gll.seqAt(grammar, index, rpath) == items : +List<Spec.Item>}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, 0n) : Nat}}
          +itemsNil = fits_nil_items(grammar, items, fit0)
          +seqNil = Equal.trans(+List<Spec.Item>, Gll.seqAt(grammar, index, rpath), items, [], rem, itemsNil)
          +n0 = Equal.trans(Nat, n, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)), 0n, Equal.sym(Nat, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)), n, nEq), Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.seqAt(grammar, index, rpath), [], seqNil))
          +jk = Equal.trans(Nat, j, Nat.add(k, 0n), k, jEq, Lemma.add_zero_right(k))
          +y = Spec.at(index, prefix, 0n, i, k, k)
          +y2 = Spec.at(index, prefix, n, i, k, j)
          +yEq = Equal.trans(Spec.Bsr, y2, Spec.at(index, prefix, 0n, i, k, j), y, Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, v, i, k, j), n, 0n, n0), Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, 0n, i, k, v), j, k, jk))
          +mS = R.in_head(y, [], s, inS0)
          +mS2 = Equal.trans(Bool, Spec.bsrMember(y2, s), Spec.bsrMember(y, s), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, s), y2, y, yEq), mS)
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +mK = encl(k, mS2)
          +mK2 = Equal.trans(Bool, Spec.bsrMember(y, kept), Spec.bsrMember(y2, kept), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, kept), y, y2, Equal.sym(Spec.Bsr, y2, y, yEq)), mK)
          Lemma.and_true_intro(Spec.bsrMember(y, kept), True{}, mK2, {==})
    case 1n+d:
      {==}

law sel_round_go:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pre: +List<Nat>
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, pre, 0n, i, k), s) == True{} : Bool}
  for unbCh: Spec.Unbeaten(grammar, gm, marks, ch, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(rest), after))
  for +pEqA: {pre == Gll.reverseOnto(a <> m <> outer, []) : +List<Nat>}
  for +itemsEqR: {G.dropItems(0n, Gll.seqAt(grammar, index, a <> m <> outer)) == Spec.altOf(alts, a) : +List<Spec.Item>}
  for +nEqR: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, a <> m <> outer)) == List.length(&2, Spec.Item, Spec.altOf(alts, a)) : Nat}
  for +noNtR: {noNt(Spec.altOf(alts, a)) == True{} : Bool}
  for +spCh: G.Spells(ch, input, k)
  for +posCh: {List.append(&2, Nat, Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(rest), after)) == Lemma.dropN(k, input) : +List<Nat>}
  for enclR: Encl(grammar, gm, marks, input, fuel, s, index, pre, List.length(&2, Spec.Item, Spec.altOf(alts, a)), i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for sf: SameFacts(Spec.pathEq(Spec.leaves(ch), span), above, Spec.lhsOf(grammar, index), s, grammar, input, Spec.leaves(ch))
  for +restOk: {Spec.allIn(Spec.walk(rest, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  {Spec.allIn(List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, pre, 0n, i, k), Spec.walk(rest, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def sel_round_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, m, outer, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j, a, ch, rest, pre, fitCh, inSCh, unbCh, pEqA, itemsEqR, nEqR, noNtR, spCh, posCh, enclR, ihCh, sf, restOk):
  match sf:
    case (lkS, hdS):
      +w = Spec.leaves(ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +same = Spec.sameAbove(above, span, w)
      +next = List.append(&2, Nat, Spec.leaves(rest), after)
      chOk = ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, same, w, next, False{}, List.length(&2, Spec.Item, Spec.altOf(alts, a)), end, pEqA, spCh, posCh, (itemsEqR, (fitCh, (inSCh, (unbCh, (lkS, (hdS, (noNtR, (nEqR, ({==}, enclR))))))))))
      G.all_in_app(Spec.walk(ch, False{}, index, pre, 0n, i, k), Spec.walk(rest, True{}, index, prefix, 0n, i, end), Unb.kept(s, fuel, grammar, gm, marks, input), chOk, restOk)

law sel_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(True{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  for ihCh: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, ch)
  for ihRest: SelIH(grammar, gm, marks, input, fuel, s, s0, gEq, rest)
  SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k)

def sel_round(rpath, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j, a, ch, rest, pEq, sp, pos, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, (inS0, ((nr, (unbCh, unbRest)), (lk0, hd0)))))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +lk = {lk0 : {linked(above, s, grammar, input, span) == True{} : Bool}}
          +hd = {hd0 : {headOk(above, Spec.lhsOf(grammar, index)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +inSCh = R.in_app_left(wCh, wRest, s, inS)
          +inSRest = R.in_app_right(wCh, wRest, s, inS)
          +spCh = G.spells_first(input, k, w, lr, sp)
          +spRest = G.spells_second(input, k, w, lr, sp)
          +next = List.append(&2, Nat, lr, after)
          +posCh = PG.pos_children(w, lr, after, input, k, pos)
          +posRest = PG.pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
          +oneG = round_group_s_last(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, inSCh, Sub.last_any(ch, index, pre, i, k))
          +one = one_group_len(alts, oneG)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +nEqR = Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.bracketAlt(G.loopItem(grammar, index, m <> outer), a), Spec.altOf(alts, a), itemsEqR)
          enclR = round_encl(fuel, grammar, gm, marks, input, s, index, m, outer, prefix, pEq, kind, alts, loopIt, one, a, isA, ch, i, k)
          restOk = ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, above, span, after, start, n, j, pEq, spRest, posRest, (loopIt, (isL, (fitRest, (inSRest, (unbRest, (lk, hd)))))))
          sel_round_go(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, m, outer, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j, a, ch, rest, pre, fitCh, inSCh, unbCh, pEqA, itemsEqR, nEqR, one_group_nont(alts, oneG, a), spCh, PG.pos_children(Spec.leaves(ch), Spec.leaves(rest), after, input, k, pos), enclR, ihCh, same_facts(Spec.pathEq(w, span), above, Spec.lhsOf(grammar, index), s, grammar, input, w, span, {==}, hd, lk), restOk)

law sel_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  for +start: Bool
  for +n: Nat
  for +j: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for +pos: {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for ready: SelReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j)
  SelDone(rounds, grammar, gm, marks, input, fuel, s, forest, index, prefix, dot, i, k)

def sel_walk(forest, rounds, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j, pEq, sp, pos, ready):
  match forest rounds:
    case Nil{} False{}:
      sel_nil(dot, items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, i, k, kind, alts, above, span, after, start, n, j, ready)
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      sel_leaf(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, k0, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ts, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      sel_node(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, q, ch, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ch, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ts, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      sel_pick(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, a, ch, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ch, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ts, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      sel_skip(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ts, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      sel_loop(items, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, rpath, prefix, dot, i, k, kind, alts, above, span, after, start, n, j, rs, ts, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(rs, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ts, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      sel_round(rpath, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, index, prefix, dot, i, k, items, kind, alts, above, span, after, start, n, j, a, ch, rest, pEq, sp, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(ch, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => ab => spn => af => sta => nn => jj => pe => spx => po => rd => sel_walk(rest, ri, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, ab, spn, af, sta, nn, jj, pe, spx, po, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(SelDone(True{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law top_xs_in:
  for b: Bool
  for +start: Nat
  for +c: +List<Nat>
  for +nx: {Prefer.natIn(start, c) == True{} : Bool}
  {allNatIn(start <> Spec.keepAbove(b, []), c) == True{} : Bool}

def top_xs_in(b, start, c, nx):
  match b:
    case True{}:
      Lemma.and_true_intro(Prefer.natIn(start, c), True{}, nx, {==})
    case False{}:
      Lemma.and_true_intro(Prefer.natIn(start, c), True{}, nx, {==})

law top_links:
  for b: Bool
  for +start: Nat
  for +s: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +w: +List<Nat>
  {linked(start <> Spec.keepAbove(b, []), s, grammar, input, w) == True{} : Bool}

def top_links(b, start, s, grammar, input, w):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# A unbeaten tree uses only kept steps.
law selected_kept:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for allS: {Spec.allIn(Spec.steps(tree, 0n), s) == True{} : Bool}
  for unb: Spec.Unbeaten(grammar, gm, marks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  {Spec.allIn(Spec.steps(tree, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def selected_kept(grammar, gm, marks, start, input, fuel, s, s0, gEq, okAll, tree, fitting, spelled, allS, unb):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Leaf{k}, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      match unb:
        case (nr, (unbCh, rest)):
          +both = fitting
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, both)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +w = Spec.leaves(ch)
          +spCh = G.root_spells(input, q, ch, spelled)
          +inS = {allS : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), s) == True{} : Bool}}
          +b = Spec.pathEq(w, [])
          +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
          +xs = {start <> Spec.sameAbove([], [], w) : +List<Nat>}
          +lhsX = spec_lhs_of_is(grammar, q, start, lhsQ)
          +hd = Equal.trans(Bool, Nat.is_eq(start, Spec.lhsOf(grammar, q)), Nat.is_eq(start, start), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(start, v), Spec.lhsOf(grammar, q), start, lhsX), Lemma.nat_eq_refl(start))
          encl = node_encl(fuel, grammar, gm, marks, input, s, s0, gEq, okAll, start, q, ch, 0n, lhsQ, spCh, xs, [], pos, (+c => +cl => +nx => top_xs_in(b, start, c, nx)), nr)
          sel_walk(ch, False{}, grammar, gm, marks, input, fuel, s, s0, gEq, okAll, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], xs, w, [], True{}, List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), Nat.add(0n, List.length(&2, Nat, w)), {==}, spCh, pos,
            ({==}, (fitCh, (inS, (unbCh, (top_links(b, start, s, grammar, input, w), (hd, (({==}, {==}), ({==}, ({==}, encl))))))))))
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Pick{a, ch}, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Skip{}, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Loop{rs}, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))

law embeds_back:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +okG: {Guard.allKnown(s0, fuel, grammar, gm, input) == True{} : Bool}
  for +eqE: {Exact.exactSteps(fuel, grammar, start, input) == Some{s0} : Maybe<&2, +List<Spec.Bsr>>}
  for +tree: Spec.Tree
  for +fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for both: Spec.Admissible(grammar, gm, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, gm, marks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  {Spec.allIn(Spec.steps(tree, 0n), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

def embeds_back(grammar, gm, marks, start, input, fuel, s, s0, gEq, okAll, okG, eqE, tree, fitting, spelled, both):
  match both:
    case (adm, unb):
      +inG = PG.kept_of_admissible(grammar, gm, start, input, fuel, s0, okG, eqE, tree, fitting, spelled, adm)
      +allS = Equal.trans(Bool, Spec.allIn(Spec.steps(tree, 0n), s), Spec.allIn(Spec.steps(tree, 0n), Guard.guardKept(s0, fuel, grammar, gm, input)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(Spec.steps(tree, 0n), v), s, Guard.guardKept(s0, fuel, grammar, gm, input), Equal.sym(+List<Spec.Bsr>, Guard.guardKept(s0, fuel, grammar, gm, input), s, gEq)), inG)
      selected_kept(grammar, gm, marks, start, input, fuel, s, s0, gEq, okAll, tree, fitting, spelled, allS, unb)

law embeds_with:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +keptEq: {Unb.kept(s, fuel, grammar, gm, marks, input) == set : +List<Spec.Bsr>}
  for gf: PG.GuardFacts(fuel, grammar, gm, start, input, s)
  Spec.EmbedsUnbeaten(grammar, gm, marks, start, input, set)

def embeds_with(fuel, grammar, gm, marks, start, input, set, s, okAll, keptEq, gf):
  match gf:
    case (s00, (eqE0, (okG0, gEq0))):
      +s0 = {s00 : +List<Spec.Bsr>}
      +eqE = {eqE0 : {Exact.exactSteps(fuel, grammar, start, input) == Some{s0} : Maybe<&2, +List<Spec.Bsr>>}}
      +okG = {okG0 : {Guard.allKnown(s0, fuel, grammar, gm, input) == True{} : Bool}}
      +gEq = {gEq0 : {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}}
      %keptEq : Spec.EmbedsUnbeaten(grammar, gm, marks, start, input, _)
      +tree => +fitting => +spelled =>
        (+allK => (PG.admissible_of_kept(grammar, gm, start, input, fuel, s0, tree, fitting, spelled, kept_guarded(Spec.steps(tree, 0n), s, s0, fuel, grammar, gm, marks, input, gEq, allK)), survivors(grammar, gm, marks, start, input, fuel, s, okAll, tree, fitting, spelled, allK)),
          both => embeds_back(grammar, gm, marks, start, input, fuel, s, s0, gEq, okAll, okG, eqE, tree, fitting, spelled, both))

law embeds_of:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for facts: PreferFacts(fuel, grammar, gm, marks, start, input, set)
  Spec.EmbedsUnbeaten(grammar, gm, marks, start, input, set)

def embeds_of(fuel, grammar, gm, marks, start, input, set, facts):
  match facts:
    case (s1, (eqG0, (okAll0, keptEq0))):
      +s = {s1 : +List<Spec.Bsr>}
      +eqG = {eqG0 : {Guard.guardSteps(fuel, grammar, gm, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}}
      +okAll = {okAll0 : {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
      +keptEq = {keptEq0 : {Unb.kept(s, fuel, grammar, gm, marks, input) == set : +List<Spec.Bsr>}}
      embeds_with(fuel, grammar, gm, marks, start, input, set, s, okAll, keptEq, PG.guard_found(Exact.exactSteps(fuel, grammar, start, input), fuel, grammar, gm, start, input, s, {==}, eqG))

# The law prefer_avoid_exact.
def Laws.prefer_avoid_exact(fuel, grammar, gm, marks, start, input, set, got):
  +f = fuel
  embeds_of(f, grammar, gm, marks, start, input, set, prefer_found(Guard.guardSteps(f, grammar, gm, start, input), f, grammar, gm, marks, start, input, set, {==}, got))

law end_same:
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +k: Nat
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Sub.endOf(t2, k) == Sub.endOf(t, k) : Nat}

def end_same(t, t2, k, lv):
  Equal.trans(Nat, Sub.endOf(t2, k), Nat.add(k, List.length(&2, Nat, Spec.leaves([t2]))), Sub.endOf(t, k), Sub.end_of_one(t2, k),
    Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves([t2]))), Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), Sub.endOf(t, k), Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, v)), Spec.leaves([t2]), Spec.leaves([t]), lv), Equal.sym(Nat, Sub.endOf(t, k), Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), Sub.end_of_one(t, k))))

# A repaired tree in place of t: it fits t's item, spells what t spells, and the steps
# inside it are kept.
def HeadFix(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +t: Spec.Tree, +it: Spec.Item, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +k: Nat) -> Type:
  &t2: Spec.Tree -> {Spec.fits([t2], grammar, [it]) == True{} : Bool} & {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>} & {Spec.allIn(Sub.inner(t2, index, prefix, dot, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

# A repaired forest in place of a sequence's forest.
def RepDone(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Type:
  &f2: +List<Spec.Tree> -> {Spec.fits(f2, grammar, items) == True{} : Bool} & {Spec.leaves(f2) == Spec.leaves(forest) : +List<Nat>} & {Spec.allIn(Spec.walk(f2, False{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

# Repaired rounds in place of a loop's rounds: as many, and each consuming as before.
def RoundsDone(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +alts: +List<+List<Spec.Item>>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Type:
  &f2: +List<Spec.Tree> -> {Spec.fits(f2, grammar, Spec.times(List.length(&2, Spec.Tree, f2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.leaves(f2) == Spec.leaves(forest) : +List<Nat>} &
    {List.length(&2, Spec.Tree, f2) == List.length(&2, Spec.Tree, forest) : Nat} & {Spec.allConsume(f2) == Spec.allConsume(forest) : Bool} & {Spec.allIn(Spec.walk(f2, True{}, index, prefix, dot, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}

law seq_fix2:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +t2: Spec.Tree
  for +fit2: {Spec.fits([t2], grammar, [it]) == True{} : Bool}
  for +lv2: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  for +in2: {Spec.allIn(Sub.inner(t2, index, prefix, dot, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for tail: RepDone(grammar, gm, marks, input, fuel, s, ts, rest, index, prefix, 1n+dot, i, Sub.endOf(t, k))
  for +keptY: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  RepDone(grammar, gm, marks, input, fuel, s, t <> ts, it <> rest, index, prefix, dot, i, k)

def seq_fix2(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, t, ts, it, rest, t2, fit2, lv2, in2, tail, keptY):
  match tail:
    case (ts20, (fitT, (lvT, inT))):
      +ts2 = {ts20 : +List<Spec.Tree>}
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +e = end_same(t, t2, k, lv2)
      +lvAll = Equal.trans(+List<Nat>, Spec.leaves(t2 <> ts2), List.append(&2, Nat, Spec.leaves([t2]), Spec.leaves(ts2)), Spec.leaves(t <> ts), Sub.leaves_cons(t2, ts2),
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves([t2]), Spec.leaves(ts2)), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Spec.leaves(t <> ts), Lemma.append_congr(Spec.leaves([t2]), Spec.leaves(ts2), Spec.leaves([t]), Spec.leaves(ts), lv2, lvT), Equal.sym(+List<Nat>, Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Sub.leaves_cons(t, ts))))
      +body = {Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)) <> List.append(&2, Spec.Bsr, Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k))) : +List<Spec.Bsr>}
      +okBody = Lemma.and_true_intro(Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), kept), Spec.allIn(List.append(&2, Spec.Bsr, Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k))), kept), keptY, G.all_in_app(Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k)), kept, in2, inT))
      +e1 = Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, kept), Spec.walk(t2 <> ts2, False{}, index, prefix, dot, i, k), Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t2, k)) <> List.append(&2, Spec.Bsr, Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, Sub.endOf(t2, k))), Sub.walk_cons(t2, ts2, index, prefix, dot, i, k))
      +e2 = Equal.cong(Nat, Bool, v => Spec.allIn(Spec.at(index, prefix, 1n+dot, i, k, v) <> List.append(&2, Spec.Bsr, Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, v)), kept), Sub.endOf(t2, k), Sub.endOf(t, k), e)
      +w0 = Spec.walk(t2 <> ts2, False{}, index, prefix, dot, i, k)
      +w1 = {Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t2, k)) <> List.append(&2, Spec.Bsr, Sub.inner(t2, index, prefix, dot, k), Spec.walk(ts2, False{}, index, prefix, 1n+dot, i, Sub.endOf(t2, k))) : +List<Spec.Bsr>}
      (t2 <> ts2, (Fits.fits_join(t2, ts2, grammar, it, rest, fit2, fitT), (lvAll, Equal.trans(Bool, Spec.allIn(w0, kept), Spec.allIn(w1, kept), True{}, e1, Equal.trans(Bool, Spec.allIn(w1, kept), Spec.allIn(body, kept), True{}, e2, okBody)))))

law seq_fix:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for head: HeadFix(grammar, gm, marks, input, fuel, s, t, it, index, prefix, dot, k)
  for tail: RepDone(grammar, gm, marks, input, fuel, s, ts, rest, index, prefix, 1n+dot, i, Sub.endOf(t, k))
  for +keptY: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  RepDone(grammar, gm, marks, input, fuel, s, t <> ts, it <> rest, index, prefix, dot, i, k)

def seq_fix(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, t, ts, it, rest, head, tail, keptY):
  match head:
    case (t20, (fit20, (lv20, in20))):
      +t2 = {t20 : Spec.Tree}
      seq_fix2(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, t, ts, it, rest, t2, fit20, lv20, in20, tail, keptY)

# The completion of a sequence whose choice the oracle kept is kept, from any pivot.
law encl_prod_keep:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +q: Nat
  for +k: Nat
  for +end: Nat
  for +isV: {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end) == Prefer.Keep{} : Prefer.Verdict}
  Encl(grammar, gm, marks, input, fuel, s, q, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), k, end)

def encl_prod_keep(grammar, gm, marks, input, fuel, s, q, k, end, isV):
  +n = List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))
  +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
  +e1 = Equal.cong(Prefer.Done, Bool, vv => Prefer.isKeep(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end)), Prefer.doneAt([n], grammar, q), Prefer.DoneProd{q}, done_prod(grammar, q, n, {==}))
  +e2 = Equal.cong(Prefer.Verdict, Bool, vv => Prefer.isKeep(vv), pv, Prefer.Keep{}, isV)
  +ik = Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.doneAt([n], grammar, q), fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(pv), True{}, e1, e2)
  +piv => +mS => kept_of(s, fuel, grammar, gm, marks, input, Spec.at(q, [], n, k, piv, end), mS, ik)

law encl_alt_keep:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +k: Nat
  for +end: Nat
  for +isV: {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, List.append(&2, Nat, prefix, [dot]), a, k, end) == Prefer.Keep{} : Prefer.Verdict}
  Encl(grammar, gm, marks, input, fuel, s, index, List.append(&2, Nat, prefix, [dot, a]), List.length(&2, Spec.Item, Spec.altOf(alts, a)), k, end)

def encl_alt_keep(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, kind, alts, itemEq, k, end, isV):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  +pre = List.append(&2, Nat, prefix, [dot, a])
  +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
  +revEq = R.step_rev(a <> dot <> rpath, pre, n, G.prefix_ext(rpath, prefix, [dot, a], pEq))
  +done = {Prefer.DoneAlt{index, dot <> rpath, a, alts} : Prefer.Done}
  +da = done_alt(grammar, index, rpath, dot, a, n, kind, alts, itemEq, {==})
  +dEq = Equal.trans(Prefer.Done, Prefer.doneAt(rev, grammar, index), Prefer.doneAt(n <> a <> dot <> rpath, grammar, index), done, Equal.cong(+List<Nat>, Prefer.Done, vv => Prefer.doneAt(vv, grammar, index), rev, n <> a <> dot <> rpath, revEq), da)
  +la = List.length(&2, +List<Spec.Item>, alts)
  +path = List.append(&2, Nat, prefix, [dot])
  +rp = Gll.reverseOnto(rpath, [dot])
  +e1 = Equal.cong(Prefer.Done, Bool, vv => Prefer.isKeep(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end)), Prefer.doneAt(rev, grammar, index), done, dEq)
  +e2 = Equal.cong(+List<Nat>, Bool, vv => Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, vv, a, k, end)), rp, path, Equal.sym(+List<Nat>, path, rp, G.prefix_ext(rpath, prefix, [dot], pEq)))
  +e3 = Equal.cong(Prefer.Verdict, Bool, vv => Prefer.isKeep(vv), Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, path, a, k, end), Prefer.Keep{}, isV)
  +ik = Equal.trans(Bool, Prefer.isKeep(Unb.verdictFor(Prefer.doneAt(rev, grammar, index), fuel, grammar, gm, marks, input, k, end)), Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, rp, a, k, end)), True{}, e1,
    Equal.trans(Bool, Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, rp, a, k, end)), Prefer.isKeep(Unb.altVerdict(la, fuel, grammar, gm, marks, input, alts, index, path, a, k, end)), True{}, e2, e3))
  +piv => +mS => kept_of(s, fuel, grammar, gm, marks, input, Spec.at(index, pre, n, k, piv, end), mS, ik)

law opt_rounds:
  for +b: Nat
  for +f: +List<Spec.Tree>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +lv: {Spec.leaves(f) == Spec.leaves(ch) : +List<Nat>}
  {Spec.roundsOk(Spec.Optional{}, [Spec.Pick{b, f}]) == Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]) : Bool}

def opt_rounds(b, f, a, ch, lv):
  Equal.cong(+List<Nat>, Bool, v => Bool.or(Bool.and(Bool.not(List.is_empty(&2, Nat, List.append(&2, Nat, v, []))), True{}), False{}), Spec.leaves(f), Spec.leaves(ch), lv)

law rounds_ok_same:
  for +kind: Spec.Bracket
  for +xs: +List<Spec.Tree>
  for +ys: +List<Spec.Tree>
  for +lenEq: {List.length(&2, Spec.Tree, xs) == List.length(&2, Spec.Tree, ys) : Nat}
  for +consEq: {Spec.allConsume(xs) == Spec.allConsume(ys) : Bool}
  {Spec.roundsOk(kind, xs) == Spec.roundsOk(kind, ys) : Bool}

def rounds_ok_same(kind, xs, ys, lenEq, consEq):
  +m = Spec.minRounds(kind)
  +lx = List.length(&2, Spec.Tree, xs)
  +ly = List.length(&2, Spec.Tree, ys)
  Equal.trans(Bool, Bool.and(Bool.not(Nat.is_lt(lx, m)), Bool.or(Spec.allConsume(xs), Nat.is_eq(lx, m))), Bool.and(Bool.not(Nat.is_lt(ly, m)), Bool.or(Spec.allConsume(xs), Nat.is_eq(ly, m))), Bool.and(Bool.not(Nat.is_lt(ly, m)), Bool.or(Spec.allConsume(ys), Nat.is_eq(ly, m))),
    Equal.cong(Nat, Bool, v => Bool.and(Bool.not(Nat.is_lt(v, m)), Bool.or(Spec.allConsume(xs), Nat.is_eq(v, m))), lx, ly, lenEq),
    Equal.cong(Bool, Bool, v => Bool.and(Bool.not(Nat.is_lt(ly, m)), Bool.or(v, Nat.is_eq(ly, m))), Spec.allConsume(xs), Spec.allConsume(ys), consEq))

# What the repair needs: as for the walks above, the forest's place in the grammar, that
# it fits, that its steps are in the exact set, and, in a sequence, that the sequence's
# completion is kept.
def RepReady(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +n: Nat, +j: Nat) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), s) == True{} : Bool} &
        {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat} & {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) : Nat} & Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), s) == True{} : Bool}

def RepOut(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      RepDone(grammar, gm, marks, input, fuel, s, forest, items, index, prefix, dot, i, k)
    case True{}:
      RoundsDone(grammar, gm, marks, input, fuel, s, forest, alts, index, prefix, dot, i, k)

def RepIH(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @n: Nat -> @j: Nat ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> G.Spells(forest, input, k) -> RepReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, n, j) -> RepOut(rounds, grammar, gm, marks, input, fuel, s, forest, items, index, prefix, dot, i, k, alts)

law node_keep_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for rec: RepDone(grammar, gm, marks, input, fuel, s, ch, Spec.rhsOf(grammar, q), q, [], 0n, k, k)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_keep_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, rec):
  match rec:
    case (ch20, (fit0, (lv0, in0))):
      +ch2 = {ch20 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +lv = {lv0 : {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}}
      (Spec.Node{q, ch2}, (Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q))), True{}, Lemma.and_true_intro(Spec.lhsIs(grammar, q, x), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q)), lhsQ, fit), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(ch2), Spec.leaves(ch), lv), in0)))

law node_rival_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +who: Nat
  for parts: CertParts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for +cand: {Prefer.prodCand(grammar, marks, Spec.lhsOf(grammar, q), q, who) == True{} : Bool}
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_rival_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, who, parts, cand):
  match parts:
    case (natX0, (closed0, (f0, rOk0))):
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +f = {f0 : +List<Spec.Tree>}
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +c = certC(grammar, input, s, Prefer.DoneProd{q}, k, end)
      +wT = Prefer.tokensFrom(input, k, end)
      +items = Spec.rhsOf(grammar, who)
      +rOk = {rOk0 : {Prefer.rivalOk(Prefer.DoneProd{q}, grammar, kept, who, k, items, c, wT, f) == True{} : Bool}}
      +fOk = Lemma.and_true_left(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneProd{q}, who, k, f), kept), rOk)
      +inF = Lemma.and_true_right_side(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneProd{q}, who, k, f), kept), rOk)
      +eqL = Gll.natsEq(Spec.leaves(f), wT)
      +nr = Bool.not(Spec.revisits(grammar, f, c, wT))
      +fitF = Lemma.and_true_left(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)
      +lvF = G.nats_eq_sound(Spec.leaves(f), wT, Lemma.and_true_left(eqL, nr, Lemma.and_true_right_side(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)))
      +tEq = Sub.tokens_spelled(input, k, Spec.leaves(ch), spCh)
      +lhsX = spec_lhs_of_is(grammar, q, x, lhsQ)
      +lw0 = Lemma.and_true_left(Spec.lhsIs(grammar, who, Spec.lhsOf(grammar, q)), Spec.outranks(Spec.prodRank(marks, who), Spec.prodRank(marks, q)), cand)
      +lhsW = Equal.trans(Bool, Spec.lhsIs(grammar, who, x), Spec.lhsIs(grammar, who, Spec.lhsOf(grammar, q)), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, who, v), x, Spec.lhsOf(grammar, q), Equal.sym(Nat, Spec.lhsOf(grammar, q), x, lhsX)), lw0)
      (Spec.Node{who, f}, (Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, who, x), Spec.fits(f, grammar, items)), True{}, Lemma.and_true_intro(Spec.lhsIs(grammar, who, x), Spec.fits(f, grammar, items), lhsW, fitF), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(f), Spec.leaves(ch), Equal.trans(+List<Nat>, Spec.leaves(f), wT, Spec.leaves(ch), lvF, tEq)), inF)))

law node_rival_any:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for pc: ProdCert(fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_rival_any(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, pc):
  match pc:
    case (m0, (cand, cOk)):
      +m = {m0 : Nat}
      node_rival_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, m, cert_parts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, m, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), cOk), cand)

law node_fix_case:
  for v: Prefer.Verdict
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), s) == True{} : Bool}
  for +isV: {Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == v : Prefer.Verdict}
  for +vOk2: {Prefer.verdictOk(Unb.verdictFor(Prefer.DoneProd{q}, fuel, grammar, gm, marks, input, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_fix_case(v, grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, fitCh, inSCh, isV, vOk2, ihCh):
  match v:
    case Prefer.Keep{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      encl = encl_prod_keep(grammar, gm, marks, input, fuel, s, q, k, end, isV)
      rec = ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), Spec.Group{}, [], List.length(&2, Spec.Item, Spec.rhsOf(grammar, q)), end, {==}, spCh, ({==}, (fitCh, (inSCh, ({==}, ({==}, encl))))))
      node_keep_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, rec)
    case Prefer.Remove{+who}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
      +vc = Equal.trans(Bool, Prefer.verdictOk(Prefer.Remove{who}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(pv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.Remove{who}, pv, Equal.sym(Prefer.Verdict, pv, Prefer.Remove{who}, isV)), vOk2)
      node_rival_any(grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, cert_any_prod(List.length(&2, Spec.Production, grammar), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Spec.lhsOf(grammar, q), q, k, end, vc))
    case Prefer.Unsure{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pv = Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end)
      +vu = Equal.trans(Bool, Prefer.verdictOk(Prefer.Unsure{}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(pv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.Unsure{}, pv, Equal.sym(Prefer.Verdict, pv, Prefer.Unsure{}, isV)), vOk2)
      Empty.absurd(HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k), Lemma.false_is_not_true(vu))

law node_fix_last:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), s) == True{} : Bool}
  for last: Sub.LastIn(ch, q, [], 0n, k, k)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_fix_last(grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, x, q, ch, k, lhsQ, spCh, fitCh, inSCh, last, ihCh):
  match last:
    case (piv0, mem):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +y = Spec.at(q, [], n, k, piv, end)
      +mS = G.ebnf_all_in_member(Spec.walk(ch, False{}, q, [], 0n, k, k), s, y, inSCh, mem)
      +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
      +d0 = Prefer.doneAt([n], grammar, q)
      +vOk = Lemma.and_true_right_side(Prefer.groupedAt([n], grammar, q), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), ok)
      +dp = done_prod(grammar, q, n, Fits.fits_count(ch, grammar, Spec.rhsOf(grammar, q), fitCh))
      +vOk2 = Equal.trans(Bool, Prefer.verdictOk(Unb.verdictFor(Prefer.DoneProd{q}, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneProd{q}, k, end), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), True{}, Equal.cong(Prefer.Done, Bool, vv => Prefer.verdictOk(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), vv, k, end), Prefer.DoneProd{q}, d0, Equal.sym(Prefer.Done, d0, Prefer.DoneProd{q}, dp)), vOk)
      node_fix_case(Unb.prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, k, end), grammar, gm, marks, input, fuel, s, index, prefix, dot, x, q, ch, k, lhsQ, spCh, fitCh, inSCh, {==}, vOk2, ihCh)

# A node, repaired.
law node_fix:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +x: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, k, k), s) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, index, prefix, dot, k)

def node_fix(grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, x, q, ch, k, lhsQ, spCh, fitCh, inSCh, ihCh):
  node_fix_last(grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, x, q, ch, k, lhsQ, spCh, fitCh, inSCh, Sub.last_any(ch, q, [], k, k), ihCh)

law pick_group_keep_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for rec: RepDone(grammar, gm, marks, input, fuel, s, ch, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_keep_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, rec):
  match rec:
    case (ch20, (fit0, (lv0, in0))):
      +ch2 = {ch20 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(ch2, grammar, Spec.altOf(alts, a)) == True{} : Bool}}
      +lv = {lv0 : {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}}
      (Spec.Pick{a, ch2}, (Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch2, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(ch2, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)), fit), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(ch2), Spec.leaves(ch), lv), in0)))

law pick_group_rival_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +who: Nat
  for parts: CertParts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for +lt: {Nat.is_lt(who, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_rival_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, who, parts, lt):
  match parts:
    case (natX0, (closed0, (f0, rOk0))):
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +f = {f0 : +List<Spec.Tree>}
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +c = certC(grammar, input, s, Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end)
      +wT = Prefer.tokensFrom(input, k, end)
      +items = Spec.altOf(alts, who)
      +rOk = {rOk0 : {Prefer.rivalOk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, grammar, kept, who, k, items, c, wT, f) == True{} : Bool}}
      +fOk = Lemma.and_true_left(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, f), kept), rOk)
      +inF0 = Lemma.and_true_right_side(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, f), kept), rOk)
      +eqL = Gll.natsEq(Spec.leaves(f), wT)
      +nr = Bool.not(Spec.revisits(grammar, f, c, wT))
      +fitF = Lemma.and_true_left(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)
      +lvF = G.nats_eq_sound(Spec.leaves(f), wT, Lemma.and_true_left(eqL, nr, Lemma.and_true_right_side(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)))
      +tEq = Sub.tokens_spelled(input, k, Spec.leaves(ch), spCh)
      +lvFC = Equal.trans(+List<Nat>, Spec.leaves(f), wT, Spec.leaves(ch), lvF, tEq)
      +rp = List.append(&2, Nat, Gll.reverseOnto(rpath, [dot]), [who])
      +pre = List.append(&2, Nat, prefix, [dot, who])
      +rpEq = Equal.trans(+List<Nat>, rp, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [who]), pre, Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [who]), Gll.reverseOnto(rpath, [dot]), List.append(&2, Nat, prefix, [dot]), Equal.sym(+List<Nat>, List.append(&2, Nat, prefix, [dot]), Gll.reverseOnto(rpath, [dot]), G.prefix_ext(rpath, prefix, [dot], pEq))), G.nat_append_assoc(prefix, [dot], [who]))
      +inF = Equal.trans(Bool, Spec.allIn(Spec.walk(f, False{}, index, pre, 0n, k, k), kept), Spec.allIn(Spec.walk(f, False{}, index, rp, 0n, k, k), kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(f, False{}, index, v, 0n, k, k), kept), pre, rp, Equal.sym(+List<Nat>, rp, pre, rpEq)), inF0)
      (Spec.Pick{who, f}, (Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, who), Spec.fits(f, grammar, Spec.altOf(alts, who))), True{}, Lemma.and_true_intro(Spec.isAlt(alts, who), Spec.fits(f, grammar, Spec.altOf(alts, who)), lt, fitF), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(f), Spec.leaves(ch), lvFC), inF)))

law pick_group_remove:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for pc: AltCert(fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, +List<Spec.Item>, alts))
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_remove(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, pc):
  match pc:
    case (who0, (cand, (lt, vc))):
      +who = {who0 : Nat}
      pick_group_rival_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, who, cert_parts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), vc), lt)

law pick_group_case:
  for v: Prefer.Verdict
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for +isV: {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == v : Prefer.Verdict}
  for +vOk2: {Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_case(v, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, isV, vOk2, ihCh):
  match v:
    case Prefer.Keep{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +isV2 = Equal.trans(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, List.append(&2, Nat, prefix, [dot]), a, k, end), Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Keep{}, Equal.cong(+List<Nat>, Prefer.Verdict, vv => Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, vv, a, k, end), List.append(&2, Nat, prefix, [dot]), Gll.reverseOnto(rpath, [dot]), G.prefix_ext(rpath, prefix, [dot], pEq)), isV)
      encl = encl_alt_keep(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, Spec.Group{}, alts, itemEq, k, end, isV2)
      +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, vv => Gll.bracketAlt(vv, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, alts}}, itemEq)
      +nEqCh = Equal.cong(+List<Spec.Item>, Nat, vv => List.length(&2, Spec.Item, vv), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Spec.altOf(alts, a), itemsEq2)
      +pEqPre = G.prefix_ext(rpath, prefix, [dot, a], pEq)
      rec = ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k, Spec.altOf(alts, a), Spec.Group{}, [], List.length(&2, Spec.Item, Spec.altOf(alts, a)), end, pEqPre, spCh, (itemsEq2, (Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)), (inSCh, (nEqCh, ({==}, encl))))))
      pick_group_keep_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, rec)
    case Prefer.Remove{+who}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vc = Equal.trans(Bool, Prefer.verdictOk(Prefer.Remove{who}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Remove{who}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Remove{who}, isV)), vOk2)
      pick_group_remove(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, cert_any_alt(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, end, vc))
    case Prefer.Unsure{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vu = Equal.trans(Bool, Prefer.verdictOk(Prefer.Unsure{}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Unsure{}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Unsure{}, isV)), vOk2)
      Empty.absurd(HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k), Lemma.false_is_not_true(vu))

law pick_group_last:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for last: Sub.LastIn(ch, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_last(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, last, ihCh):
  match last:
    case (piv0, mem):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pre = List.append(&2, Nat, prefix, [dot, a])
      +y = Spec.at(index, pre, n, k, piv, end)
      +mS = G.ebnf_all_in_member(Spec.walk(ch, False{}, index, pre, 0n, k, k), s, y, inSCh, mem)
      +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
      +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
      +d0 = Prefer.doneAt(rev, grammar, index)
      +vOk = Lemma.and_true_right_side(Prefer.groupedAt(rev, grammar, index), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), ok)
      +revEq = R.step_rev(a <> dot <> rpath, pre, n, G.prefix_ext(rpath, prefix, [dot, a], pEq))
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk))
      +da = done_alt(grammar, index, rpath, dot, a, n, Spec.Group{}, alts, itemEq, Fits.fits_count(ch, grammar, Spec.altOf(alts, a), fitCh))
      +dEq = Equal.trans(Prefer.Done, d0, Prefer.doneAt(n <> a <> dot <> rpath, grammar, index), Prefer.DoneAlt{index, dot <> rpath, a, alts}, Equal.cong(+List<Nat>, Prefer.Done, vv => Prefer.doneAt(vv, grammar, index), rev, n <> a <> dot <> rpath, revEq), da)
      +vOk2 = Equal.trans(Bool, Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), True{}, Equal.cong(Prefer.Done, Bool, vv => Prefer.verdictOk(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), vv, k, end), Prefer.DoneAlt{index, dot <> rpath, a, alts}, d0, Equal.sym(Prefer.Done, d0, Prefer.DoneAlt{index, dot <> rpath, a, alts}, dEq)), vOk)
      pick_group_case(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, {==}, vOk2, ihCh)

law pick_group_fix:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Group{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, alts}, index, prefix, dot, k)

def pick_group_fix(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, ihCh):
  pick_group_last(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, Sub.last_any(ch, index, List.append(&2, Nat, prefix, [dot, a]), k, k), ihCh)

law pick_optional_keep_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for rec: RepDone(grammar, gm, marks, input, fuel, s, ch, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_keep_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, rec):
  match rec:
    case (ch20, (fit0, (lv0, in0))):
      +ch2 = {ch20 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(ch2, grammar, Spec.altOf(alts, a)) == True{} : Bool}}
      +lv = {lv0 : {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}}
      (Spec.Pick{a, ch2}, (Lemma.and_true_intro(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch2}]), Spec.isAlt(alts, a)), Spec.fits(ch2, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch2}]), Spec.isAlt(alts, a)), Spec.fits(ch2, grammar, Spec.altOf(alts, a)), Lemma.and_true_intro(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch2}]), Spec.isAlt(alts, a), Equal.trans(Bool, Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch2}]), Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), True{}, opt_rounds(a, ch2, a, ch, lv), Lemma.and_true_left(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)))), Lemma.and_true_right_side(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)))), fit), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(ch2), Spec.leaves(ch), lv), in0)))

law pick_optional_rival_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +who: Nat
  for parts: CertParts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  for +lt: {Nat.is_lt(who, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_rival_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, who, parts, lt):
  match parts:
    case (natX0, (closed0, (f0, rOk0))):
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +f = {f0 : +List<Spec.Tree>}
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +c = certC(grammar, input, s, Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end)
      +wT = Prefer.tokensFrom(input, k, end)
      +items = Spec.altOf(alts, who)
      +rOk = {rOk0 : {Prefer.rivalOk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, grammar, kept, who, k, items, c, wT, f) == True{} : Bool}}
      +fOk = Lemma.and_true_left(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, f), kept), rOk)
      +inF0 = Lemma.and_true_right_side(Prefer.forestOk(grammar, items, c, wT, f), Spec.allIn(Prefer.rivalWalk(Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, f), kept), rOk)
      +eqL = Gll.natsEq(Spec.leaves(f), wT)
      +nr = Bool.not(Spec.revisits(grammar, f, c, wT))
      +fitF = Lemma.and_true_left(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)
      +lvF = G.nats_eq_sound(Spec.leaves(f), wT, Lemma.and_true_left(eqL, nr, Lemma.and_true_right_side(Spec.fits(f, grammar, items), Bool.and(eqL, nr), fOk)))
      +tEq = Sub.tokens_spelled(input, k, Spec.leaves(ch), spCh)
      +lvFC = Equal.trans(+List<Nat>, Spec.leaves(f), wT, Spec.leaves(ch), lvF, tEq)
      +rp = List.append(&2, Nat, Gll.reverseOnto(rpath, [dot]), [who])
      +pre = List.append(&2, Nat, prefix, [dot, who])
      +rpEq = Equal.trans(+List<Nat>, rp, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [who]), pre, Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [who]), Gll.reverseOnto(rpath, [dot]), List.append(&2, Nat, prefix, [dot]), Equal.sym(+List<Nat>, List.append(&2, Nat, prefix, [dot]), Gll.reverseOnto(rpath, [dot]), G.prefix_ext(rpath, prefix, [dot], pEq))), G.nat_append_assoc(prefix, [dot], [who]))
      +inF = Equal.trans(Bool, Spec.allIn(Spec.walk(f, False{}, index, pre, 0n, k, k), kept), Spec.allIn(Spec.walk(f, False{}, index, rp, 0n, k, k), kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(f, False{}, index, v, 0n, k, k), kept), pre, rp, Equal.sym(+List<Nat>, rp, pre, rpEq)), inF0)
      (Spec.Pick{who, f}, (Lemma.and_true_intro(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{who, f}]), Spec.isAlt(alts, who)), Spec.fits(f, grammar, Spec.altOf(alts, who))), True{}, Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{who, f}]), Spec.isAlt(alts, who)), Spec.fits(f, grammar, Spec.altOf(alts, who)), Lemma.and_true_intro(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{who, f}]), Spec.isAlt(alts, who), Equal.trans(Bool, Spec.roundsOk(Spec.Optional{}, [Spec.Pick{who, f}]), Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), True{}, opt_rounds(who, f, a, ch, lvFC), Lemma.and_true_left(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)))), lt), fitF), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(f), Spec.leaves(ch), lvFC), inF)))

law pick_optional_remove:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for pc: AltCert(fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, +List<Spec.Item>, alts))
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_remove(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, pc):
  match pc:
    case (who0, (cand, (lt, vc))):
      +who = {who0 : Nat}
      pick_optional_rival_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, who, cert_parts(fuel, grammar, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, who, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), vc), lt)

law pick_optional_case:
  for v: Prefer.Verdict
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for +isV: {Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == v : Prefer.Verdict}
  for +vOk2: {Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_case(v, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, isV, vOk2, ihCh):
  match v:
    case Prefer.Keep{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +isV2 = Equal.trans(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, List.append(&2, Nat, prefix, [dot]), a, k, end), Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Keep{}, Equal.cong(+List<Nat>, Prefer.Verdict, vv => Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, vv, a, k, end), List.append(&2, Nat, prefix, [dot]), Gll.reverseOnto(rpath, [dot]), G.prefix_ext(rpath, prefix, [dot], pEq)), isV)
      encl = encl_alt_keep(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, Spec.Optional{}, alts, itemEq, k, end, isV2)
      +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, vv => Gll.bracketAlt(vv, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, alts}}, itemEq)
      +nEqCh = Equal.cong(+List<Spec.Item>, Nat, vv => List.length(&2, Spec.Item, vv), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Spec.altOf(alts, a), itemsEq2)
      +pEqPre = G.prefix_ext(rpath, prefix, [dot, a], pEq)
      rec = ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k, Spec.altOf(alts, a), Spec.Group{}, [], List.length(&2, Spec.Item, Spec.altOf(alts, a)), end, pEqPre, spCh, (itemsEq2, (Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk)), (inSCh, (nEqCh, ({==}, encl))))))
      pick_optional_keep_head(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, rec)
    case Prefer.Remove{+who}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vc = Equal.trans(Bool, Prefer.verdictOk(Prefer.Remove{who}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Remove{who}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Remove{who}, isV)), vOk2)
      pick_optional_remove(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, cert_any_alt(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), index, dot <> rpath, a, alts, k, end, vc))
    case Prefer.Unsure{}:
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +vu = Equal.trans(Bool, Prefer.verdictOk(Prefer.Unsure{}, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), True{}, Equal.cong(Prefer.Verdict, Bool, vv => Prefer.verdictOk(vv, fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.Unsure{}, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Equal.sym(Prefer.Verdict, Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Prefer.Unsure{}, isV)), vOk2)
      Empty.absurd(HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k), Lemma.false_is_not_true(vu))

law pick_optional_last:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for last: Sub.LastIn(ch, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_last(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, last, ihCh):
  match last:
    case (piv0, mem):
      +piv = {piv0 : Nat}
      +n = List.length(&2, Spec.Tree, ch)
      +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
      +pre = List.append(&2, Nat, prefix, [dot, a])
      +y = Spec.at(index, pre, n, k, piv, end)
      +mS = G.ebnf_all_in_member(Spec.walk(ch, False{}, index, pre, 0n, k, k), s, y, inSCh, mem)
      +ok = step_ok_of(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), y, okAll, mS)
      +rev = Gll.reverseOnto(List.append(&2, Nat, pre, [n]), [])
      +d0 = Prefer.doneAt(rev, grammar, index)
      +vOk = Lemma.and_true_right_side(Prefer.groupedAt(rev, grammar, index), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), ok)
      +revEq = R.step_rev(a <> dot <> rpath, pre, n, G.prefix_ext(rpath, prefix, [dot, a], pEq))
      +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headOk))
      +da = done_alt(grammar, index, rpath, dot, a, n, Spec.Optional{}, alts, itemEq, Fits.fits_count(ch, grammar, Spec.altOf(alts, a), fitCh))
      +dEq = Equal.trans(Prefer.Done, d0, Prefer.doneAt(n <> a <> dot <> rpath, grammar, index), Prefer.DoneAlt{index, dot <> rpath, a, alts}, Equal.cong(+List<Nat>, Prefer.Done, vv => Prefer.doneAt(vv, grammar, index), rev, n <> a <> dot <> rpath, revEq), da)
      +vOk2 = Equal.trans(Bool, Prefer.verdictOk(Unb.verdictFor(Prefer.DoneAlt{index, dot <> rpath, a, alts}, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), Prefer.DoneAlt{index, dot <> rpath, a, alts}, k, end), Prefer.verdictOk(Unb.verdictFor(d0, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), d0, k, end), True{}, Equal.cong(Prefer.Done, Bool, vv => Prefer.verdictOk(Unb.verdictFor(vv, fuel, grammar, gm, marks, input, k, end), fuel, grammar, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input), vv, k, end), Prefer.DoneAlt{index, dot <> rpath, a, alts}, d0, Equal.sym(Prefer.Done, d0, Prefer.DoneAlt{index, dot <> rpath, a, alts}, dEq)), vOk)
      pick_optional_case(Unb.altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(dot <> rpath, []), a, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, {==}, vOk2, ihCh)

law pick_optional_fix:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +a: Nat
  for +alts: +List<+List<Spec.Item>>
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +headOk: {Spec.fits([Spec.Pick{a, ch}], grammar, [Spec.Brack{Spec.Optional{}, alts}]) == True{} : Bool}
  for +spCh: {Spec.leaves(ch) == Lemma.slice(input, k, List.length(&2, Nat, Spec.leaves(ch))) : +List<Nat>}
  for +inSCh: {Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), s) == True{} : Bool}
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, alts}, index, prefix, dot, k)

def pick_optional_fix(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, ihCh):
  pick_optional_last(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, alts, itemEq, ch, k, headOk, spCh, inSCh, Sub.last_any(ch, index, List.append(&2, Nat, prefix, [dot, a]), k, k), ihCh)

law loop_closure_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +balts: +List<+List<Spec.Item>>
  for +rs: +List<Spec.Tree>
  for +old: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for rec: RoundsDone(grammar, gm, marks, input, fuel, s, rs, balts, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Loop{rs}, Spec.Brack{Spec.Closure{}, balts}, index, prefix, dot, k)

def loop_closure_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, k, balts, rs, old, rec):
  match rec:
    case (rs20, (fit0, (lv0, (len0, (cons0, in0))))):
      +rs2 = {rs20 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}}
      +ro = Equal.trans(Bool, Spec.roundsOk(Spec.Closure{}, rs2), Spec.roundsOk(Spec.Closure{}, rs), True{}, rounds_ok_same(Spec.Closure{}, rs2, rs, len0, cons0), old)
      (Spec.Loop{rs2}, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, rs2), Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts}))), True{}, Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, rs2), Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})), ro, fit), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(rs2), Spec.leaves(rs), lv0), in0)))

law loop_positive_head:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +balts: +List<+List<Spec.Item>>
  for +rs: +List<Spec.Tree>
  for +old: {Spec.roundsOk(Spec.Positive{}, rs) == True{} : Bool}
  for rec: RoundsDone(grammar, gm, marks, input, fuel, s, rs, balts, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
  HeadFix(grammar, gm, marks, input, fuel, s, Spec.Loop{rs}, Spec.Brack{Spec.Positive{}, balts}, index, prefix, dot, k)

def loop_positive_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, k, balts, rs, old, rec):
  match rec:
    case (rs20, (fit0, (lv0, (len0, (cons0, in0))))):
      +rs2 = {rs20 : +List<Spec.Tree>}
      +fit = {fit0 : {Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}}
      +ro = Equal.trans(Bool, Spec.roundsOk(Spec.Positive{}, rs2), Spec.roundsOk(Spec.Positive{}, rs), True{}, rounds_ok_same(Spec.Positive{}, rs2, rs, len0, cons0), old)
      (Spec.Loop{rs2}, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, rs2), Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts}))), True{}, Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, rs2), Spec.fits(rs2, grammar, Spec.times(List.length(&2, Spec.Tree, rs2), Spec.Brack{Spec.Group{}, balts})), ro, fit), {==}),
        (Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, []), Spec.leaves(rs2), Spec.leaves(rs), lv0), in0)))

# A repaired head and the rest of the sequence, repaired in turn.
law rep_seq:
  for ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +t: Spec.Tree
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for head: HeadFix(grammar, gm, marks, input, fuel, s, t, it, index, prefix, dot, k)
  for +rem: {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == it <> rest : +List<Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +mS: {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)), s) == True{} : Bool}
  for +spTs: G.Spells(ts, input, Sub.endOf(t, k))
  for +inSTs: {Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, Sub.endOf(t, k)), s) == True{} : Bool}
  for +nEq: {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}
  for +jEq: {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))) : Nat}
  for +jEqTs: {j == Nat.add(Sub.endOf(t, k), List.length(&2, Nat, Spec.leaves(ts))) : Nat}
  for encl: Encl(grammar, gm, marks, input, fuel, s, index, prefix, n, i, j)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepDone(grammar, gm, marks, input, fuel, s, t <> ts, it <> rest, index, prefix, dot, i, k)

def rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, t, it, rest, head, rem, restEq, fitTs, mS, spTs, inSTs, nEq, jEq, jEqTs, encl, ihTs):
  match ts:
    case Nil{}:
      seq_fix(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, t, [], it, rest, head, ([], (fitTs, ({==}, {==}))),
        child_last(grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, n, nEq, j, jEq, rem, fitTs, mS, encl))
    case Con{+t2, +ts2}:
      tail = ihTs(False{}, index, rpath, prefix, 1n+dot, i, Sub.endOf(t, k), rest, kind, alts, n, j, pEq, spTs, (restEq, (fitTs, (inSTs, (nEq, (jEqTs, encl))))))
      seq_fix(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, t, t2 <> ts2, it, rest, head, tail,
        child_mid(t2, ts2, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, t, it, rest, rem, fitTs, mS))

law rep_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Leaf{k0} <> ts, input, k)
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts)

def rep_leaf(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, k0, ts, pEq, sp, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = {1n+k : Nat}
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = {[] : +List<Spec.Bsr>}
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, 1n+List.length(&2, Nat, lts)), Nat.add(1n+k, List.length(&2, Nat, lts)), jEq, Lemma.add_succ_right(k, List.length(&2, Nat, lts)))
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Leaf{k0}, Spec.Sym{Spec.Terminal{t0}}, rest, (Spec.Leaf{k0}, (Fits.fits_head(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit), ({==}, {==}))), rem, restEq, fitTs, mS, G.leaf_rest(input, k, k0, Spec.leaves(ts), sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))

law rep_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Skip{} <> ts, input, k)
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts)

def rep_skip(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, ts, pEq, sp, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = k
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = {[] : +List<Spec.Bsr>}
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = jEq
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Skip{}, Spec.Brack{Spec.Optional{}, balts}, rest, (Spec.Skip{}, (Fits.fits_head(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit), ({==}, {==}))), rem, restEq, fitTs, mS, sp, inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = k
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = {[] : +List<Spec.Bsr>}
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = jEq
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Skip{}, Spec.Eps{}, rest, (Spec.Skip{}, (Fits.fits_head(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit), ({==}, {==}))), rem, restEq, fitTs, mS, sp, inSTs, nEq, jEq, jEqTs, encl, ihTs)

law rep_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts)

def rep_node(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, q, ch, ts, pEq, sp, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), G.end_split(k, Spec.leaves(ch), lts)))
          head = node_fix(grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, x, q, ch, k, Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit))), G.spells_first(input, k, Spec.leaves(ch), lts, sp), Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit))), inSIn, ihCh)
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{x}}, rest, head, rem, restEq, fitTs, mS, G.spells_second(input, k, Spec.leaves(ch), lts, sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))

law rep_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts)

def rep_pick(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, a, ch, ts, pEq, sp, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), G.end_split(k, Spec.leaves(ch), lts)))
          head = pick_group_fix(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, balts, G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem), ch, k, Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit), G.spells_first(input, k, Spec.leaves(ch), lts, sp), inSIn, ihCh)
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Pick{a, ch}, Spec.Brack{Spec.Group{}, balts}, rest, head, rem, restEq, fitTs, mS, G.spells_second(input, k, Spec.leaves(ch), lts, sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), lts))), G.end_split(k, Spec.leaves(ch), lts)))
          head = pick_optional_fix(grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, pEq, dot, a, balts, G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem), ch, k, Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit), G.spells_first(input, k, Spec.leaves(ch), lts, sp), inSIn, ihCh)
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Pick{a, ch}, Spec.Brack{Spec.Optional{}, balts}, rest, head, rem, restEq, fitTs, mS, G.spells_second(input, k, Spec.leaves(ch), lts, sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))

law rep_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihRs: RepIH(grammar, gm, marks, input, fuel, s, rs)
  for ihTs: RepIH(grammar, gm, marks, input, fuel, s, ts)
  RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts)

def rep_loop(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, rs, ts, pEq, sp, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), lts))), G.end_split(k, Spec.leaves(rs), lts)))
          head = loop_closure_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, k, balts, rs, Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit))), ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, k, k, rest, Spec.Closure{}, balts, 0n, 0n, G.prefix_ext(rpath, prefix, [dot], pEq), G.spells_first(input, k, Spec.leaves(rs), lts, sp), (G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem), ({==}, (Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit))), inSIn)))))
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Loop{rs}, Spec.Brack{Spec.Closure{}, balts}, rest, head, rem, restEq, fitTs, mS, G.spells_second(input, k, Spec.leaves(rs), lts, sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) : Nat}}
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +y = Spec.at(index, prefix, 1n+dot, i, k, end)
          +wIn = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +mS = R.in_head(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inS2 = R.in_tail(y, List.append(&2, Spec.Bsr, wIn, wTs), s, inS)
          +inSIn = R.in_app_left(wIn, wTs, s, inS2)
          +inSTs = R.in_app_right(wIn, wTs, s, inS2)
          +jEqTs = Equal.trans(Nat, j, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), lts))), Nat.add(end, List.length(&2, Nat, lts)), jEq, Equal.sym(Nat, Nat.add(end, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), lts))), G.end_split(k, Spec.leaves(rs), lts)))
          head = loop_positive_head(grammar, gm, marks, input, fuel, s, index, prefix, dot, k, balts, rs, Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit))), ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, k, k, rest, Spec.Positive{}, balts, 0n, 0n, G.prefix_ext(rpath, prefix, [dot], pEq), G.spells_first(input, k, Spec.leaves(rs), lts, sp), (G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem), ({==}, (Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit))), inSIn)))))
          rep_seq(ts, grammar, gm, marks, input, fuel, s, index, rpath, prefix, pEq, dot, i, k, kind, alts, n, j, Spec.Loop{rs}, Spec.Brack{Spec.Positive{}, balts}, rest, head, rem, restEq, fitTs, mS, G.spells_second(input, k, Spec.leaves(rs), lts, sp), inSTs, nEq, jEq, jEqTs, encl, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          Empty.absurd(RepOut(False{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))

law round_join2:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +ch2: +List<Spec.Tree>
  for +fitC: {Spec.fits(ch2, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +lvC: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for +inC: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for recRest: RoundsDone(grammar, gm, marks, input, fuel, s, rest, alts, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  RoundsDone(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, alts, index, prefix, dot, i, k)

def round_join2(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, alts, a, ch, rest, isA, ch2, fitC, lvC, inC, recRest):
  match recRest:
    case (rest20, (fitR, (lvR, (lenR, (consR, inR))))):
      +rest2 = {rest20 : +List<Spec.Tree>}
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +G0 = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +headF = Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch2, grammar, Spec.altOf(alts, a))), True{}, Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(ch2, grammar, Spec.altOf(alts, a)), isA, fitC), {==})
      +fitAll = Fits.fits_join(Spec.Pick{a, ch2}, rest2, grammar, G0, Spec.times(List.length(&2, Spec.Tree, rest2), G0), headF, fitR)
      +lvAll = Lemma.append_congr(Spec.leaves(ch2), Spec.leaves(rest2), Spec.leaves(ch), Spec.leaves(rest), lvC, lvR)
      +lenAll = Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Tree, rest2), List.length(&2, Spec.Tree, rest), lenR)
      +c1 = Equal.cong(+List<Nat>, Bool, v => Bool.and(Bool.not(List.is_empty(&2, Nat, List.append(&2, Nat, v, []))), Spec.allConsume(rest2)), Spec.leaves(ch2), Spec.leaves(ch), lvC)
      +c2 = Equal.cong(Bool, Bool, v => Bool.and(Spec.consumes(Spec.Pick{a, ch}), v), Spec.allConsume(rest2), Spec.allConsume(rest), consR)
      +consAll = Equal.trans(Bool, Bool.and(Spec.consumes(Spec.Pick{a, ch2}), Spec.allConsume(rest2)), Bool.and(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(rest2)), Bool.and(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(rest)), c1, c2)
      +inR2 = Equal.trans(Bool, Spec.allIn(Spec.walk(rest2, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), kept), Spec.allIn(Spec.walk(rest2, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(rest2, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, v))), kept), Spec.leaves(ch2), Spec.leaves(ch), lvC), inR)
      (Spec.Pick{a, ch2} <> rest2, (fitAll, (lvAll, (lenAll, (consAll, G.all_in_app(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), Spec.walk(rest2, True{}, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), kept, inC, inR2))))))

law round_join:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for recCh: RepDone(grammar, gm, marks, input, fuel, s, ch, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [a]), 0n, i, k)
  for recRest: RoundsDone(grammar, gm, marks, input, fuel, s, rest, alts, index, prefix, 0n, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
  RoundsDone(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, alts, index, prefix, dot, i, k)

def round_join(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, alts, a, ch, rest, isA, recCh, recRest):
  match recCh:
    case (ch20, (fitC, (lvC, inC))):
      +ch2 = {ch20 : +List<Spec.Tree>}
      round_join2(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, alts, a, ch, rest, isA, ch2, fitC, lvC, inC, recRest)

law rep_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for ready: RepReady(True{}, grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  for ihCh: RepIH(grammar, gm, marks, input, fuel, s, ch)
  for ihRest: RepIH(grammar, gm, marks, input, fuel, s, rest)
  RoundsDone(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, alts, index, prefix, dot, i, k)

def rep_round(rpath, grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, n, j, a, ch, rest, pEq, sp, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(RoundsDone(grammar, gm, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, alts, index, prefix, dot, i, k), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, inS0))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +inS = {inS0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +inSCh = R.in_app_left(wCh, wRest, s, inS)
          +inSRest = R.in_app_right(wCh, wRest, s, inS)
          +spCh = G.spells_first(input, k, w, lr, sp)
          +spRest = G.spells_second(input, k, w, lr, sp)
          +oneG = round_group_s_last(fuel, grammar, gm, marks, input, s, okAll, index, m, outer, prefix, pEq, kind, alts, loopIt, isL, a, ch, i, k, inSCh, Sub.last_any(ch, index, pre, i, k))
          +one = one_group_len(alts, oneG)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +nEqR = Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.bracketAlt(G.loopItem(grammar, index, m <> outer), a), Spec.altOf(alts, a), itemsEqR)
          enclR = round_encl(fuel, grammar, gm, marks, input, s, index, m, outer, prefix, pEq, kind, alts, loopIt, one, a, isA, ch, i, k)
          recCh = ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, List.length(&2, Spec.Item, Spec.altOf(alts, a)), end, pEqA, spCh, (itemsEqR, (fitCh, (inSCh, (nEqR, ({==}, enclR))))))
          recRest = ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, n, j, pEq, spRest, (loopIt, (isL, (fitRest, inSRest))))
          round_join(grammar, gm, marks, input, fuel, s, index, prefix, dot, i, k, alts, a, ch, rest, isA, recCh, recRest)

law rep_nil:
  for dot: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for ready: RepReady(False{}, grammar, gm, marks, input, fuel, s, [], index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  RepDone(grammar, gm, marks, input, fuel, s, [], items, index, prefix, dot, i, k)

def rep_nil(dot, items, grammar, gm, marks, input, fuel, s, index, rpath, prefix, i, k, kind, alts, n, j, ready):
  match dot:
    case 0n:
      match ready:
        case (rem0, (fit0, (inS0, (nEq0, (jEq0, encl))))):
          +rem = {rem0 : {Gll.seqAt(grammar, index, rpath) == items : +List<Spec.Item>}}
          +nEq = {nEq0 : {List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)) == n : Nat}}
          +jEq = {jEq0 : {j == Nat.add(k, 0n) : Nat}}
          +fit = {fit0 : {Spec.fits([], grammar, items) == True{} : Bool}}
          +itemsNil = fits_nil_items(grammar, items, fit)
          +seqNil = Equal.trans(+List<Spec.Item>, Gll.seqAt(grammar, index, rpath), items, [], rem, itemsNil)
          +n0 = Equal.trans(Nat, n, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)), 0n, Equal.sym(Nat, List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath)), n, nEq), Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Gll.seqAt(grammar, index, rpath), [], seqNil))
          +jk = Equal.trans(Nat, j, Nat.add(k, 0n), k, jEq, Lemma.add_zero_right(k))
          +y = Spec.at(index, prefix, 0n, i, k, k)
          +y2 = Spec.at(index, prefix, n, i, k, j)
          +yEq = Equal.trans(Spec.Bsr, y2, Spec.at(index, prefix, 0n, i, k, j), y, Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, v, i, k, j), n, 0n, n0), Equal.cong(Nat, Spec.Bsr, v => Spec.at(index, prefix, 0n, i, k, v), j, k, jk))
          +mS = R.in_head(y, [], s, inS0)
          +mS2 = Equal.trans(Bool, Spec.bsrMember(y2, s), Spec.bsrMember(y, s), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, s), y2, y, yEq), mS)
          +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
          +mK = encl(k, mS2)
          +mK2 = Equal.trans(Bool, Spec.bsrMember(y, kept), Spec.bsrMember(y2, kept), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, kept), y, y2, Equal.sym(Spec.Bsr, y2, y, yEq)), mK)
          ([], (fit, ({==}, Lemma.and_true_intro(Spec.bsrMember(y, kept), True{}, mK2, {==}))))
    case 1n+d:
      match ready:
        case (rem0, (fit0, more)):
          ([], (fit0, ({==}, {==})))

law rep_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +n: Nat
  for +j: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for ready: RepReady(rounds, grammar, gm, marks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, n, j)
  RepOut(rounds, grammar, gm, marks, input, fuel, s, forest, items, index, prefix, dot, i, k, alts)

def rep_walk(forest, rounds, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, items, kind, alts, n, j, pEq, sp, ready):
  match forest rounds:
    case Nil{} False{}:
      rep_nil(dot, items, grammar, gm, marks, input, fuel, s, index, rpath, prefix, i, k, kind, alts, n, j, ready)
    case Nil{} True{}:
      ([], ({==}, ({==}, ({==}, ({==}, {==})))))
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      rep_leaf(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, k0, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      rep_node(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, q, ch, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      rep_pick(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, a, ch, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      rep_skip(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      rep_loop(items, grammar, gm, marks, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, n, j, rs, ts, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(rs, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ts, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      rep_round(rpath, grammar, gm, marks, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, n, j, a, ch, rest, pEq, sp, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(rest, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(RepOut(True{}, grammar, gm, marks, input, fuel, s, Spec.Leaf{k0} <> rest, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(RepOut(True{}, grammar, gm, marks, input, fuel, s, Spec.Node{q, ch} <> rest, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(RepOut(True{}, grammar, gm, marks, input, fuel, s, Spec.Skip{} <> rest, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(RepOut(True{}, grammar, gm, marks, input, fuel, s, Spec.Loop{rs} <> rest, items, index, prefix, dot, i, k, alts), Lemma.false_is_not_true(fit0))

law steps_inner:
  for t: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for fit: {Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  {Spec.steps(t, 0n) == Sub.inner(t, 0n, [], 0n, 0n) : +List<Spec.Bsr>}

def steps_inner(t, grammar, start, fit):
  match t:
    case Spec.Leaf{kk}:
      Empty.absurd({Spec.steps(Spec.Leaf{kk}, 0n) == Sub.inner(Spec.Leaf{kk}, 0n, [], 0n, 0n) : +List<Spec.Bsr>}, Lemma.false_is_not_true(fit))
    case Spec.Node{+q, +ch}:
      {==}
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.steps(Spec.Pick{a, ch}, 0n) == Sub.inner(Spec.Pick{a, ch}, 0n, [], 0n, 0n) : +List<Spec.Bsr>}, Lemma.false_is_not_true(fit))
    case Spec.Skip{}:
      Empty.absurd({Spec.steps(Spec.Skip{}, 0n) == Sub.inner(Spec.Skip{}, 0n, [], 0n, 0n) : +List<Spec.Bsr>}, Lemma.false_is_not_true(fit))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.steps(Spec.Loop{rs}, 0n) == Sub.inner(Spec.Loop{rs}, 0n, [], 0n, 0n) : +List<Spec.Bsr>}, Lemma.false_is_not_true(fit))

law root_selected:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +start: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +spelled: {Spec.leaves([Spec.Node{q, ch}]) == input : +List<Nat>}
  for hf: HeadFix(grammar, gm, marks, input, fuel, s, Spec.Node{q, ch}, Spec.Sym{Spec.Nonterminal{start}}, 0n, [], 0n, 0n)
  Spec.SomeUnbeaten(grammar, gm, marks, start, input)

def root_selected(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, start, q, ch, spelled, hf):
  match hf:
    case (t20, (fit0, (lv0, in0))):
      +t2 = {t20 : Spec.Tree}
      +fit = {fit0 : {Spec.fits([t2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}}
      +lv = Equal.trans(+List<Nat>, Spec.leaves([t2]), Spec.leaves([Spec.Node{q, ch}]), input, lv0, spelled)
      +kept = Unb.kept(s, fuel, grammar, gm, marks, input)
      +allK = Equal.trans(Bool, Spec.allIn(Spec.steps(t2, 0n), kept), Spec.allIn(Sub.inner(t2, 0n, [], 0n, 0n), kept), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, kept), Spec.steps(t2, 0n), Sub.inner(t2, 0n, [], 0n, 0n), steps_inner(t2, grammar, start, fit)), in0)
      adm = PG.admissible_of_kept(grammar, gm, start, input, fuel, s0, t2, fit, lv, kept_guarded(Spec.steps(t2, 0n), s, s0, fuel, grammar, gm, marks, input, gEq, allK))
      (t2, ((fit, (lv, adm)), survivors(grammar, gm, marks, start, input, fuel, s, okAll, t2, fit, lv, allK)))

law safe_root:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +gEq: {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}
  for +okG: {Guard.allKnown(s0, fuel, grammar, gm, input) == True{} : Bool}
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for +start: Nat
  for +eqE: {Exact.exactSteps(fuel, grammar, start, input) == Some{s0} : Maybe<&2, +List<Spec.Bsr>>}
  for tree: Spec.Tree
  for admissible: Spec.AdmissibleTree(grammar, gm, start, input, tree)
  Spec.SomeUnbeaten(grammar, gm, marks, start, input)

def safe_root(grammar, gm, marks, input, fuel, s, s0, gEq, okG, okAll, start, eqE, tree, admissible):
  match tree:
    case Spec.Leaf{kk}:
      match admissible:
        case (fitting, rest):
          Empty.absurd(Spec.SomeUnbeaten(grammar, gm, marks, start, input), Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      match admissible:
        case (fitting, (spelled, adm)):
          +fitT = {fitting : {Spec.fits([Spec.Node{q, ch}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}}
          +sp = {spelled : {Spec.leaves([Spec.Node{q, ch}]) == input : +List<Nat>}}
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, fitT)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +spCh = G.root_spells(input, q, ch, sp)
          +inG = PG.kept_of_admissible(grammar, gm, start, input, fuel, s0, okG, eqE, Spec.Node{q, ch}, fitT, sp, adm)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)
          +inSCh = Equal.trans(Bool, Spec.allIn(wCh, s), Spec.allIn(wCh, Guard.guardKept(s0, fuel, grammar, gm, input)), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(wCh, v), s, Guard.guardKept(s0, fuel, grammar, gm, input), Equal.sym(+List<Spec.Bsr>, Guard.guardKept(s0, fuel, grammar, gm, input), s, gEq)), inG)
          root_selected(grammar, gm, marks, input, fuel, s, s0, gEq, okAll, start, q, ch, sp,
            node_fix(grammar, gm, marks, input, fuel, s, okAll, 0n, [], 0n, start, q, ch, 0n, lhsQ, spCh, fitCh, inSCh, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => nn => jj => pe => spx => rd => rep_walk(ch, ri, grammar, gm, marks, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, nn, jj, pe, spx, rd))))
    case Spec.Pick{a, ch}:
      match admissible:
        case (fitting, rest):
          Empty.absurd(Spec.SomeUnbeaten(grammar, gm, marks, start, input), Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      match admissible:
        case (fitting, rest):
          Empty.absurd(Spec.SomeUnbeaten(grammar, gm, marks, start, input), Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      match admissible:
        case (fitting, rest):
          Empty.absurd(Spec.SomeUnbeaten(grammar, gm, marks, start, input), Lemma.false_is_not_true(fitting))

law safe_with:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}
  for gf: PG.GuardFacts(fuel, grammar, gm, start, input, s)
  for tree: Spec.Tree
  for admissible: Spec.AdmissibleTree(grammar, gm, start, input, tree)
  Spec.SomeUnbeaten(grammar, gm, marks, start, input)

def safe_with(fuel, grammar, gm, marks, start, input, s, okAll, gf, tree, admissible):
  match gf:
    case (s00, (eqE0, (okG0, gEq0))):
      +s0 = {s00 : +List<Spec.Bsr>}
      +eqE = {eqE0 : {Exact.exactSteps(fuel, grammar, start, input) == Some{s0} : Maybe<&2, +List<Spec.Bsr>>}}
      +okG = {okG0 : {Guard.allKnown(s0, fuel, grammar, gm, input) == True{} : Bool}}
      +gEq = {gEq0 : {Guard.guardKept(s0, fuel, grammar, gm, input) == s : +List<Spec.Bsr>}}
      safe_root(grammar, gm, marks, input, fuel, s, s0, gEq, okG, okAll, start, eqE, tree, admissible)

law safe_of:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for facts: PreferFacts(fuel, grammar, gm, marks, start, input, set)
  for tree: Spec.Tree
  for admissible: Spec.AdmissibleTree(grammar, gm, start, input, tree)
  Spec.SomeUnbeaten(grammar, gm, marks, start, input)

def safe_of(fuel, grammar, gm, marks, start, input, set, facts, tree, admissible):
  match facts:
    case (s1, (eqG0, (okAll0, keptEq))):
      +s = {s1 : +List<Spec.Bsr>}
      +eqG = {eqG0 : {Guard.guardSteps(fuel, grammar, gm, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}}
      +okAll = {okAll0 : {Unb.allStepsOk(s, fuel, grammar, gm, marks, input, s, Unb.kept(s, fuel, grammar, gm, marks, input)) == True{} : Bool}}
      safe_with(fuel, grammar, gm, marks, start, input, s, okAll, PG.guard_found(Exact.exactSteps(fuel, grammar, start, input), fuel, grammar, gm, start, input, s, {==}, eqG), tree, admissible)

# The law prefer_avoid_safe.
def Laws.prefer_avoid_safe(fuel, grammar, gm, marks, start, input, set, got, tree, admissible):
  +f = fuel
  safe_of(f, grammar, gm, marks, start, input, set, prefer_found(Guard.guardSteps(f, grammar, gm, start, input), f, grammar, gm, marks, start, input, set, {==}, got), tree, admissible)
