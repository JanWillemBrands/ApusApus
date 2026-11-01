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
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_SUBPARSE.bend as Sub
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# THE RULES KEEP EXACTLY THE ADMISSIBLE TREES: guards_exact.
#
# Both halves walk a parse tree the way `Spec.walk` lists its steps, next to
# `Spec.Admissible`, which walks it the same way. The rules of a node are decided by the
# steps of its own sequence, its "own steps": the last one has the node's start and its
# last child's span, the first one its first child's span.
#
# A tree that uses only kept steps is admissible: every own step answered Yes, and a Yes
# is a checked answer, so every rule holds.
#
# An admissible tree uses only kept steps: its steps are in the exact set, so each was
# decided; a No would be a checked answer against a rule that holds.

# ======== WHAT THE ORACLE'S ANSWER SAYS ========

def GuardFacts(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +start: Nat, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Type:
  &s: +List<Spec.Bsr> -> {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>} & {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool} & {Guard.guardKept(s, fuel, grammar, gm, input) == set : +List<Spec.Bsr>}

law guard_both:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +eqF: {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}
  for facts: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool} & {Guard.guardKept(s, fuel, grammar, gm, input) == set : +List<Spec.Bsr>}
  GuardFacts(fuel, grammar, gm, start, input, set)

def guard_both(fuel, grammar, gm, start, input, set, s, eqF, facts):
  match facts:
    case (ok, same):
      (s, (eqF, (ok, same)))

law guard_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +eqF: {Exact.exactSteps(fuel, grammar, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Guard.guardFrom(found, fuel, grammar, gm, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  GuardFacts(fuel, grammar, gm, start, input, set)

def guard_found(found, fuel, grammar, gm, start, input, set, eqF, got):
  match found:
    case Some{+s}:
      guard_both(fuel, grammar, gm, start, input, set, s, eqF, Sub.prefer_pick_facts(Guard.allKnown(s, fuel, grammar, gm, input), Guard.guardKept(s, fuel, grammar, gm, input), set, got))
    case None{}:
      Empty.absurd(GuardFacts(fuel, grammar, gm, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# ======== THE KEPT STEPS ========

law gkept_sub_pick:
  for b: Bool
  for +e: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Spec.bsrMember(y, rest) == True{} : Bool}
  {Spec.bsrMember(y, e <> rest) == True{} : Bool}

def gkept_sub_pick(b, e, rest, ks, y, m, searchRest):
  match b:
    case True{}:
      G.member_pick(y, e, ks, e <> rest, G.ebnf_member_cases(y, e, ks, m), R.bsr_member_head(e, rest), later => R.bsr_member_cons(y, e, rest, searchRest(later)))
    case False{}:
      R.bsr_member_cons(y, e, rest, searchRest(m))

# A kept step is a step of the set.
law gkept_sub:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Guard.guardKept(es, fuel, grammar, gm, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def gkept_sub(es, fuel, grammar, gm, input, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      gkept_sub_pick(Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), e, rest, Guard.guardKept(rest, fuel, grammar, gm, input), y, m,
        later => gkept_sub(rest, fuel, grammar, gm, input, y, later))

law gkept_keep_case:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for -ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, ks) == True{} : Bool}>
  for +isB: {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}
  {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}

def gkept_keep_case(fuel, grammar, gm, input, e, ks, y, cases, isB, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, _)) == True{} : Bool}
      isB
    case Inr{later}:
      searchRest(later)

law gkept_keep_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)) == b : Bool}
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}
  {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}

def gkept_keep_pick(b, fuel, grammar, gm, input, e, isB, ks, y, m, searchRest):
  match b:
    case True{}:
      gkept_keep_case(fuel, grammar, gm, input, e, ks, y, G.ebnf_member_cases(y, e, ks, m), isB, searchRest)
    case False{}:
      searchRest(m)

# A kept step answered Yes.
law gkept_keep:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Guard.guardKept(es, fuel, grammar, gm, input)) == True{} : Bool}
  {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}

def gkept_keep(es, fuel, grammar, gm, input, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      gkept_keep_pick(Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), fuel, grammar, gm, input, e, {==}, Guard.guardKept(rest, fuel, grammar, gm, input), y, m,
        later => gkept_keep(rest, fuel, grammar, gm, input, y, later))

law gkept_of_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +isB: {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)) == b : Bool}
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +ok: {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Spec.bsrMember(y, ks) == True{} : Bool}
  {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}

def gkept_of_pick(b, fuel, grammar, gm, input, e, isB, rest, ks, y, cases, ok, searchRest):
  match cases:
    case Inl{same0}:
      +same = {same0 : {y == e : Spec.Bsr}}
      +okE = Equal.trans(Bool, Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)), True{}, Equal.cong(Spec.Bsr, Bool, v => Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, v)), e, y, Equal.sym(Spec.Bsr, y, e, same)), ok)
      +isT = Equal.trans(Bool, b, Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), True{}, Equal.sym(Bool, Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), b, isB), okE)
      %Equal.sym(Spec.Bsr, y, e, same) : {Spec.bsrMember(_, Prune.keepPick(b, e, ks)) == True{} : Bool}
      R.keep_link_head(b, isT, e, ks)
    case Inr{later}:
      R.keep_link_later(b, e, ks, y, searchRest(later))

# A step of the set that answers Yes is kept.
law gkept_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  for +ok: {Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}
  {Spec.bsrMember(y, Guard.guardKept(es, fuel, grammar, gm, input)) == True{} : Bool}

def gkept_of(es, fuel, grammar, gm, input, y, m, ok):
  match es:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, []) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      gkept_of_pick(Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, e)), fuel, grammar, gm, input, e, {==}, rest, Guard.guardKept(rest, fuel, grammar, gm, input), y, G.ebnf_member_cases(y, e, rest, m), ok,
        later => gkept_of(rest, fuel, grammar, gm, input, y, later, ok))

law known_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +okE: {Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, e)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}
  {Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}

def known_pick(fuel, grammar, gm, input, e, rest, y, cases, okE, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, _)) == True{} : Bool}
      okE
    case Inr{later}:
      searchRest(later)

# Every step of an answered set was decided.
law known_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +ok: {Guard.allKnown(es, fuel, grammar, gm, input) == True{} : Bool}
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  {Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}

def known_of(es, fuel, grammar, gm, input, ok, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      +okE = Lemma.and_true_left(Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, e)), Guard.allKnown(rest, fuel, grammar, gm, input), ok)
      +okR = Lemma.and_true_right_side(Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, e)), Guard.allKnown(rest, fuel, grammar, gm, input), ok)
      known_pick(fuel, grammar, gm, input, e, rest, y, G.ebnf_member_cases(y, e, rest, m), okE, later => known_of(rest, fuel, grammar, gm, input, okR, y, later))

# ======== THREE-VALUED ANSWERS ========

law tri_ne_no_yes:
  for e: {Guard.No{} == Guard.Yes{} : Guard.Tri}
  Empty

def tri_ne_no_yes(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.No{}, Guard.Yes{}, e))

law tri_ne_unknown_yes:
  for e: {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}
  Empty

def tri_ne_unknown_yes(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.Unknown{}, Guard.Yes{}, e))

law tri_ne_yes_no:
  for e: {Guard.Yes{} == Guard.No{} : Guard.Tri}
  Empty

def tri_ne_yes_no(e):
  Lemma.true_is_not_false(Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.Yes{}, Guard.No{}, e))

law tri_ne_unknown_no:
  for e: {Guard.Unknown{} == Guard.No{} : Guard.Tri}
  Empty

def tri_ne_unknown_no(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => Guard.isKnown(v), Guard.Unknown{}, Guard.No{}, e))
law and_yes:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.andTri(a, b) == Guard.Yes{} : Guard.Tri}
  {a == Guard.Yes{} : Guard.Tri} & {b == Guard.Yes{} : Guard.Tri}

def and_yes(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      ({==}, {==})
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))

law and_no:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.andTri(a, b) == Guard.No{} : Guard.Tri}
  Either<{a == Guard.No{} : Guard.Tri}, {b == Guard.No{} : Guard.Tri}>

def and_no(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd(Either<{Guard.Yes{} == Guard.No{} : Guard.Tri}, {Guard.Yes{} == Guard.No{} : Guard.Tri}>, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.No{}:
      Inr{{==}}
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Yes{} == Guard.No{} : Guard.Tri}, {Guard.Unknown{} == Guard.No{} : Guard.Tri}>, tri_ne_unknown_no(e))
    case Guard.No{} Guard.Yes{}:
      Inl{{==}}
    case Guard.No{} Guard.No{}:
      Inl{{==}}
    case Guard.No{} Guard.Unknown{}:
      Inl{{==}}
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.No{} : Guard.Tri}, {Guard.Yes{} == Guard.No{} : Guard.Tri}>, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.No{}:
      Inr{{==}}
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.No{} : Guard.Tri}, {Guard.Unknown{} == Guard.No{} : Guard.Tri}>, tri_ne_unknown_no(e))

law or_yes:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.orTri(a, b) == Guard.Yes{} : Guard.Tri}
  Either<{a == Guard.Yes{} : Guard.Tri}, {b == Guard.Yes{} : Guard.Tri}>

def or_yes(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      Inl{{==}}
    case Guard.Yes{} Guard.No{}:
      Inl{{==}}
    case Guard.Yes{} Guard.Unknown{}:
      Inl{{==}}
    case Guard.No{} Guard.Yes{}:
      Inr{{==}}
    case Guard.No{} Guard.No{}:
      Empty.absurd(Either<{Guard.No{} == Guard.Yes{} : Guard.Tri}, {Guard.No{} == Guard.Yes{} : Guard.Tri}>, tri_ne_no_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.No{} == Guard.Yes{} : Guard.Tri}, {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}>, tri_ne_unknown_yes(e))
    case Guard.Unknown{} Guard.Yes{}:
      Inr{{==}}
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, {Guard.No{} == Guard.Yes{} : Guard.Tri}>, tri_ne_unknown_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}>, tri_ne_unknown_yes(e))

law or_no:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.orTri(a, b) == Guard.No{} : Guard.Tri}
  {a == Guard.No{} : Guard.Tri} & {b == Guard.No{} : Guard.Tri}

def or_no(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.No{}:
      ({==}, {==})
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))

law not_yes:
  for a: Guard.Tri
  for e: {Guard.notTri(a) == Guard.Yes{} : Guard.Tri}
  {a == Guard.No{} : Guard.Tri}

def not_yes(a, e):
  match a:
    case Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{}:
      {==}
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_yes(e))

law not_no:
  for a: Guard.Tri
  for e: {Guard.notTri(a) == Guard.No{} : Guard.Tri}
  {a == Guard.Yes{} : Guard.Tri}

def not_no(a, e):
  match a:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_no(e))

law yes_of_known:
  for a: Guard.Tri
  for k: {Guard.isKnown(a) == True{} : Bool}
  for notNo: {a == Guard.No{} : Guard.Tri} -> Empty
  {a == Guard.Yes{} : Guard.Tri}

def yes_of_known(a, k, notNo):
  match a:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, notNo({==}))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(k))

law is_yes_of:
  for a: Guard.Tri
  for e: {a == Guard.Yes{} : Guard.Tri}
  {Guard.isYes(a) == True{} : Bool}

def is_yes_of(a, e):
  Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), a, Guard.Yes{}, e)

law yes_of_is:
  for a: Guard.Tri
  for e: {Guard.isYes(a) == True{} : Bool}
  {a == Guard.Yes{} : Guard.Tri}

def yes_of_is(a, e):
  match a:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))

# A refusal is never a Yes, and never decided.
law unless_yes:
  for f: Guard.Tri
  for t: Guard.Tri
  for e: {Guard.unlessRefused(f, t) == Guard.Yes{} : Guard.Tri}
  {f == Guard.Yes{} : Guard.Tri} & {t == Guard.Yes{} : Guard.Tri}

def unless_yes(f, t, e):
  match f:
    case Guard.Yes{}:
      ({==}, e)
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {t == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {t == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))

law unless_known:
  for f: Guard.Tri
  for t: Guard.Tri
  for e: {Guard.isKnown(Guard.unlessRefused(f, t)) == True{} : Bool}
  {f == Guard.Yes{} : Guard.Tri}

def unless_known(f, t, e):
  match f:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))
law and_yes_l:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.andTri(a, b) == Guard.Yes{} : Guard.Tri}
  {a == Guard.Yes{} : Guard.Tri}

def and_yes_l(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      {==}
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))

law and_yes_r:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.andTri(a, b) == Guard.Yes{} : Guard.Tri}
  {b == Guard.Yes{} : Guard.Tri}

def and_yes_r(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      {==}
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, tri_ne_no_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))

law or_no_l:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.orTri(a, b) == Guard.No{} : Guard.Tri}
  {a == Guard.No{} : Guard.Tri}

def or_no_l(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.No{}:
      {==}
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))

law or_no_r:
  for a: Guard.Tri
  for b: Guard.Tri
  for e: {Guard.orTri(a, b) == Guard.No{} : Guard.Tri}
  {b == Guard.No{} : Guard.Tri}

def or_no_r(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.No{} Guard.No{}:
      {==}
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, tri_ne_unknown_no(e))

law last_only_yes:
  for b: Bool
  for t: Guard.Tri
  for bT: {b == True{} : Bool}
  for e: {Guard.lastOnly(b, t) == Guard.Yes{} : Guard.Tri}
  {t == Guard.Yes{} : Guard.Tri}

def last_only_yes(b, t, bT, e):
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({t == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(bT))

law last_only_no_t:
  for b: Bool
  for t: Guard.Tri
  for e: {Guard.lastOnly(b, t) == Guard.No{} : Guard.Tri}
  {t == Guard.No{} : Guard.Tri}

def last_only_no_t(b, t, e):
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({t == Guard.No{} : Guard.Tri}, tri_ne_yes_no(e))

law last_only_no_b:
  for b: Bool
  for t: Guard.Tri
  for e: {Guard.lastOnly(b, t) == Guard.No{} : Guard.Tri}
  {b == True{} : Bool}

def last_only_no_b(b, t, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, tri_ne_yes_no(e))

law unless_free:
  for f: Guard.Tri
  for t: Guard.Tri
  for e: {Guard.isYes(Guard.unlessRefused(f, t)) == True{} : Bool}
  {f == Guard.Yes{} : Guard.Tri}

def unless_free(f, t, e):
  match f:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(e))

# ======== WHAT A YES AND A NO MEAN ========

law tri_of_yes:
  for found: Maybe<&2, Bool>
  for yes: Bool
  for e: {Guard.triOf(found, yes) == Guard.Yes{} : Guard.Tri}
  {yes == True{} : Bool}

def tri_of_yes(found, yes, e):
  match found:
    case Some{b}:
      match b:
        case True{}:
          match yes:
            case True{}:
              {==}
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, tri_ne_unknown_yes(e))
        case False{}:
          Empty.absurd({yes == True{} : Bool}, tri_ne_no_yes(e))
    case None{}:
      Empty.absurd({yes == True{} : Bool}, tri_ne_unknown_yes(e))

law tri_of_no:
  for found: Maybe<&2, Bool>
  for yes: Bool
  for e: {Guard.triOf(found, yes) == Guard.No{} : Guard.Tri}
  {found == Some{False{}} : Maybe<&2, Bool>}

def tri_of_no(found, yes, e):
  match found:
    case Some{b}:
      match b:
        case True{}:
          match yes:
            case True{}:
              Empty.absurd({Some{True{}} == Some{False{}} : Maybe<&2, Bool>}, tri_ne_yes_no(e))
            case False{}:
              Empty.absurd({Some{True{}} == Some{False{}} : Maybe<&2, Bool>}, tri_ne_unknown_no(e))
        case False{}:
          {==}
    case None{}:
      Empty.absurd({None{} == Some{False{}} : Maybe<&2, Bool>}, tri_ne_unknown_no(e))

law forests_pick:
  for +f: +List<Spec.Tree>
  for +rest: +List<+List<Spec.Tree>>
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for cases: Either<{Bool.and(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w)) == True{} : Bool}, {Guard.anyForestFor(rest, grammar, items, w) == True{} : Bool}>
  for later: {Guard.anyForestFor(rest, grammar, items, w) == True{} : Bool} -> Spec.Derives(grammar, items, w)
  Spec.Derives(grammar, items, w)

def forests_pick(f, rest, grammar, items, w, cases, later):
  match cases:
    case Inl{ok0}:
      +ok = {ok0 : {Bool.and(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w)) == True{} : Bool}}
      (f, (Lemma.and_true_left(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w), ok), G.nats_eq_sound(Spec.leaves(f), w, Lemma.and_true_right_side(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w), ok))))
    case Inr{r}:
      later(r)

law forests_yes:
  for fs: +List<+List<Spec.Tree>>
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for e: {Guard.anyForestFor(fs, grammar, items, w) == True{} : Bool}
  Spec.Derives(grammar, items, w)

def forests_yes(fs, grammar, items, w, e):
  match fs:
    case Nil{}:
      Empty.absurd(Spec.Derives(grammar, items, w), Lemma.false_is_not_true(e))
    case Con{+f, +rest}:
      forests_pick(f, rest, grammar, items, w, Lemma.or_true_cases(Bool.and(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w)), Guard.anyForestFor(rest, grammar, items, w), e), r => forests_yes(rest, grammar, items, w, r))

# A Yes comes with a forest that SPEC.bend accepts.
law derives_yes:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for e: {Guard.derivesW(fuel, grammar, items, w) == Guard.Yes{} : Guard.Tri}
  Spec.Derives(grammar, items, w)

def derives_yes(fuel, grammar, items, w, e):
  +ext = Prefer.extended(grammar, items)
  +fresh = Prefer.freshNt(grammar)
  +idx = List.length(&2, Spec.Production, grammar)
  +n = List.length(&2, Spec.Item, items)
  +fs = Guard.forestsFrom(Exact.exactSteps(fuel, ext, fresh, w), fuel, ext, idx, n, w)
  forests_yes(fs, grammar, items, w, tri_of_yes(Prefer.derivesHere(fuel, grammar, items, w, 0n, List.length(&2, Nat, w)), Guard.anyForestFor(fs, grammar, items, w), e))

law derives_no_with:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for e: {Guard.derivesW(fuel, grammar, items, w) == Guard.No{} : Guard.Tri}
  for +f: +List<Spec.Tree>
  for +fit: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +lv: {Spec.leaves(f) == w : +List<Nat>}
  Empty

def derives_no_with(fuel, grammar, items, w, e, f, fit, lv):
  +ext = Prefer.extended(grammar, items)
  +fresh = Prefer.freshNt(grammar)
  +idx = List.length(&2, Spec.Production, grammar)
  +n = List.length(&2, Spec.Item, items)
  +fs = Guard.forestsFrom(Exact.exactSteps(fuel, ext, fresh, w), fuel, ext, idx, n, w)
  +dh = tri_of_no(Prefer.derivesHere(fuel, grammar, items, w, 0n, List.length(&2, Nat, w)), Guard.anyForestFor(fs, grammar, items, w), e)
  +sp = Equal.sym(+List<Nat>, Lemma.takeN(List.length(&2, Nat, w), w), w, Lemma.take_length(w))
  Sub.sub_parse_refutes(fuel, grammar, items, w, 0n, w, sp, f, fit, lv, dh)

# A No comes from the checked parser, which misses no tree.
law derives_no:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for e: {Guard.derivesW(fuel, grammar, items, w) == Guard.No{} : Guard.Tri}
  for d: Spec.Derives(grammar, items, w)
  Empty

def derives_no(fuel, grammar, items, w, e, d):
  match d:
    case (f0, (fit0, lv0)):
      derives_no_with(fuel, grammar, items, w, e, f0, fit0, lv0)

# ======== LOOKAHEAD: SOME PREFIX OF THE REST ========

law take_drop_id:
  for +m: Nat
  for +d: +List<Nat>
  {List.append(&2, Nat, Lemma.takeN(m, d), Lemma.dropN(m, d)) == d : +List<Nat>}

def take_drop_id(m, d):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match d:
        case Nil{}:
          {==}
        case Con{h, t}:
          %take_drop_id(p, t) : {h <> List.append(&2, Nat, Lemma.takeN(p, t), Lemma.dropN(p, t)) == h <> _ : +List<Nat>}
          {==}

law length_drop_sub:
  for s: Nat
  for +x: +List<Nat>
  {List.length(&2, Nat, Lemma.dropN(s, x)) == Nat.sub(List.length(&2, Nat, x), s) : Nat}

def length_drop_sub(s, x):
  match s:
    case 0n:
      Equal.sym(Nat, Nat.sub(List.length(&2, Nat, x), 0n), List.length(&2, Nat, x), Lemma.sub_zero(List.length(&2, Nat, x)))
    case 1n+(+p):
      match x:
        case Nil{}:
          {==}
        case Con{h, +t}:
          length_drop_sub(p, t)

# The tokens from i, m of them.
law tok_take:
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  {Prefer.tokensFrom(input, i, Nat.add(i, m)) == Lemma.takeN(m, Lemma.dropN(i, input)) : +List<Nat>}

def tok_take(input, i, m):
  Equal.cong(Nat, +List<Nat>, v => Lemma.takeN(v, Lemma.dropN(i, input)), Nat.sub(Nat.add(i, m), i), m, Lemma.sub_add_left(i, m))

law ahead_tok:
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], Prefer.tokensFrom(input, i, Nat.add(i, m)))
  Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], Lemma.takeN(m, Lemma.dropN(i, input)))

def ahead_tok(grammar, x, input, i, m, d):
  %tok_take(input, i, m) : Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], _)
  d

law ahead_here:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], Prefer.tokensFrom(input, i, Nat.add(i, m)))
  Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))

def ahead_here(fuel, grammar, x, input, i, m, d):
  +dd = Lemma.dropN(i, input)
  (Lemma.takeN(m, dd), (Lemma.dropN(m, dd), (take_drop_id(m, dd), ahead_tok(grammar, x, input, i, m, d))))

law ahead_below_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  for cases: Either<{Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))) == Guard.Yes{} : Guard.Tri}, {Guard.aheadBelow(m, fuel, grammar, x, input, i) == Guard.Yes{} : Guard.Tri}>
  for later: {Guard.aheadBelow(m, fuel, grammar, x, input, i) == Guard.Yes{} : Guard.Tri} -> Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))
  Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))

def ahead_below_pick(fuel, grammar, x, input, i, m, cases, later):
  match cases:
    case Inl{e1}:
      ahead_here(fuel, grammar, x, input, i, m, derives_yes(fuel, grammar, [Spec.Sym{Spec.Nonterminal{x}}], Prefer.tokensFrom(input, i, Nat.add(i, m)), e1))
    case Inr{e2}:
      later(e2)

law ahead_below_yes:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.aheadBelow(n, fuel, grammar, x, input, i) == Guard.Yes{} : Guard.Tri}
  Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))

def ahead_below_yes(n, fuel, grammar, x, input, i, e):
  match n:
    case 0n:
      Empty.absurd(Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input)), tri_ne_no_yes(e))
    case 1n+(+m):
      ahead_below_pick(fuel, grammar, x, input, i, m, or_yes(Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))), Guard.aheadBelow(m, fuel, grammar, x, input, i), e), r => ahead_below_yes(m, fuel, grammar, x, input, i, r))

# A Yes: x derives some prefix of the tokens from i on.
law ahead_yes:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.aheadAt(fuel, grammar, x, input, i) == Guard.Yes{} : Guard.Tri}
  Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))

def ahead_yes(fuel, grammar, x, input, i, e):
  ahead_below_yes(1n+Nat.sub(List.length(&2, Nat, input), i), fuel, grammar, x, input, i, e)

law derives_at:
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +toks: +List<Nat>
  for +pre: +List<Nat>
  for +tEq: {toks == pre : +List<Nat>}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], toks)

def derives_at(grammar, x, toks, pre, tEq, d):
  %Equal.sym(+List<Nat>, toks, pre, tEq) : Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], _)
  d

law ahead_at_len:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  for e1: {Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))) == Guard.No{} : Guard.Tri}
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == Lemma.dropN(i, input) : +List<Nat>}
  for +same: {m == List.length(&2, Nat, pre) : Nat}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  Empty

def ahead_at_len(fuel, grammar, x, input, i, m, e1, pre, post, eq, same, d):
  +toks = Prefer.tokensFrom(input, i, Nat.add(i, m))
  +t1 = tok_take(input, i, m)
  +t2 = Equal.cong(Nat, +List<Nat>, v => Lemma.takeN(v, Lemma.dropN(i, input)), m, List.length(&2, Nat, pre), same)
  +t3 = Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(List.length(&2, Nat, pre), v), Lemma.dropN(i, input), List.append(&2, Nat, pre, post), Equal.sym(+List<Nat>, List.append(&2, Nat, pre, post), Lemma.dropN(i, input), eq))
  +t4 = Lemma.take_append_length(pre, post)
  +tEq = Equal.trans(+List<Nat>, toks, Lemma.takeN(m, Lemma.dropN(i, input)), pre, t1, Equal.trans(+List<Nat>, Lemma.takeN(m, Lemma.dropN(i, input)), Lemma.takeN(List.length(&2, Nat, pre), Lemma.dropN(i, input)), pre, t2, Equal.trans(+List<Nat>, Lemma.takeN(List.length(&2, Nat, pre), Lemma.dropN(i, input)), Lemma.takeN(List.length(&2, Nat, pre), List.append(&2, Nat, pre, post)), pre, t3, t4)))
  derives_no(fuel, grammar, [Spec.Sym{Spec.Nonterminal{x}}], toks, e1, derives_at(grammar, x, toks, pre, tEq, d))

law ahead_no_case:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for +m: Nat
  for +e1: {Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))) == Guard.No{} : Guard.Tri}
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == Lemma.dropN(i, input) : +List<Nat>}
  for +bEq: {Nat.is_eq(m, List.length(&2, Nat, pre)) == b : Bool}
  for +lt: {Nat.is_lt(List.length(&2, Nat, pre), 1n+m) == True{} : Bool}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  for later: {Nat.is_lt(List.length(&2, Nat, pre), m) == True{} : Bool} -> Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre) -> Empty
  Empty

def ahead_no_case(b, fuel, grammar, x, input, i, m, e1, pre, post, eq, bEq, lt, d, later):
  match b:
    case True{}:
      ahead_at_len(fuel, grammar, x, input, i, m, e1, pre, post, eq, Lemma.nat_eq_sound(m, List.length(&2, Nat, pre), bEq), d)
    case False{}:
      later(Lemma.lt_succ_ne(List.length(&2, Nat, pre), m, lt, bEq), d)

law ahead_below_both:
  for +m: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for both: {Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))) == Guard.No{} : Guard.Tri} & {Guard.aheadBelow(m, fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == Lemma.dropN(i, input) : +List<Nat>}
  for +lt: {Nat.is_lt(List.length(&2, Nat, pre), 1n+m) == True{} : Bool}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  for later: {Guard.aheadBelow(m, fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri} -> {Nat.is_lt(List.length(&2, Nat, pre), m) == True{} : Bool} -> Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre) -> Empty
  Empty

def ahead_below_both(m, fuel, grammar, x, input, i, both, pre, post, eq, lt, d, later):
  match both:
    case (e10, e20):
      +e1 = {e10 : {Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))) == Guard.No{} : Guard.Tri}}
      +e2 = {e20 : {Guard.aheadBelow(m, fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}}
      ahead_no_case(Nat.is_eq(m, List.length(&2, Nat, pre)), fuel, grammar, x, input, i, m, e1, pre, post, eq, {==}, lt, d,
        later(e2))

law ahead_below_no:
  for n: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.aheadBelow(n, fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == Lemma.dropN(i, input) : +List<Nat>}
  for +lt: {Nat.is_lt(List.length(&2, Nat, pre), n) == True{} : Bool}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  Empty

def ahead_below_no(n, fuel, grammar, x, input, i, e, pre, post, eq, lt, d):
  match n:
    case 0n:
      Lemma.lt_zero_false(List.length(&2, Nat, pre), lt)
    case 1n+(+m):
      ahead_below_both(m, fuel, grammar, x, input, i, or_no(Guard.derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))), Guard.aheadBelow(m, fuel, grammar, x, input, i), e), pre, post, eq, lt, d,
        e2 => lt2 => d2 => ahead_below_no(m, fuel, grammar, x, input, i, e2, pre, post, eq, lt2, d2))

law ahead_no_with:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.aheadAt(fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == Lemma.dropN(i, input) : +List<Nat>}
  for d: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], pre)
  Empty

def ahead_no_with(fuel, grammar, x, input, i, e, pre, post, eq, d):
  +lp = List.length(&2, Nat, pre)
  +rest = Nat.sub(List.length(&2, Nat, input), i)
  +sum = Nat.add(lp, List.length(&2, Nat, post))
  +l1 = Lemma.length_append(pre, post)
  +l2 = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, pre, post), Lemma.dropN(i, input), eq)
  +l3 = length_drop_sub(i, input)
  +sumEq = Equal.trans(Nat, sum, List.length(&2, Nat, List.append(&2, Nat, pre, post)), rest, Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, pre, post)), sum, l1), Equal.trans(Nat, List.length(&2, Nat, List.append(&2, Nat, pre, post)), List.length(&2, Nat, Lemma.dropN(i, input)), rest, l2, l3))
  +le = Equal.trans(Bool, Nat.is_le(lp, rest), Nat.is_le(lp, sum), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(lp, v), rest, sum, Equal.sym(Nat, sum, rest, sumEq)), Lemma.le_add_right(lp, List.length(&2, Nat, post)))
  ahead_below_no(1n+rest, fuel, grammar, x, input, i, e, pre, post, eq, Lemma.lt_of_succ_le(lp, 1n+rest, le), d)

# A No: x derives no prefix of the tokens from i on.
law ahead_no:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +x: Nat
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.aheadAt(fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}
  for h: Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))
  Empty

def ahead_no(fuel, grammar, x, input, i, e, h):
  match h:
    case (pre0, rest0):
      match rest0:
        case (post0, (eq0, d)):
          +pre = {pre0 : +List<Nat>}
          +post = {post0 : +List<Nat>}
          ahead_no_with(fuel, grammar, x, input, i, e, pre, post, eq0, d)

# ======== EVERY, NONE ========

law all_ahead_yes:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for +e: {Guard.allAhead(xs, fuel, grammar, input, i) == Guard.Yes{} : Guard.Tri}
  Spec.AllAhead(grammar, xs, Lemma.dropN(i, input))

def all_ahead_yes(xs, fuel, grammar, input, i, e):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      (ahead_yes(fuel, grammar, x, input, i, and_yes_l(Guard.aheadAt(fuel, grammar, x, input, i), Guard.allAhead(rest, fuel, grammar, input, i), e)),
        all_ahead_yes(rest, fuel, grammar, input, i, and_yes_r(Guard.aheadAt(fuel, grammar, x, input, i), Guard.allAhead(rest, fuel, grammar, input, i), e)))

law none_ahead_yes:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for +e: {Guard.noneAhead(xs, fuel, grammar, input, i) == Guard.Yes{} : Guard.Tri}
  Spec.NoneAhead(grammar, xs, Lemma.dropN(i, input))

def none_ahead_yes(xs, fuel, grammar, input, i, e):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +nx = not_yes(Guard.aheadAt(fuel, grammar, x, input, i), and_yes_l(Guard.notTri(Guard.aheadAt(fuel, grammar, x, input, i)), Guard.noneAhead(rest, fuel, grammar, input, i), e))
      (h => ahead_no(fuel, grammar, x, input, i, nx, h),
        none_ahead_yes(rest, fuel, grammar, input, i, and_yes_r(Guard.notTri(Guard.aheadAt(fuel, grammar, x, input, i)), Guard.noneAhead(rest, fuel, grammar, input, i), e)))

law none_derive_yes:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +w: +List<Nat>
  for +e: {Guard.noneDerive(xs, fuel, grammar, w) == Guard.Yes{} : Guard.Tri}
  Spec.NoneDerive(grammar, xs, w)

def none_derive_yes(xs, fuel, grammar, w, e):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +nx = not_yes(Guard.derivesNt(fuel, grammar, x, w), and_yes_l(Guard.notTri(Guard.derivesNt(fuel, grammar, x, w)), Guard.noneDerive(rest, fuel, grammar, w), e))
      (d => derives_no(fuel, grammar, [Spec.Sym{Spec.Nonterminal{x}}], w, nx, d),
        none_derive_yes(rest, fuel, grammar, w, and_yes_r(Guard.notTri(Guard.derivesNt(fuel, grammar, x, w)), Guard.noneDerive(rest, fuel, grammar, w), e)))

law edge_ok_yes:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, w) == Guard.Yes{} : Guard.Tri}
  Spec.EdgeOk(grammar, ids, items, w)

def edge_ok_yes(ids, fuel, grammar, items, w, e):
  match ids:
    case Nil{}:
      d => derives_no(fuel, grammar, items, w, not_yes(Guard.derivesW(fuel, grammar, items, w), e), d)
    case Con{+x, +rest}:
      none_derive_yes(x <> rest, fuel, grammar, w, e)

law all_ahead_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for +x: Nat
  for +rest: +List<Nat>
  for cases: Either<{Guard.aheadAt(fuel, grammar, x, input, i) == Guard.No{} : Guard.Tri}, {Guard.allAhead(rest, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}>
  for h1: Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input))
  for later: {Guard.allAhead(rest, fuel, grammar, input, i) == Guard.No{} : Guard.Tri} -> Empty
  Empty

def all_ahead_pick(fuel, grammar, input, i, x, rest, cases, h1, later):
  match cases:
    case Inl{e1}:
      ahead_no(fuel, grammar, x, input, i, e1, h1)
    case Inr{e2}:
      later(e2)

law all_ahead_no:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.allAhead(xs, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}
  for h: Spec.AllAhead(grammar, xs, Lemma.dropN(i, input))
  Empty

def all_ahead_no(xs, fuel, grammar, input, i, e, h):
  match xs:
    case Nil{}:
      tri_ne_yes_no(e)
    case Con{+x, +rest}:
      match h:
        case (h1, hr):
          all_ahead_pick(fuel, grammar, input, i, x, rest, and_no(Guard.aheadAt(fuel, grammar, x, input, i), Guard.allAhead(rest, fuel, grammar, input, i), e), h1, e2 => all_ahead_no(rest, fuel, grammar, input, i, e2, hr))

law none_ahead_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for +x: Nat
  for +rest: +List<Nat>
  for cases: Either<{Guard.notTri(Guard.aheadAt(fuel, grammar, x, input, i)) == Guard.No{} : Guard.Tri}, {Guard.noneAhead(rest, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}>
  for h1: Spec.DerivesAhead(grammar, x, Lemma.dropN(i, input)) -> Empty
  for later: {Guard.noneAhead(rest, fuel, grammar, input, i) == Guard.No{} : Guard.Tri} -> Empty
  Empty

def none_ahead_pick(fuel, grammar, input, i, x, rest, cases, h1, later):
  match cases:
    case Inl{e1}:
      h1(ahead_yes(fuel, grammar, x, input, i, not_no(Guard.aheadAt(fuel, grammar, x, input, i), e1)))
    case Inr{e2}:
      later(e2)

law none_ahead_no:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +i: Nat
  for e: {Guard.noneAhead(xs, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}
  for h: Spec.NoneAhead(grammar, xs, Lemma.dropN(i, input))
  Empty

def none_ahead_no(xs, fuel, grammar, input, i, e, h):
  match xs:
    case Nil{}:
      tri_ne_yes_no(e)
    case Con{+x, +rest}:
      match h:
        case (h1, hr):
          none_ahead_pick(fuel, grammar, input, i, x, rest, and_no(Guard.notTri(Guard.aheadAt(fuel, grammar, x, input, i)), Guard.noneAhead(rest, fuel, grammar, input, i), e), h1, e2 => none_ahead_no(rest, fuel, grammar, input, i, e2, hr))

law none_derive_pick:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +w: +List<Nat>
  for +x: Nat
  for +rest: +List<Nat>
  for cases: Either<{Guard.notTri(Guard.derivesNt(fuel, grammar, x, w)) == Guard.No{} : Guard.Tri}, {Guard.noneDerive(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri}>
  for h1: Spec.Derives(grammar, [Spec.Sym{Spec.Nonterminal{x}}], w) -> Empty
  for later: {Guard.noneDerive(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri} -> Empty
  Empty

def none_derive_pick(fuel, grammar, w, x, rest, cases, h1, later):
  match cases:
    case Inl{e1}:
      h1(derives_yes(fuel, grammar, [Spec.Sym{Spec.Nonterminal{x}}], w, not_no(Guard.derivesNt(fuel, grammar, x, w), e1)))
    case Inr{e2}:
      later(e2)

law none_derive_no:
  for xs: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +w: +List<Nat>
  for e: {Guard.noneDerive(xs, fuel, grammar, w) == Guard.No{} : Guard.Tri}
  for h: Spec.NoneDerive(grammar, xs, w)
  Empty

def none_derive_no(xs, fuel, grammar, w, e, h):
  match xs:
    case Nil{}:
      tri_ne_yes_no(e)
    case Con{+x, +rest}:
      match h:
        case (h1, hr):
          none_derive_pick(fuel, grammar, w, x, rest, and_no(Guard.notTri(Guard.derivesNt(fuel, grammar, x, w)), Guard.noneDerive(rest, fuel, grammar, w), e), h1, e2 => none_derive_no(rest, fuel, grammar, w, e2, hr))

law edge_ok_no:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for e: {Guard.edgeOk(ids, fuel, grammar, items, w) == Guard.No{} : Guard.Tri}
  for h: Spec.EdgeOk(grammar, ids, items, w)
  Empty

def edge_ok_no(ids, fuel, grammar, items, w, e, h):
  match ids:
    case Nil{}:
      h(derives_yes(fuel, grammar, items, w, not_no(Guard.derivesW(fuel, grammar, items, w), e)))
    case Con{+x, +rest}:
      none_derive_no(x <> rest, fuel, grammar, w, e, h)

# ======== ONE RULE OF A NODE ========

def SpIf(b: Bool, +sp: Maybe<&2, +List<Nat>>, +w: +List<Nat>) -> Data:
  match b:
    case True{}:
      {sp == Some{w} : Maybe<&2, +List<Nat>>}
    case False{}:
      {w == w : +List<Nat>}

def TokIf(b: Bool, +x: +List<Nat>, +w: +List<Nat>) -> Data:
  match b:
    case True{}:
      {x == w : +List<Nat>}
    case False{}:
      {w == w : +List<Nat>}

law edge_of_yes:
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +toks: +List<Nat>
  for +w: +List<Nat>
  for +tok: {toks == w : +List<Nat>}
  for +sp: Maybe<&2, +List<Nat>>
  for +spEq: {sp == Some{w} : Maybe<&2, +List<Nat>>}
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, toks) == Guard.Yes{} : Guard.Tri}
  Spec.EdgeFree(grammar, ids, items, sp)

def edge_of_yes(ids, fuel, grammar, items, toks, w, tok, sp, spEq, e):
  %Equal.sym(Maybe<&2, +List<Nat>>, sp, Some{w}, spEq) : Spec.EdgeFree(grammar, ids, items, _)
  edge_ok_yes(ids, fuel, grammar, items, w, Equal.trans(Guard.Tri, Guard.edgeOk(ids, fuel, grammar, items, w), Guard.edgeOk(ids, fuel, grammar, items, toks), Guard.Yes{}, Equal.cong(+List<Nat>, Guard.Tri, v => Guard.edgeOk(ids, fuel, grammar, items, v), w, toks, Equal.sym(+List<Nat>, toks, w, tok)), e))

# A rule of a node with no children: its one step answered Yes.
law guard_hold_nil:
  for g: Spec.Guard
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +y: {Guard.guardAt(g, fuel, grammar, input, items, 0n, 0n, i, i, i) == Guard.Yes{} : Guard.Tri}
  Spec.Holds(grammar, g, items, [], Lemma.dropN(i, input))

def guard_hold_nil(g, fuel, grammar, input, items, i, y):
  match g:
    case Spec.Ahead{+ids}:
      all_ahead_yes(ids, fuel, grammar, input, i, y)
    case Spec.NotAhead{+ids}:
      none_ahead_yes(ids, fuel, grammar, input, i, y)
    case Spec.LeftAssoc{+ids}:
      Unit{}
    case Spec.RightAssoc{+ids}:
      Unit{}

# A rule of a node with children: its last and its first own step answered Yes.
law guard_hold_cons:
  for g: Spec.Guard
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +kL: Nat
  for +jL: Nat
  for +jF: Nat
  for +ch: +List<Spec.Tree>
  for +wL: +List<Nat>
  for +wF: +List<Nat>
  for +yL: {Guard.guardAt(g, fuel, grammar, input, items, n, n, i, kL, jL) == Guard.Yes{} : Guard.Tri}
  for +yF: {Guard.guardAt(g, fuel, grammar, input, items, n, 1n, i, i, jF) == Guard.Yes{} : Guard.Tri}
  for +nn: {Nat.is_eq(n, n) == True{} : Bool}
  for +nPos: {Nat.is_lt(0n, n) == True{} : Bool}
  for +tokL: {Prefer.tokensFrom(input, kL, jL) == wL : +List<Nat>}
  for +tokF: {Prefer.tokensFrom(input, i, jF) == wF : +List<Nat>}
  for +spL: {Spec.lastSpell(ch) == Some{wL} : Maybe<&2, +List<Nat>>}
  for +spF: {Spec.firstSpell(ch) == Some{wF} : Maybe<&2, +List<Nat>>}
  Spec.Holds(grammar, g, items, ch, Lemma.dropN(i, input))

def guard_hold_cons(g, fuel, grammar, input, items, n, i, kL, jL, jF, ch, wL, wF, yL, yF, nn, nPos, tokL, tokF, spL, spF):
  match g:
    case Spec.Ahead{+ids}:
      all_ahead_yes(ids, fuel, grammar, input, i, last_only_yes(Nat.is_eq(n, n), Guard.allAhead(ids, fuel, grammar, input, i), nn, yL))
    case Spec.NotAhead{+ids}:
      none_ahead_yes(ids, fuel, grammar, input, i, last_only_yes(Nat.is_eq(n, n), Guard.noneAhead(ids, fuel, grammar, input, i), nn, yL))
    case Spec.LeftAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, kL, jL)
      edge_of_yes(ids, fuel, grammar, items, toks, wL, tokL, Spec.lastSpell(ch), spL, last_only_yes(Bool.and(Nat.is_eq(n, n), Nat.is_lt(0n, n)), Guard.edgeOk(ids, fuel, grammar, items, toks), Lemma.and_true_intro(Nat.is_eq(n, n), Nat.is_lt(0n, n), nn, nPos), yL))
    case Spec.RightAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, i, jF)
      edge_of_yes(ids, fuel, grammar, items, toks, wF, tokF, Spec.firstSpell(ch), spF, last_only_yes(Nat.is_lt(0n, n), Guard.edgeOk(ids, fuel, grammar, items, toks), nPos, yF))

law edge_free_fn:
  for +grammar: +List<Spec.Production>
  for +ids: +List<Nat>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for +sp: Maybe<&2, +List<Nat>>
  for +spEq: {sp == Some{w} : Maybe<&2, +List<Nat>>}
  Spec.EdgeFree(grammar, ids, items, sp) -> Spec.EdgeOk(grammar, ids, items, w)

def edge_free_fn(grammar, ids, items, w, sp, spEq):
  %Equal.sym(Maybe<&2, +List<Nat>>, sp, Some{w}, spEq) : Spec.EdgeFree(grammar, ids, items, _) -> Spec.EdgeOk(grammar, ids, items, w)
  hh => hh

law edge_free_at:
  for +grammar: +List<Spec.Production>
  for +ids: +List<Nat>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for +sp: Maybe<&2, +List<Nat>>
  for +spEq: {sp == Some{w} : Maybe<&2, +List<Nat>>}
  for h: Spec.EdgeFree(grammar, ids, items, sp)
  Spec.EdgeOk(grammar, ids, items, w)

def edge_free_at(grammar, ids, items, w, sp, spEq, h):
  edge_free_fn(grammar, ids, items, w, sp, spEq)(h)

law edge_no_some:
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +w: +List<Nat>
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, w) == Guard.No{} : Guard.Tri}
  for +sp: Maybe<&2, +List<Nat>>
  for +spEq: {sp == Some{w} : Maybe<&2, +List<Nat>>}
  for h: Spec.EdgeFree(grammar, ids, items, sp)
  Empty

def edge_no_some(ids, fuel, grammar, items, w, e, sp, spEq, h):
  edge_ok_no(ids, fuel, grammar, items, w, e, edge_free_at(grammar, ids, items, w, sp, spEq, h))

law edge_no_at:
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +toks: +List<Nat>
  for +w: +List<Nat>
  for +sp: Maybe<&2, +List<Nat>>
  for +tok: {toks == w : +List<Nat>}
  for +spEq: {sp == Some{w} : Maybe<&2, +List<Nat>>}
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, toks) == Guard.No{} : Guard.Tri}
  for h: Spec.EdgeFree(grammar, ids, items, sp)
  Empty

def edge_no_at(ids, fuel, grammar, items, toks, w, sp, tok, spEq, e, h):
  +eW = Equal.trans(Guard.Tri, Guard.edgeOk(ids, fuel, grammar, items, w), Guard.edgeOk(ids, fuel, grammar, items, toks), Guard.No{}, Equal.cong(+List<Nat>, Guard.Tri, v => Guard.edgeOk(ids, fuel, grammar, items, v), w, toks, Equal.sym(+List<Nat>, toks, w, tok)), e)
  edge_no_some(ids, fuel, grammar, items, w, eW, sp, spEq, h)

law edge_no_case:
  for b: Bool
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +toks: +List<Nat>
  for +w: +List<Nat>
  for +sp: Maybe<&2, +List<Nat>>
  for +bT: {b == True{} : Bool}
  for +tok: TokIf(b, toks, w)
  for +spEq: SpIf(b, sp, w)
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, toks) == Guard.No{} : Guard.Tri}
  for h: Spec.EdgeFree(grammar, ids, items, sp)
  Empty

def edge_no_case(b, ids, fuel, grammar, items, toks, w, sp, bT, tok, spEq, e, h):
  match b:
    case True{}:
      edge_no_at(ids, fuel, grammar, items, toks, w, sp, tok, spEq, e, h)
    case False{}:
      Lemma.false_is_not_true(bT)

law tok_if_of:
  for b: Bool
  for +x: +List<Nat>
  for +w: +List<Nat>
  for +eq: {x == w : +List<Nat>}
  TokIf(b, x, w)

def tok_if_of(b, x, w, eq):
  match b:
    case True{}:
      eq
    case False{}:
      {==}

law true_of_eq:
  for +b: Bool
  for +c: Bool
  for +bc: {c == b : Bool}
  for +cT: {c == True{} : Bool}
  {b == True{} : Bool}

def true_of_eq(b, c, bc, cT):
  Equal.trans(Bool, b, c, True{}, Equal.sym(Bool, c, b, bc), cT)

# A rule that holds is never answered No by an own step of its node.
law guard_not_no:
  for g: Spec.Guard
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +kS: Nat
  for +jS: Nat
  for +ch: +List<Spec.Tree>
  for +w: +List<Nat>
  for holds: Spec.Holds(grammar, g, items, ch, Lemma.dropN(i, input))
  for +bL: Bool
  for +lEq: {Nat.is_eq(d, n) == bL : Bool}
  for +tokL: {Prefer.tokensFrom(input, kS, jS) == w : +List<Nat>}
  for +spL: SpIf(bL, Spec.lastSpell(ch), w)
  for +bF: Bool
  for +fEq: {Nat.is_eq(d, 1n) == bF : Bool}
  for +tokF: TokIf(bF, Prefer.tokensFrom(input, i, jS), w)
  for +spF: SpIf(bF, Spec.firstSpell(ch), w)
  for +e: {Guard.guardAt(g, fuel, grammar, input, items, n, d, i, kS, jS) == Guard.No{} : Guard.Tri}
  Empty

def guard_not_no(g, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, holds, bL, lEq, tokL, spL, bF, fEq, tokF, spF, e):
  match g:
    case Spec.Ahead{+ids}:
      all_ahead_no(ids, fuel, grammar, input, i, last_only_no_t(Nat.is_eq(d, n), Guard.allAhead(ids, fuel, grammar, input, i), e), holds)
    case Spec.NotAhead{+ids}:
      none_ahead_no(ids, fuel, grammar, input, i, last_only_no_t(Nat.is_eq(d, n), Guard.noneAhead(ids, fuel, grammar, input, i), e), holds)
    case Spec.LeftAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, kS, jS)
      +cond = Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n))
      +cT = last_only_no_b(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e)
      +bT = true_of_eq(bL, Nat.is_eq(d, n), lEq, Lemma.and_true_left(Nat.is_eq(d, n), Nat.is_lt(0n, n), cT))
      edge_no_case(bL, ids, fuel, grammar, items, toks, w, Spec.lastSpell(ch), bT, tok_if_of(bL, toks, w, tokL), spL, last_only_no_t(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e), holds)
    case Spec.RightAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, i, jS)
      +cond = Bool.and(Nat.is_eq(d, 1n), Nat.is_lt(0n, n))
      +cT = last_only_no_b(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e)
      +bT = true_of_eq(bF, Nat.is_eq(d, 1n), fEq, Lemma.and_true_left(Nat.is_eq(d, 1n), Nat.is_lt(0n, n), cT))
      edge_no_case(bF, ids, fuel, grammar, items, toks, w, Spec.firstSpell(ch), bT, tokF, spF, last_only_no_t(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e), holds)

# ======== ALL RULES OF A NODE ========

law guards_hold_nil:
  for gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +y: {Guard.guardsAt(gs, fuel, grammar, input, items, 0n, 0n, i, i, i) == Guard.Yes{} : Guard.Tri}
  Spec.AllHold(grammar, gs, items, [], Lemma.dropN(i, input))

def guards_hold_nil(gs, fuel, grammar, input, items, i, y):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +rest}:
      +a = Guard.guardAt(g, fuel, grammar, input, items, 0n, 0n, i, i, i)
      +b = Guard.guardsAt(rest, fuel, grammar, input, items, 0n, 0n, i, i, i)
      (guard_hold_nil(g, fuel, grammar, input, items, i, and_yes_l(a, b, y)), guards_hold_nil(rest, fuel, grammar, input, items, i, and_yes_r(a, b, y)))

law guards_hold_cons:
  for gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +kL: Nat
  for +jL: Nat
  for +jF: Nat
  for +ch: +List<Spec.Tree>
  for +wL: +List<Nat>
  for +wF: +List<Nat>
  for +yL: {Guard.guardsAt(gs, fuel, grammar, input, items, n, n, i, kL, jL) == Guard.Yes{} : Guard.Tri}
  for +yF: {Guard.guardsAt(gs, fuel, grammar, input, items, n, 1n, i, i, jF) == Guard.Yes{} : Guard.Tri}
  for +nn: {Nat.is_eq(n, n) == True{} : Bool}
  for +nPos: {Nat.is_lt(0n, n) == True{} : Bool}
  for +tokL: {Prefer.tokensFrom(input, kL, jL) == wL : +List<Nat>}
  for +tokF: {Prefer.tokensFrom(input, i, jF) == wF : +List<Nat>}
  for +spL: {Spec.lastSpell(ch) == Some{wL} : Maybe<&2, +List<Nat>>}
  for +spF: {Spec.firstSpell(ch) == Some{wF} : Maybe<&2, +List<Nat>>}
  Spec.AllHold(grammar, gs, items, ch, Lemma.dropN(i, input))

def guards_hold_cons(gs, fuel, grammar, input, items, n, i, kL, jL, jF, ch, wL, wF, yL, yF, nn, nPos, tokL, tokF, spL, spF):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +rest}:
      +aL = Guard.guardAt(g, fuel, grammar, input, items, n, n, i, kL, jL)
      +bL = Guard.guardsAt(rest, fuel, grammar, input, items, n, n, i, kL, jL)
      +aF = Guard.guardAt(g, fuel, grammar, input, items, n, 1n, i, i, jF)
      +bF = Guard.guardsAt(rest, fuel, grammar, input, items, n, 1n, i, i, jF)
      (guard_hold_cons(g, fuel, grammar, input, items, n, i, kL, jL, jF, ch, wL, wF, and_yes_l(aL, bL, yL), and_yes_l(aF, bF, yF), nn, nPos, tokL, tokF, spL, spF),
        guards_hold_cons(rest, fuel, grammar, input, items, n, i, kL, jL, jF, ch, wL, wF, and_yes_r(aL, bL, yL), and_yes_r(aF, bF, yF), nn, nPos, tokL, tokF, spL, spF))

law guards_no_pick:
  for +a: Guard.Tri
  for +b: Guard.Tri
  for cases: Either<{a == Guard.No{} : Guard.Tri}, {b == Guard.No{} : Guard.Tri}>
  for first: {a == Guard.No{} : Guard.Tri} -> Empty
  for later: {b == Guard.No{} : Guard.Tri} -> Empty
  Empty

def guards_no_pick(a, b, cases, first, later):
  match cases:
    case Inl{e1}:
      first(e1)
    case Inr{e2}:
      later(e2)

law guards_not_no:
  for gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +kS: Nat
  for +jS: Nat
  for +ch: +List<Spec.Tree>
  for +w: +List<Nat>
  for holds: Spec.AllHold(grammar, gs, items, ch, Lemma.dropN(i, input))
  for +bL: Bool
  for +lEq: {Nat.is_eq(d, n) == bL : Bool}
  for +tokL: {Prefer.tokensFrom(input, kS, jS) == w : +List<Nat>}
  for +spL: SpIf(bL, Spec.lastSpell(ch), w)
  for +bF: Bool
  for +fEq: {Nat.is_eq(d, 1n) == bF : Bool}
  for +tokF: TokIf(bF, Prefer.tokensFrom(input, i, jS), w)
  for +spF: SpIf(bF, Spec.firstSpell(ch), w)
  for +e: {Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, kS, jS) == Guard.No{} : Guard.Tri}
  Empty

def guards_not_no(gs, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, holds, bL, lEq, tokL, spL, bF, fEq, tokF, spF, e):
  match gs:
    case Nil{}:
      tri_ne_yes_no(e)
    case Con{+g, +rest}:
      match holds:
        case (h1, hr):
          +a = Guard.guardAt(g, fuel, grammar, input, items, n, d, i, kS, jS)
          +b = Guard.guardsAt(rest, fuel, grammar, input, items, n, d, i, kS, jS)
          guards_no_pick(a, b, and_no(a, b, e),
            e1 => guard_not_no(g, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, h1, bL, lEq, tokL, spL, bF, fEq, tokF, spF, e1),
            e2 => guards_not_no(rest, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, hr, bL, lEq, tokL, spL, bF, fEq, tokF, spF, e2))

# ======== THE OWN STEPS OF A NODE ========
#
# The Tri of an own step: the step is item d of the node's sequence, whose rules are gs
# and items `items` (n of them); `free` is Yes unless the rules sit on a loop.

def ownTri(free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  Guard.unlessRefused(free, Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, k, j))

def emptyOk(dot: Nat, +free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +i: Nat, +k: Nat) -> Bool:
  match dot:
    case 0n:
      Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 0n, i, k, k))
    case 1n+p:
      True{}

# Every own step of the forest, from the dot on, answered Yes.
def ownOk(f: +List<Spec.Tree>, +free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +dot: Nat, +i: Nat, +k: Nat) -> Bool:
  match f:
    case Nil{}:
      emptyOk(dot, free, gs, fuel, grammar, input, items, n, i, k)
    case Con{+t, +ts}:
      Bool.and(Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n+dot, i, k, Sub.endOf(t, k))), ownOk(ts, free, gs, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k)))

def emptyKnown(dot: Nat, +free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +i: Nat, +k: Nat) -> Bool:
  match dot:
    case 0n:
      Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, 0n, i, k, k))
    case 1n+p:
      True{}

# Every own step of the forest, from the dot on, was decided.
def ownKnown(f: +List<Spec.Tree>, +free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +dot: Nat, +i: Nat, +k: Nat) -> Bool:
  match f:
    case Nil{}:
      emptyKnown(dot, free, gs, fuel, grammar, input, items, n, i, k)
    case Con{+t, +ts}:
      Bool.and(Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, 1n+dot, i, k, Sub.endOf(t, k))), ownKnown(ts, free, gs, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k)))

# ---- Where the children are ----

law pos_assoc:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +next: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(k, input) : +List<Nat>}
  {List.append(&2, Nat, Spec.leaves([t]), List.append(&2, Nat, Spec.leaves(ts), next)) == Lemma.dropN(k, input) : +List<Nat>}

def pos_assoc(t, ts, next, input, k, pos):
  +lt = Spec.leaves([t])
  +lts = Spec.leaves(ts)
  +c1 = Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, next), Spec.leaves(t <> ts), List.append(&2, Nat, lt, lts), Sub.leaves_cons(t, ts))
  Equal.trans(+List<Nat>, List.append(&2, Nat, lt, List.append(&2, Nat, lts, next)), List.append(&2, Nat, List.append(&2, Nat, lt, lts), next), Lemma.dropN(k, input), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lt, lts), next), List.append(&2, Nat, lt, List.append(&2, Nat, lts, next)), G.nat_append_assoc(lt, lts, next)),
    Equal.trans(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lt, lts), next), List.append(&2, Nat, Spec.leaves(t <> ts), next), Lemma.dropN(k, input), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(t <> ts), next), List.append(&2, Nat, List.append(&2, Nat, lt, lts), next), c1), pos))

# What the first tree spells: the tokens from k to its end.
law pos_head_tok:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +next: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(k, input) : +List<Nat>}
  {Prefer.tokensFrom(input, k, Sub.endOf(t, k)) == Spec.leaves([t]) : +List<Nat>}

def pos_head_tok(t, ts, next, input, k, pos):
  +lt = Spec.leaves([t])
  +rest = List.append(&2, Nat, Spec.leaves(ts), next)
  +p2 = pos_assoc(t, ts, next, input, k, pos)
  +e0 = Equal.cong(Nat, +List<Nat>, v => Prefer.tokensFrom(input, k, v), Sub.endOf(t, k), Nat.add(k, List.length(&2, Nat, lt)), Sub.end_of_one(t, k))
  +e1 = tok_take(input, k, List.length(&2, Nat, lt))
  +e2 = Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(List.length(&2, Nat, lt), v), Lemma.dropN(k, input), List.append(&2, Nat, lt, rest), Equal.sym(+List<Nat>, List.append(&2, Nat, lt, rest), Lemma.dropN(k, input), p2))
  Equal.trans(+List<Nat>, Prefer.tokensFrom(input, k, Sub.endOf(t, k)), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, lt))), lt, e0,
    Equal.trans(+List<Nat>, Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, lt))), Lemma.takeN(List.length(&2, Nat, lt), Lemma.dropN(k, input)), lt, e1,
      Equal.trans(+List<Nat>, Lemma.takeN(List.length(&2, Nat, lt), Lemma.dropN(k, input)), Lemma.takeN(List.length(&2, Nat, lt), List.append(&2, Nat, lt, rest)), lt, e2, Lemma.take_append_length(lt, rest))))

# The rest of the forest starts where the first tree ends.
law pos_tail:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +next: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(k, input) : +List<Nat>}
  {List.append(&2, Nat, Spec.leaves(ts), next) == Lemma.dropN(Sub.endOf(t, k), input) : +List<Nat>}

def pos_tail(t, ts, next, input, k, pos):
  +lt = Spec.leaves([t])
  +rest = List.append(&2, Nat, Spec.leaves(ts), next)
  +p2 = pos_assoc(t, ts, next, input, k, pos)
  +e0 = Equal.cong(Nat, +List<Nat>, v => Lemma.dropN(v, input), Sub.endOf(t, k), Nat.add(k, List.length(&2, Nat, lt)), Sub.end_of_one(t, k))
  +e1 = Lemma.drop_add(k, List.length(&2, Nat, lt), input)
  +e2 = Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.dropN(List.length(&2, Nat, lt), v), Lemma.dropN(k, input), List.append(&2, Nat, lt, rest), Equal.sym(+List<Nat>, List.append(&2, Nat, lt, rest), Lemma.dropN(k, input), p2))
  Equal.sym(+List<Nat>, Lemma.dropN(Sub.endOf(t, k), input), rest,
    Equal.trans(+List<Nat>, Lemma.dropN(Sub.endOf(t, k), input), Lemma.dropN(Nat.add(k, List.length(&2, Nat, lt)), input), rest, e0,
      Equal.trans(+List<Nat>, Lemma.dropN(Nat.add(k, List.length(&2, Nat, lt)), input), Lemma.dropN(List.length(&2, Nat, lt), Lemma.dropN(k, input)), rest, e1,
        Equal.trans(+List<Nat>, Lemma.dropN(List.length(&2, Nat, lt), Lemma.dropN(k, input)), Lemma.dropN(List.length(&2, Nat, lt), List.append(&2, Nat, lt, rest)), rest, e2, Lemma.drop_append_length(lt, rest)))))

# ======== DIRECTION 1: OWN STEPS ANSWERED YES, SO THE RULES HOLD ========

law unless_yes_t:
  for f: Guard.Tri
  for t: Guard.Tri
  for e: {Guard.unlessRefused(f, t) == Guard.Yes{} : Guard.Tri}
  {t == Guard.Yes{} : Guard.Tri}

def unless_yes_t(f, t, e):
  match f:
    case Guard.Yes{}:
      e
    case Guard.No{}:
      Empty.absurd({t == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))
    case Guard.Unknown{}:
      Empty.absurd({t == Guard.Yes{} : Guard.Tri}, tri_ne_unknown_yes(e))

# An own step that answered Yes: its guardsAt is Yes.
law own_yes:
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +e: {Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d, i, k, j)) == True{} : Bool}
  {Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, k, j) == Guard.Yes{} : Guard.Tri}

def own_yes(free, gs, fuel, grammar, input, items, n, d, i, k, j, e):
  +g = Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, k, j)
  unless_yes_t(free, g, yes_of_is(Guard.unlessRefused(free, g), e))

# The last own step, and what the last child spells.
def LastOwn(+free: Guard.Tri, +gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +dEnd: Nat, +i: Nat, +w: +List<Nat>) -> Type:
  &kL: Nat -> &jL: Nat -> {Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, dEnd, i, kL, jL)) == True{} : Bool} & {Prefer.tokensFrom(input, kL, jL) == w : +List<Nat>}

law last_shift:
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d1: Nat
  for +d2: Nat
  for +dEq: {d1 == d2 : Nat}
  for +i: Nat
  for +w: +List<Nat>
  for last: LastOwn(free, gs, fuel, grammar, input, items, n, d1, i, w)
  LastOwn(free, gs, fuel, grammar, input, items, n, d2, i, w)

def last_shift(free, gs, fuel, grammar, input, items, n, d1, d2, dEq, i, w, last):
  match last:
    case (kL0, rest0):
      match rest0:
        case (jL0, (y0, tk0)):
          +kL = {kL0 : Nat}
          +jL = {jL0 : Nat}
          +y = Equal.trans(Bool, Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d2, i, kL, jL)), Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d1, i, kL, jL)), True{}, Equal.cong(Nat, Bool, v => Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, v, i, kL, jL)), d2, d1, Equal.sym(Nat, d1, d2, dEq)), y0)
          (kL, (jL, (y, tk0)))

law own_ok_last:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(k, input) : +List<Nat>}
  for +ok: {ownOk(t <> ts, free, gs, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}
  LastOwn(free, gs, fuel, grammar, input, items, n, Nat.add(dot, List.length(&2, Spec.Tree, t <> ts)), i, Spec.leaves([Spec.lastOf(ts, t)]))

def own_ok_last(ts, t, free, gs, fuel, grammar, input, items, n, dot, i, k, next, pos, ok):
  match ts:
    case Nil{}:
      +head = Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n+dot, i, k, Sub.endOf(t, k)))
      +tail = ownOk([], free, gs, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k))
      +y = Lemma.and_true_left(head, tail, ok)
      last_shift(free, gs, fuel, grammar, input, items, n, 1n+dot, Nat.add(dot, 1n), Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)), i, Spec.leaves([t]),
        (k, (Sub.endOf(t, k), (y, pos_head_tok(t, [], next, input, k, pos)))))
    case Con{+u, +us}:
      +head = Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n+dot, i, k, Sub.endOf(t, k)))
      +tail = ownOk(u <> us, free, gs, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k))
      rec = own_ok_last(us, u, free, gs, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k), next, pos_tail(t, u <> us, next, input, k, pos), Lemma.and_true_right_side(head, tail, ok))
      last_shift(free, gs, fuel, grammar, input, items, n, Nat.add(1n+dot, List.length(&2, Spec.Tree, u <> us)), Nat.add(dot, List.length(&2, Spec.Tree, t <> u <> us)), Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, u <> us)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, u <> us)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, u <> us))), i, Spec.leaves([Spec.lastOf(us, u)]), rec)

law holds_with_last:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +nEq: {List.length(&2, Spec.Tree, t <> ts) == n : Nat}
  for +yF: {Guard.guardsAt(gs, fuel, grammar, input, items, n, 1n, i, i, Sub.endOf(t, i)) == Guard.Yes{} : Guard.Tri}
  for last: LastOwn(free, gs, fuel, grammar, input, items, n, n, i, Spec.leaves([Spec.lastOf(ts, t)]))
  Spec.AllHold(grammar, gs, items, t <> ts, Lemma.dropN(i, input))

def holds_with_last(t, ts, free, gs, fuel, grammar, input, items, n, i, next, pos, nEq, yF, last):
  match last:
    case (kL0, rest0):
      match rest0:
        case (jL0, (y0, tk0)):
          +kL = {kL0 : Nat}
          +jL = {jL0 : Nat}
          +yL = own_yes(free, gs, fuel, grammar, input, items, n, n, i, kL, jL, y0)
          +nPos = Equal.trans(Bool, Nat.is_lt(0n, n), Nat.is_lt(0n, List.length(&2, Spec.Tree, t <> ts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(0n, v), n, List.length(&2, Spec.Tree, t <> ts), Equal.sym(Nat, List.length(&2, Spec.Tree, t <> ts), n, nEq)), {==})
          guards_hold_cons(gs, fuel, grammar, input, items, n, i, kL, jL, Sub.endOf(t, i), t <> ts, Spec.leaves([Spec.lastOf(ts, t)]), Spec.leaves([t]), yL, yF, Lemma.nat_eq_refl(n), nPos, tk0, pos_head_tok(t, ts, next, input, i, pos), {==}, {==})

# A node whose own steps all answered Yes keeps its rules.
law holds_at:
  for ch: +List<Spec.Tree>
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +nEq: {List.length(&2, Spec.Tree, ch) == n : Nat}
  for +ok: {ownOk(ch, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}
  Spec.AllHold(grammar, gs, items, ch, Lemma.dropN(i, input))

def holds_at(ch, free, gs, fuel, grammar, input, items, n, i, next, pos, nEq, ok):
  match ch:
    case Nil{}:
      +y = own_yes(free, gs, fuel, grammar, input, items, n, 0n, i, i, i, ok)
      +y0 = Equal.trans(Guard.Tri, Guard.guardsAt(gs, fuel, grammar, input, items, 0n, 0n, i, i, i), Guard.guardsAt(gs, fuel, grammar, input, items, n, 0n, i, i, i), Guard.Yes{}, Equal.cong(Nat, Guard.Tri, v => Guard.guardsAt(gs, fuel, grammar, input, items, v, 0n, i, i, i), 0n, n, nEq), y)
      guards_hold_nil(gs, fuel, grammar, input, items, i, y0)
    case Con{+t, +ts}:
      +head = Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, Sub.endOf(t, i)))
      +tail = ownOk(ts, free, gs, fuel, grammar, input, items, n, 1n, i, Sub.endOf(t, i))
      +yF = own_yes(free, gs, fuel, grammar, input, items, n, 1n, i, i, Sub.endOf(t, i), Lemma.and_true_left(head, tail, ok))
      last0 = own_ok_last(ts, t, free, gs, fuel, grammar, input, items, n, 0n, i, i, next, pos, ok)
      holds_with_last(t, ts, free, gs, fuel, grammar, input, items, n, i, next, pos, nEq, yF, last_shift(free, gs, fuel, grammar, input, items, n, List.length(&2, Spec.Tree, t <> ts), n, nEq, i, Spec.leaves([Spec.lastOf(ts, t)]), last0))

# ======== DIRECTION 2: THE RULES HOLD, SO NO OWN STEP ANSWERS NO ========
#
# A rule's Holds can be used once, and each rule is decided by one own step: @right by
# the first, every other rule by the last. So the rules are split up front into the
# @right part (sel = True) and the rest (sel = False), each handed to its step.

def HoldSel(sel: Bool, +grammar: +List<Spec.Production>, g: Spec.Guard, +items: +List<Spec.Item>, +ch: +List<Spec.Tree>, +ahead: +List<Nat>) -> Type:
  match sel g:
    case True{} Spec.RightAssoc{ids}:
      Spec.Holds(grammar, Spec.RightAssoc{ids}, items, ch, ahead)
    case True{} Spec.Ahead{ids}:
      Unit
    case True{} Spec.NotAhead{ids}:
      Unit
    case True{} Spec.LeftAssoc{ids}:
      Unit
    case False{} Spec.RightAssoc{ids}:
      Unit
    case False{} Spec.Ahead{ids}:
      Spec.Holds(grammar, Spec.Ahead{ids}, items, ch, ahead)
    case False{} Spec.NotAhead{ids}:
      Spec.Holds(grammar, Spec.NotAhead{ids}, items, ch, ahead)
    case False{} Spec.LeftAssoc{ids}:
      Spec.Holds(grammar, Spec.LeftAssoc{ids}, items, ch, ahead)

def HoldIf(b: Bool, +sel: Bool, +grammar: +List<Spec.Production>, +g: Spec.Guard, +items: +List<Spec.Item>, +ch: +List<Spec.Tree>, +ahead: +List<Nat>) -> Type:
  match b:
    case True{}:
      HoldSel(sel, grammar, g, items, ch, ahead)
    case False{}:
      Unit

def Part(+b: Bool, +sel: Bool, +grammar: +List<Spec.Production>, gs: +List<Spec.Guard>, +items: +List<Spec.Item>, +ch: +List<Spec.Tree>, +ahead: +List<Nat>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{+g, +rest}:
      HoldIf(b, sel, grammar, g, items, ch, ahead) & Part(b, sel, grammar, rest, items, ch, ahead)

def Split(+grammar: +List<Spec.Production>, +gs: +List<Spec.Guard>, +items: +List<Spec.Item>, +ch: +List<Spec.Tree>, +ahead: +List<Nat>) -> Type:
  Part(True{}, True{}, grammar, gs, items, ch, ahead) & Part(True{}, False{}, grammar, gs, items, ch, ahead)

def SplitOne(+grammar: +List<Spec.Production>, +g: Spec.Guard, +items: +List<Spec.Item>, +ch: +List<Spec.Tree>, +ahead: +List<Nat>) -> Type:
  HoldSel(True{}, grammar, g, items, ch, ahead) & HoldSel(False{}, grammar, g, items, ch, ahead)

law split_one:
  for g: Spec.Guard
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for h: Spec.Holds(grammar, g, items, ch, ahead)
  SplitOne(grammar, g, items, ch, ahead)

def split_one(g, grammar, items, ch, ahead, h):
  match g:
    case Spec.Ahead{+ids}:
      (Unit{}, h)
    case Spec.NotAhead{+ids}:
      (Unit{}, h)
    case Spec.LeftAssoc{+ids}:
      (Unit{}, h)
    case Spec.RightAssoc{+ids}:
      (h, Unit{})

law split_cons:
  for +grammar: +List<Spec.Production>
  for +g: Spec.Guard
  for +rest: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for one: SplitOne(grammar, g, items, ch, ahead)
  for more: Split(grammar, rest, items, ch, ahead)
  Split(grammar, g <> rest, items, ch, ahead)

def split_cons(grammar, g, rest, items, ch, ahead, one, more):
  match one:
    case (r1, l1):
      match more:
        case (r2, l2):
          ((r1, r2), (l1, l2))

law split_all:
  for gs: +List<Spec.Guard>
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for holds: Spec.AllHold(grammar, gs, items, ch, ahead)
  Split(grammar, gs, items, ch, ahead)

def split_all(gs, grammar, items, ch, ahead, holds):
  match gs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+g, +rest}:
      match holds:
        case (h1, hr):
          split_cons(grammar, g, rest, items, ch, ahead, split_one(g, grammar, items, ch, ahead, h1), split_all(rest, grammar, items, ch, ahead, hr))

law unit_part:
  for gs: +List<Spec.Guard>
  for +sel: Bool
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  Part(False{}, sel, grammar, gs, items, ch, ahead)

def unit_part(gs, sel, grammar, items, ch, ahead):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +rest}:
      (Unit{}, unit_part(rest, sel, grammar, items, ch, ahead))

# ---- One rule at one own step ----

law ahead_part:
  for bA: Bool
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +ch: +List<Spec.Tree>
  for +bT: {bA == True{} : Bool}
  for +e: {Guard.allAhead(ids, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}
  for h: HoldIf(bA, False{}, grammar, Spec.Ahead{ids}, items, ch, Lemma.dropN(i, input))
  Empty

def ahead_part(bA, ids, fuel, grammar, input, items, i, ch, bT, e, h):
  match bA:
    case True{}:
      all_ahead_no(ids, fuel, grammar, input, i, e, h)
    case False{}:
      Lemma.false_is_not_true(bT)

law not_ahead_part:
  for bA: Bool
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +ch: +List<Spec.Tree>
  for +bT: {bA == True{} : Bool}
  for +e: {Guard.noneAhead(ids, fuel, grammar, input, i) == Guard.No{} : Guard.Tri}
  for h: HoldIf(bA, False{}, grammar, Spec.NotAhead{ids}, items, ch, Lemma.dropN(i, input))
  Empty

def not_ahead_part(bA, ids, fuel, grammar, input, items, i, ch, bT, e, h):
  match bA:
    case True{}:
      none_ahead_no(ids, fuel, grammar, input, i, e, h)
    case False{}:
      Lemma.false_is_not_true(bT)

law left_part:
  for bA: Bool
  for bE: Bool
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +ch: +List<Spec.Tree>
  for +toks: +List<Nat>
  for +w: +List<Nat>
  for +aT: {bA == True{} : Bool}
  for +eT: {bE == True{} : Bool}
  for +tok: {toks == w : +List<Nat>}
  for +sp: SpIf(bE, Spec.lastSpell(ch), w)
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, toks) == Guard.No{} : Guard.Tri}
  for h: HoldIf(bA, False{}, grammar, Spec.LeftAssoc{ids}, items, ch, Lemma.dropN(i, input))
  Empty

def left_part(bA, bE, ids, fuel, grammar, input, items, i, ch, toks, w, aT, eT, tok, sp, e, h):
  match bA bE:
    case True{} True{}:
      edge_no_at(ids, fuel, grammar, items, toks, w, Spec.lastSpell(ch), tok, sp, e, h)
    case True{} False{}:
      Lemma.false_is_not_true(eT)
    case False{} _:
      Lemma.false_is_not_true(aT)

law right_part:
  for bF: Bool
  for +ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +i: Nat
  for +ch: +List<Spec.Tree>
  for +toks: +List<Nat>
  for +w: +List<Nat>
  for +fT: {bF == True{} : Bool}
  for +tok: TokIf(bF, toks, w)
  for +sp: SpIf(bF, Spec.firstSpell(ch), w)
  for +e: {Guard.edgeOk(ids, fuel, grammar, items, toks) == Guard.No{} : Guard.Tri}
  for h: HoldIf(bF, True{}, grammar, Spec.RightAssoc{ids}, items, ch, Lemma.dropN(i, input))
  Empty

def right_part(bF, ids, fuel, grammar, input, items, i, ch, toks, w, fT, tok, sp, e, h):
  match bF:
    case True{}:
      edge_no_at(ids, fuel, grammar, items, toks, w, Spec.firstSpell(ch), tok, sp, e, h)
    case False{}:
      Lemma.false_is_not_true(fT)

# A rule never answers No at an own step, given its part of the Holds. bA: the step is
# the last (d = n); bE: and the node has children; bF: the step is the first (d = 1).
law guard_not_no2:
  for g: Spec.Guard
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +kS: Nat
  for +jS: Nat
  for +ch: +List<Spec.Tree>
  for +w: +List<Nat>
  for +bA: Bool
  for +aEq: {Nat.is_eq(d, n) == bA : Bool}
  for +bE: Bool
  for +eEq: {Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)) == bE : Bool}
  for +tokL: {Prefer.tokensFrom(input, kS, jS) == w : +List<Nat>}
  for +spL: SpIf(bE, Spec.lastSpell(ch), w)
  for +bF: Bool
  for +fEq: {Nat.is_eq(d, 1n) == bF : Bool}
  for +tokF: TokIf(bF, Prefer.tokensFrom(input, i, jS), w)
  for +spF: SpIf(bF, Spec.firstSpell(ch), w)
  for hR: HoldIf(bF, True{}, grammar, g, items, ch, Lemma.dropN(i, input))
  for hL: HoldIf(bA, False{}, grammar, g, items, ch, Lemma.dropN(i, input))
  for +e: {Guard.guardAt(g, fuel, grammar, input, items, n, d, i, kS, jS) == Guard.No{} : Guard.Tri}
  Empty

def guard_not_no2(g, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, hR, hL, e):
  match g:
    case Spec.Ahead{+ids}:
      +bT = true_of_eq(bA, Nat.is_eq(d, n), aEq, last_only_no_b(Nat.is_eq(d, n), Guard.allAhead(ids, fuel, grammar, input, i), e))
      ahead_part(bA, ids, fuel, grammar, input, items, i, ch, bT, last_only_no_t(Nat.is_eq(d, n), Guard.allAhead(ids, fuel, grammar, input, i), e), hL)
    case Spec.NotAhead{+ids}:
      +bT = true_of_eq(bA, Nat.is_eq(d, n), aEq, last_only_no_b(Nat.is_eq(d, n), Guard.noneAhead(ids, fuel, grammar, input, i), e))
      not_ahead_part(bA, ids, fuel, grammar, input, items, i, ch, bT, last_only_no_t(Nat.is_eq(d, n), Guard.noneAhead(ids, fuel, grammar, input, i), e), hL)
    case Spec.LeftAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, kS, jS)
      +cond = Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n))
      +cT = last_only_no_b(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e)
      +aT = true_of_eq(bA, Nat.is_eq(d, n), aEq, Lemma.and_true_left(Nat.is_eq(d, n), Nat.is_lt(0n, n), cT))
      +eT = true_of_eq(bE, cond, eEq, cT)
      left_part(bA, bE, ids, fuel, grammar, input, items, i, ch, toks, w, aT, eT, tokL, spL, last_only_no_t(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e), hL)
    case Spec.RightAssoc{+ids}:
      +toks = Prefer.tokensFrom(input, i, jS)
      +cond = Bool.and(Nat.is_eq(d, 1n), Nat.is_lt(0n, n))
      +cT = last_only_no_b(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e)
      +fT = true_of_eq(bF, Nat.is_eq(d, 1n), fEq, Lemma.and_true_left(Nat.is_eq(d, 1n), Nat.is_lt(0n, n), cT))
      right_part(bF, ids, fuel, grammar, input, items, i, ch, toks, w, fT, tokF, spF, last_only_no_t(cond, Guard.edgeOk(ids, fuel, grammar, items, toks), e), hR)

law guards_not_no2:
  for gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +kS: Nat
  for +jS: Nat
  for +ch: +List<Spec.Tree>
  for +w: +List<Nat>
  for +bA: Bool
  for +aEq: {Nat.is_eq(d, n) == bA : Bool}
  for +bE: Bool
  for +eEq: {Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)) == bE : Bool}
  for +tokL: {Prefer.tokensFrom(input, kS, jS) == w : +List<Nat>}
  for +spL: SpIf(bE, Spec.lastSpell(ch), w)
  for +bF: Bool
  for +fEq: {Nat.is_eq(d, 1n) == bF : Bool}
  for +tokF: TokIf(bF, Prefer.tokensFrom(input, i, jS), w)
  for +spF: SpIf(bF, Spec.firstSpell(ch), w)
  for pR: Part(bF, True{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for pL: Part(bA, False{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for +e: {Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, kS, jS) == Guard.No{} : Guard.Tri}
  Empty

def guards_not_no2(gs, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, pR, pL, e):
  match gs:
    case Nil{}:
      tri_ne_yes_no(e)
    case Con{+g, +rest}:
      match pR:
        case (hR, rR):
          match pL:
            case (hL, rL):
              +a = Guard.guardAt(g, fuel, grammar, input, items, n, d, i, kS, jS)
              +b = Guard.guardsAt(rest, fuel, grammar, input, items, n, d, i, kS, jS)
              guards_no_pick(a, b, and_no(a, b, e),
                e1 => guard_not_no2(g, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, hR, hL, e1),
                e2 => guards_not_no2(rest, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, rR, rL, e2))

law succ_ne_add:
  for dot: Nat
  for +y: Nat
  {Nat.is_eq(1n+dot, Nat.add(dot, 2n+y)) == False{} : Bool}

def succ_ne_add(dot, y):
  match dot:
    case 0n:
      {==}
    case 1n+p:
      succ_ne_add(p, y)

law own_tri_free:
  for +free: Guard.Tri
  for +x: Guard.Tri
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  {Guard.unlessRefused(free, x) == x : Guard.Tri}

def own_tri_free(free, x, freeEq):
  Equal.cong(Guard.Tri, Guard.Tri, v => Guard.unlessRefused(v, x), free, Guard.Yes{}, freeEq)

# An own step that was decided, with its part of the rules, answered Yes.
law own_step:
  for +gs: +List<Spec.Guard>
  for +free: Guard.Tri
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +d: Nat
  for +i: Nat
  for +kS: Nat
  for +jS: Nat
  for +ch: +List<Spec.Tree>
  for +w: +List<Nat>
  for +bA: Bool
  for +aEq: {Nat.is_eq(d, n) == bA : Bool}
  for +bE: Bool
  for +eEq: {Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)) == bE : Bool}
  for +tokL: {Prefer.tokensFrom(input, kS, jS) == w : +List<Nat>}
  for +spL: SpIf(bE, Spec.lastSpell(ch), w)
  for +bF: Bool
  for +fEq: {Nat.is_eq(d, 1n) == bF : Bool}
  for +tokF: TokIf(bF, Prefer.tokensFrom(input, i, jS), w)
  for +spF: SpIf(bF, Spec.firstSpell(ch), w)
  for pR: Part(bF, True{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for pL: Part(bA, False{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +known: {Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, d, i, kS, jS)) == True{} : Bool}
  {Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d, i, kS, jS)) == True{} : Bool}

def own_step(gs, free, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, pR, pL, freeEq, known):
  +x = Guard.guardsAt(gs, fuel, grammar, input, items, n, d, i, kS, jS)
  +fx = own_tri_free(free, x, freeEq)
  +kx = Equal.trans(Bool, Guard.isKnown(x), Guard.isKnown(Guard.unlessRefused(free, x)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isKnown(v), x, Guard.unlessRefused(free, x), Equal.sym(Guard.Tri, Guard.unlessRefused(free, x), x, fx)), known)
  +yx = yes_of_known(x, kx, e => guards_not_no2(gs, fuel, grammar, input, items, n, d, i, kS, jS, ch, w, bA, aEq, bE, eEq, tokL, spL, bF, fEq, tokF, spF, pR, pL, e))
  Equal.trans(Bool, Guard.isYes(Guard.unlessRefused(free, x)), Guard.isYes(x), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.unlessRefused(free, x), x, fx), is_yes_of(x, yx))

# The own steps after the first, from dot (> 0) on, of a node with children ch.
law own_rest:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +gs: +List<Spec.Guard>
  for +free: Guard.Tri
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ch: +List<Spec.Tree>
  for +next: +List<Nat>
  for +dPos: {Nat.is_eq(1n+dot, 1n) == False{} : Bool}
  for +nEq: {Nat.add(dot, List.length(&2, Spec.Tree, t <> ts)) == n : Nat}
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(k, input) : +List<Nat>}
  for +lsp: {Spec.lastSpell(ch) == Spec.lastSpell(t <> ts) : Maybe<&2, +List<Nat>>}
  for pL: Part(True{}, False{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +kn: {ownKnown(t <> ts, free, gs, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}
  {ownOk(t <> ts, free, gs, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}

def own_rest(ts, t, gs, free, fuel, grammar, input, items, n, dot, i, k, ch, next, dPos, nEq, pos, lsp, pL, freeEq, kn):
  match ts:
    case Nil{}:
      +d = {1n+dot : Nat}
      +e = Sub.endOf(t, k)
      +w = Spec.leaves([t])
      +n1 = Equal.trans(Nat, n, Nat.add(dot, 1n), d, Equal.sym(Nat, Nat.add(dot, 1n), n, nEq), Lemma.add_one_right(dot))
      +aEq = Equal.trans(Bool, Nat.is_eq(d, n), Nat.is_eq(d, d), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(d, v), n, d, n1), Lemma.nat_eq_refl(d))
      +eEq = Equal.trans(Bool, Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)), Bool.and(Nat.is_eq(d, d), Nat.is_lt(0n, d)), True{}, Equal.cong(Nat, Bool, v => Bool.and(Nat.is_eq(d, v), Nat.is_lt(0n, v)), n, d, n1), Lemma.and_true_intro(Nat.is_eq(d, d), Nat.is_lt(0n, d), Lemma.nat_eq_refl(d), {==}))
      +tok = pos_head_tok(t, [], next, input, k, pos)
      +head = Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, d, i, k, e))
      +known = Lemma.and_true_left(head, ownKnown([], free, gs, fuel, grammar, input, items, n, d, i, e), kn)
      +y = own_step(gs, free, fuel, grammar, input, items, n, d, i, k, e, ch, w, True{}, aEq, True{}, eEq, tok, lsp, False{}, dPos, {==}, {==}, unit_part(gs, True{}, grammar, items, ch, Lemma.dropN(i, input)), pL, freeEq, known)
      Lemma.and_true_intro(Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d, i, k, e)), ownOk([], free, gs, fuel, grammar, input, items, n, d, i, e), y, {==})
    case Con{+u, +us}:
      +d = {1n+dot : Nat}
      +e = Sub.endOf(t, k)
      +w = Spec.leaves([t])
      +nE = Equal.trans(Nat, Nat.add(dot, 2n+List.length(&2, Spec.Tree, us)), Nat.add(dot, List.length(&2, Spec.Tree, t <> u <> us)), n, {==}, nEq)
      +aEq = Equal.trans(Bool, Nat.is_eq(d, n), Nat.is_eq(d, Nat.add(dot, 2n+List.length(&2, Spec.Tree, us))), False{}, Equal.cong(Nat, Bool, v => Nat.is_eq(d, v), n, Nat.add(dot, 2n+List.length(&2, Spec.Tree, us)), Equal.sym(Nat, Nat.add(dot, 2n+List.length(&2, Spec.Tree, us)), n, nE)), succ_ne_add(dot, List.length(&2, Spec.Tree, us)))
      +eEq = Equal.cong(Bool, Bool, v => Bool.and(v, Nat.is_lt(0n, n)), Nat.is_eq(d, n), False{}, aEq)
      +tok = pos_head_tok(t, u <> us, next, input, k, pos)
      +head = Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, d, i, k, e))
      +known = Lemma.and_true_left(head, ownKnown(u <> us, free, gs, fuel, grammar, input, items, n, d, i, e), kn)
      +y = own_step(gs, free, fuel, grammar, input, items, n, d, i, k, e, ch, w, False{}, aEq, False{}, eEq, tok, {==}, False{}, dPos, {==}, {==}, unit_part(gs, True{}, grammar, items, ch, Lemma.dropN(i, input)), unit_part(gs, False{}, grammar, items, ch, Lemma.dropN(i, input)), freeEq, known)
      +nEq2 = Equal.trans(Nat, Nat.add(1n+dot, List.length(&2, Spec.Tree, u <> us)), Nat.add(dot, 1n+List.length(&2, Spec.Tree, u <> us)), n, Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, u <> us)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, u <> us)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, u <> us))), nEq)
      +rest = own_rest(us, u, gs, free, fuel, grammar, input, items, n, d, i, e, ch, next, {==}, nEq2, pos_tail(t, u <> us, next, input, k, pos), lsp, pL, freeEq, Lemma.and_true_right_side(head, ownKnown(u <> us, free, gs, fuel, grammar, input, items, n, d, i, e), kn))
      Lemma.and_true_intro(Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, d, i, k, e)), ownOk(u <> us, free, gs, fuel, grammar, input, items, n, d, i, e), y, rest)

law ok_first:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +gs: +List<Spec.Guard>
  for +free: Guard.Tri
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +nEq: {List.length(&2, Spec.Tree, t <> ts) == n : Nat}
  for pR: Part(True{}, True{}, grammar, gs, items, t <> ts, Lemma.dropN(i, input))
  for pL: Part(True{}, False{}, grammar, gs, items, t <> ts, Lemma.dropN(i, input))
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +kn: {ownKnown(t <> ts, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}
  for +tok: {Prefer.tokensFrom(input, i, Sub.endOf(t, i)) == Spec.leaves([t]) : +List<Nat>}
  for +known: {Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, Sub.endOf(t, i))) == True{} : Bool}
  {ownOk(t <> ts, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}

def ok_first(ts, t, gs, free, fuel, grammar, input, items, n, i, next, pos, nEq, pR, pL, freeEq, kn, tok, known):
  match ts:
    case Nil{}:
      +e = Sub.endOf(t, i)
      +w = Spec.leaves([t])
      +aEq = Equal.sym(Bool, True{}, Nat.is_eq(1n, n), Equal.cong(Nat, Bool, v => Nat.is_eq(1n, v), 1n, n, nEq))
      +eEq = Equal.sym(Bool, True{}, Bool.and(Nat.is_eq(1n, n), Nat.is_lt(0n, n)), Equal.cong(Nat, Bool, v => Bool.and(Nat.is_eq(1n, v), Nat.is_lt(0n, v)), 1n, n, nEq))
      +y = own_step(gs, free, fuel, grammar, input, items, n, 1n, i, i, e, [t], w, True{}, aEq, True{}, eEq, tok, {==}, True{}, {==}, tok, {==}, pR, pL, freeEq, known)
      Lemma.and_true_intro(Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, e)), ownOk([], free, gs, fuel, grammar, input, items, n, 1n, i, e), y, {==})
    case Con{+u, +us}:
      +e = Sub.endOf(t, i)
      +w = Spec.leaves([t])
      +ch = {t <> u <> us : +List<Spec.Tree>}
      +aEq = Equal.sym(Bool, False{}, Nat.is_eq(1n, n), Equal.cong(Nat, Bool, v => Nat.is_eq(1n, v), List.length(&2, Spec.Tree, ch), n, nEq))
      +eEq = Equal.cong(Bool, Bool, v => Bool.and(v, Nat.is_lt(0n, n)), Nat.is_eq(1n, n), False{}, aEq)
      +y = own_step(gs, free, fuel, grammar, input, items, n, 1n, i, i, e, ch, w, False{}, aEq, False{}, eEq, tok, {==}, True{}, {==}, tok, {==}, pR, unit_part(gs, False{}, grammar, items, ch, Lemma.dropN(i, input)), freeEq, known)
      +rest = own_rest(us, u, gs, free, fuel, grammar, input, items, n, 1n, i, e, ch, next, {==}, nEq, pos_tail(t, u <> us, next, input, i, pos), {==}, pL, freeEq, Lemma.and_true_right_side(Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, e)), ownKnown(u <> us, free, gs, fuel, grammar, input, items, n, 1n, i, e), kn))
      Lemma.and_true_intro(Guard.isYes(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, e)), ownOk(u <> us, free, gs, fuel, grammar, input, items, n, 1n, i, e), y, rest)

law ok_split:
  for ch: +List<Spec.Tree>
  for +gs: +List<Spec.Guard>
  for +free: Guard.Tri
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +nEq: {List.length(&2, Spec.Tree, ch) == n : Nat}
  for pR: Part(True{}, True{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for pL: Part(True{}, False{}, grammar, gs, items, ch, Lemma.dropN(i, input))
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +kn: {ownKnown(ch, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}
  {ownOk(ch, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}

def ok_split(ch, gs, free, fuel, grammar, input, items, n, i, next, pos, nEq, pR, pL, freeEq, kn):
  match ch:
    case Nil{}:
      +aEq = Equal.sym(Bool, True{}, Nat.is_eq(0n, n), Equal.cong(Nat, Bool, v => Nat.is_eq(0n, v), 0n, n, nEq))
      +eEq = Equal.sym(Bool, False{}, Bool.and(Nat.is_eq(0n, n), Nat.is_lt(0n, n)), Equal.cong(Nat, Bool, v => Bool.and(Nat.is_eq(0n, v), Nat.is_lt(0n, v)), 0n, n, nEq))
      +w = Prefer.tokensFrom(input, i, i)
      own_step(gs, free, fuel, grammar, input, items, n, 0n, i, i, i, [], w, True{}, aEq, False{}, eEq, {==}, {==}, False{}, {==}, {==}, {==}, unit_part(gs, True{}, grammar, items, [], Lemma.dropN(i, input)), pL, freeEq, kn)
    case Con{+t, +ts}:
      +e = Sub.endOf(t, i)
      +w = Spec.leaves([t])
      +tok = pos_head_tok(t, ts, next, input, i, pos)
      +head = Guard.isKnown(ownTri(free, gs, fuel, grammar, input, items, n, 1n, i, i, e))
      +known = Lemma.and_true_left(head, ownKnown(ts, free, gs, fuel, grammar, input, items, n, 1n, i, e), kn)
      ok_first(ts, t, gs, free, fuel, grammar, input, items, n, i, next, pos, nEq, pR, pL, freeEq, kn, tok, known)

law ok_with:
  for ch: +List<Spec.Tree>
  for +gs: +List<Spec.Guard>
  for +free: Guard.Tri
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +nEq: {List.length(&2, Spec.Tree, ch) == n : Nat}
  for sp: Split(grammar, gs, items, ch, Lemma.dropN(i, input))
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +kn: {ownKnown(ch, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}
  {ownOk(ch, free, gs, fuel, grammar, input, items, n, 0n, i, i) == True{} : Bool}

def ok_with(ch, gs, free, fuel, grammar, input, items, n, i, next, pos, nEq, sp, freeEq, kn):
  match sp:
    case (pR, pL):
      ok_split(ch, gs, free, fuel, grammar, input, items, n, i, next, pos, nEq, pR, pL, freeEq, kn)

# ======== FROM STEPS TO OWN STEPS ========

# Whose own steps: a node of production `index` (OProd), or alternative a of the bracket
# at item dotB of the sequence with reversed path r0 (OAlt).
type Own is Data:
  OProd{}
  OAlt{r0: +List<Nat>, dotB: Nat, a: Nat, kind: Spec.Bracket, alts: +List<+List<Spec.Item>>}

def ownRpath(o: Own) -> +List<Nat>:
  match o:
    case OProd{}:
      []
    case OAlt{+r0, +dotB, +a, kind, alts}:
      a <> dotB <> r0

def ownGuards(o: Own, +gm: +List<Spec.GuardMark>, +index: Nat) -> +List<Spec.Guard>:
  match o:
    case OProd{}:
      Spec.prodGuards(gm, index)
    case OAlt{+r0, +dotB, +a, kind, alts}:
      Spec.altGuards(gm, index, Gll.reverseOnto(dotB <> r0, []), a)

def ownItems(o: Own, +grammar: +List<Spec.Production>, +index: Nat) -> +List<Spec.Item>:
  match o:
    case OProd{}:
      Spec.rhsOf(grammar, index)
    case OAlt{r0, dotB, +a, kind, +alts}:
      Spec.altOf(alts, a)

def ownFree(o: Own, +gm: +List<Spec.GuardMark>, +index: Nat) -> Guard.Tri:
  match o:
    case OProd{}:
      Guard.Yes{}
    case OAlt{+r0, +dotB, +a, +kind, alts}:
      Guard.loopFree(kind, Spec.altGuards(gm, index, Gll.reverseOnto(dotB <> r0, []), a))

def OwnFacts(o: Own, +grammar: +List<Spec.Production>, +index: Nat) -> Data:
  match o:
    case OProd{}:
      {0n == 0n : Nat}
    case OAlt{+r0, +dotB, a, +kind, +alts}:
      {Gll.nthItem(Gll.seqAt(grammar, index, r0), dotB) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}

# The Tri of an own step of the owner.
def oTri(+o: Own, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +index: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  +items = ownItems(o, grammar, index)
  ownTri(ownFree(o, gm, index), ownGuards(o, gm, index), fuel, grammar, input, items, List.length(&2, Spec.Item, items), d, i, k, j)

law decode_at:
  for o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +facts: OwnFacts(o, grammar, index)
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Guard.stepAt(d <> ownRpath(o), fuel, grammar, gm, input, index, i, k, j) == oTri(o, fuel, grammar, gm, input, index, d, i, k, j) : Guard.Tri}

def decode_at(o, fuel, grammar, gm, input, index, facts, d, i, k, j):
  match o:
    case OProd{}:
      {==}
    case OAlt{+r0, +dotB, +a, +kind, +alts}:
      %Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, r0), dotB), Some{Spec.Brack{kind, alts}}, facts) : {Guard.altStep(_, fuel, grammar, gm, input, index, Gll.reverseOnto(dotB <> r0, []), a, d, i, k, j) == oTri(OAlt{r0, dotB, a, kind, alts}, fuel, grammar, gm, input, index, d, i, k, j) : Guard.Tri}
      {==}

# The oracle's answer on an own step is the owner's Tri.
law decode:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Guard.stepTri(fuel, grammar, gm, input, Spec.at(index, prefix, d, i, k, j)) == oTri(o, fuel, grammar, gm, input, index, d, i, k, j) : Guard.Tri}

def decode(o, fuel, grammar, gm, input, index, prefix, pEq, facts, d, i, k, j):
  +rev = R.step_rev(ownRpath(o), prefix, d, pEq)
  Equal.trans(Guard.Tri, Guard.stepAt(Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), []), fuel, grammar, gm, input, index, i, k, j), Guard.stepAt(d <> ownRpath(o), fuel, grammar, gm, input, index, i, k, j), oTri(o, fuel, grammar, gm, input, index, d, i, k, j),
    Equal.cong(+List<Nat>, Guard.Tri, v => Guard.stepAt(v, fuel, grammar, gm, input, index, i, k, j), Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), []), d <> ownRpath(o), rev),
    decode_at(o, fuel, grammar, gm, input, index, facts, d, i, k, j))

# The own steps of a sequence's forest: the step of each child, or the empty step.
def ownSteps(f: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> +List<Spec.Bsr>:
  match f:
    case Nil{}:
      Spec.emptyStep(dot, index, prefix, i, k)
    case Con{+t, +ts}:
      Spec.at(index, prefix, 1n+dot, i, k, Sub.endOf(t, k)) <> ownSteps(ts, index, prefix, 1n+dot, i, Sub.endOf(t, k))

law own_sub:
  for f: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +set: +List<Spec.Bsr>
  for +all: {Spec.allIn(Spec.walk(f, False{}, index, prefix, dot, i, k), set) == True{} : Bool}
  {Spec.allIn(ownSteps(f, index, prefix, dot, i, k), set) == True{} : Bool}

def own_sub(f, index, prefix, dot, i, k, set, all):
  match f:
    case Nil{}:
      all
    case Con{+t, +ts}:
      +e = Sub.endOf(t, k)
      +x = Spec.at(index, prefix, 1n+dot, i, k, e)
      +inn = Sub.inner(t, index, prefix, dot, k)
      +wts = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
      +all2 = Equal.trans(Bool, Spec.allIn(x <> List.append(&2, Spec.Bsr, inn, wts), set), Spec.allIn(Spec.walk(t <> ts, False{}, index, prefix, dot, i, k), set), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(v, set), x <> List.append(&2, Spec.Bsr, inn, wts), Spec.walk(t <> ts, False{}, index, prefix, dot, i, k), Equal.sym(+List<Spec.Bsr>, Spec.walk(t <> ts, False{}, index, prefix, dot, i, k), x <> List.append(&2, Spec.Bsr, inn, wts), Sub.walk_cons(t, ts, index, prefix, dot, i, k))), all)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, inn, wts), set), all2)
      +rest = R.in_app_right(inn, wts, set, R.in_tail(x, List.append(&2, Spec.Bsr, inn, wts), set, all2))
      Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), set), mx, own_sub(ts, index, prefix, 1n+dot, i, e, set, rest))

def oOk(+f: +List<Spec.Tree>, +o: Own, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +index: Nat, +dot: Nat, +i: Nat, +k: Nat) -> Bool:
  +items = ownItems(o, grammar, index)
  ownOk(f, ownFree(o, gm, index), ownGuards(o, gm, index), fuel, grammar, input, items, List.length(&2, Spec.Item, items), dot, i, k)

def oKnown(+f: +List<Spec.Tree>, +o: Own, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +index: Nat, +dot: Nat, +i: Nat, +k: Nat) -> Bool:
  +items = ownItems(o, grammar, index)
  ownKnown(f, ownFree(o, gm, index), ownGuards(o, gm, index), fuel, grammar, input, items, List.length(&2, Spec.Item, items), dot, i, k)

law yes_at:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for m: {Spec.bsrMember(Spec.at(index, prefix, d, i, k, j), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
  {Guard.isYes(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)) == True{} : Bool}

def yes_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, d, i, k, j, m):
  +x = Spec.at(index, prefix, d, i, k, j)
  +dec = decode(o, fuel, grammar, gm, input, index, prefix, pEq, facts, d, i, k, j)
  Equal.trans(Bool, Guard.isYes(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)), Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, x)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), oTri(o, fuel, grammar, gm, input, index, d, i, k, j), Guard.stepTri(fuel, grammar, gm, input, x), Equal.sym(Guard.Tri, Guard.stepTri(fuel, grammar, gm, input, x), oTri(o, fuel, grammar, gm, input, index, d, i, k, j), dec)), gkept_keep(s, fuel, grammar, gm, input, x, m))

law known_at:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for m: {Spec.bsrMember(Spec.at(index, prefix, d, i, k, j), s) == True{} : Bool}
  {Guard.isKnown(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)) == True{} : Bool}

def known_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, d, i, k, j, m):
  +x = Spec.at(index, prefix, d, i, k, j)
  +dec = decode(o, fuel, grammar, gm, input, index, prefix, pEq, facts, d, i, k, j)
  Equal.trans(Bool, Guard.isKnown(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)), Guard.isKnown(Guard.stepTri(fuel, grammar, gm, input, x)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isKnown(v), oTri(o, fuel, grammar, gm, input, index, d, i, k, j), Guard.stepTri(fuel, grammar, gm, input, x), Equal.sym(Guard.Tri, Guard.stepTri(fuel, grammar, gm, input, x), oTri(o, fuel, grammar, gm, input, index, d, i, k, j), dec)), known_of(s, fuel, grammar, gm, input, okAll, x, m))

law kept_at:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for m: {Spec.bsrMember(Spec.at(index, prefix, d, i, k, j), s) == True{} : Bool}
  for +y: {Guard.isYes(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, d, i, k, j), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def kept_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, d, i, k, j, m, y):
  +x = Spec.at(index, prefix, d, i, k, j)
  +dec = decode(o, fuel, grammar, gm, input, index, prefix, pEq, facts, d, i, k, j)
  gkept_of(s, fuel, grammar, gm, input, x, m, Equal.trans(Bool, Guard.isYes(Guard.stepTri(fuel, grammar, gm, input, x)), Guard.isYes(oTri(o, fuel, grammar, gm, input, index, d, i, k, j)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.stepTri(fuel, grammar, gm, input, x), oTri(o, fuel, grammar, gm, input, index, d, i, k, j), dec), y))

law empty_ok:
  for dot: Nat
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
  {oOk([], o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}

def empty_ok(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, i, k, all):
  match dot:
    case 0n:
      yes_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 0n, i, k, k, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, k), Guard.guardKept(s, fuel, grammar, gm, input)), True{}, all))
    case 1n+p:
      {==}

# Own steps that are kept answered Yes.
law kept_own:
  for f: +List<Spec.Tree>
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(ownSteps(f, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
  {oOk(f, o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}

def kept_own(f, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, dot, i, k, all):
  match f:
    case Nil{}:
      empty_ok(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, i, k, all)
    case Con{+t, +ts}:
      +ks = Guard.guardKept(s, fuel, grammar, gm, input)
      +e = Sub.endOf(t, k)
      +x = Spec.at(index, prefix, 1n+dot, i, k, e)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, ks), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), ks), all)
      +rest = Lemma.and_true_right_side(Spec.bsrMember(x, ks), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), ks), all)
      Lemma.and_true_intro(Guard.isYes(oTri(o, fuel, grammar, gm, input, index, 1n+dot, i, k, e)), oOk(ts, o, fuel, grammar, gm, input, index, 1n+dot, i, e), yes_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 1n+dot, i, k, e, mx), kept_own(ts, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 1n+dot, i, e, rest))

law empty_known:
  for dot: Nat
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), s) == True{} : Bool}
  {oKnown([], o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}

def empty_known(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, i, k, all):
  match dot:
    case 0n:
      known_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, 0n, i, k, k, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, k), s), True{}, all))
    case 1n+p:
      {==}

# Own steps in an answered set were decided.
law known_own:
  for f: +List<Spec.Tree>
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(ownSteps(f, index, prefix, dot, i, k), s) == True{} : Bool}
  {oKnown(f, o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}

def known_own(f, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, dot, i, k, all):
  match f:
    case Nil{}:
      empty_known(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, i, k, all)
    case Con{+t, +ts}:
      +e = Sub.endOf(t, k)
      +x = Spec.at(index, prefix, 1n+dot, i, k, e)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, s), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), s), all)
      +rest = Lemma.and_true_right_side(Spec.bsrMember(x, s), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), s), all)
      Lemma.and_true_intro(Guard.isKnown(oTri(o, fuel, grammar, gm, input, index, 1n+dot, i, k, e)), oKnown(ts, o, fuel, grammar, gm, input, index, 1n+dot, i, e), known_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, 1n+dot, i, k, e, mx), known_own(ts, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, 1n+dot, i, e, rest))

law empty_kept:
  for dot: Nat
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), s) == True{} : Bool}
  for +ok: {oOk([], o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}
  {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def empty_kept(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, i, k, all, ok):
  match dot:
    case 0n:
      +x = Spec.at(index, prefix, 0n, i, k, k)
      Lemma.and_true_intro(Spec.bsrMember(x, Guard.guardKept(s, fuel, grammar, gm, input)), True{}, kept_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 0n, i, k, k, Lemma.and_true_left(Spec.bsrMember(x, s), True{}, all), ok), {==})
    case 1n+p:
      {==}

# Own steps in the set that answered Yes are kept.
law own_kept:
  for f: +List<Spec.Tree>
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +all: {Spec.allIn(ownSteps(f, index, prefix, dot, i, k), s) == True{} : Bool}
  for +ok: {oOk(f, o, fuel, grammar, gm, input, index, dot, i, k) == True{} : Bool}
  {Spec.allIn(ownSteps(f, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def own_kept(f, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, dot, i, k, all, ok):
  match f:
    case Nil{}:
      empty_kept(dot, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, i, k, all, ok)
    case Con{+t, +ts}:
      +ks = Guard.guardKept(s, fuel, grammar, gm, input)
      +e = Sub.endOf(t, k)
      +x = Spec.at(index, prefix, 1n+dot, i, k, e)
      +hy = Guard.isYes(oTri(o, fuel, grammar, gm, input, index, 1n+dot, i, k, e))
      +ry = oOk(ts, o, fuel, grammar, gm, input, index, 1n+dot, i, e)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, s), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), s), all)
      +rest = Lemma.and_true_right_side(Spec.bsrMember(x, s), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), s), all)
      Lemma.and_true_intro(Spec.bsrMember(x, ks), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, e), ks), kept_at(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 1n+dot, i, k, e, mx, Lemma.and_true_left(hy, ry, ok)), own_kept(ts, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 1n+dot, i, e, rest, Lemma.and_true_right_side(hy, ry, ok)))

# ======== A NODE, A PICK, A ROUND ========

law free_of_known:
  for f: +List<Spec.Tree>
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +k: Nat
  for +kn: {ownKnown(f, free, gs, fuel, grammar, input, items, n, 0n, i, k) == True{} : Bool}
  {free == Guard.Yes{} : Guard.Tri}

def free_of_known(f, free, gs, fuel, grammar, input, items, n, i, k, kn):
  match f:
    case Nil{}:
      unless_known(free, Guard.guardsAt(gs, fuel, grammar, input, items, n, 0n, i, k, k), kn)
    case Con{+t, +ts}:
      +x = Guard.guardsAt(gs, fuel, grammar, input, items, n, 1n, i, k, Sub.endOf(t, k))
      unless_known(free, x, Lemma.and_true_left(Guard.isKnown(Guard.unlessRefused(free, x)), ownKnown(ts, free, gs, fuel, grammar, input, items, n, 1n, i, Sub.endOf(t, k)), kn))

law free_of_ok:
  for f: +List<Spec.Tree>
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +i: Nat
  for +k: Nat
  for +ok: {ownOk(f, free, gs, fuel, grammar, input, items, n, 0n, i, k) == True{} : Bool}
  {free == Guard.Yes{} : Guard.Tri}

def free_of_ok(f, free, gs, fuel, grammar, input, items, n, i, k, ok):
  match f:
    case Nil{}:
      unless_free(free, Guard.guardsAt(gs, fuel, grammar, input, items, n, 0n, i, k, k), ok)
    case Con{+t, +ts}:
      +x = Guard.guardsAt(gs, fuel, grammar, input, items, n, 1n, i, k, Sub.endOf(t, k))
      unless_free(free, x, Lemma.and_true_left(Guard.isYes(Guard.unlessRefused(free, x)), ownOk(ts, free, gs, fuel, grammar, input, items, n, 1n, i, Sub.endOf(t, k)), ok))

law gs_empty:
  for gs: +List<Spec.Guard>
  for e: {List.is_empty(&2, Spec.Guard, gs) == True{} : Bool}
  {gs == [] : +List<Spec.Guard>}

def gs_empty(gs, e):
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      Empty.absurd({g <> rest == [] : +List<Spec.Guard>}, Lemma.false_is_not_true(e))

law yes_if_true:
  for b: Bool
  for e: {Guard.yesIf(b) == Guard.Yes{} : Guard.Tri}
  {b == True{} : Bool}

def yes_if_true(b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, tri_ne_unknown_yes(e))

# A loop's alternative whose own steps are not refused carries no rules.
law loop_free_empty:
  for kind: Spec.Bracket
  for +gs: +List<Spec.Guard>
  for isL: {Gll.isLoop(kind) == True{} : Bool}
  for e: {Guard.loopFree(kind, gs) == Guard.Yes{} : Guard.Tri}
  {gs == [] : +List<Spec.Guard>}

def loop_free_empty(kind, gs, isL, e):
  match kind:
    case Spec.Group{}:
      Empty.absurd({gs == [] : +List<Spec.Guard>}, Lemma.false_is_not_true(isL))
    case Spec.Optional{}:
      Empty.absurd({gs == [] : +List<Spec.Guard>}, Lemma.false_is_not_true(isL))
    case Spec.Closure{}:
      gs_empty(gs, yes_if_true(List.is_empty(&2, Spec.Guard, gs), e))
    case Spec.Positive{}:
      gs_empty(gs, yes_if_true(List.is_empty(&2, Spec.Guard, gs), e))

law no_rules_hold:
  for +grammar: +List<Spec.Production>
  for +gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for +e: {gs == [] : +List<Spec.Guard>}
  Spec.AllHold(grammar, gs, items, ch, ahead)

def no_rules_hold(grammar, gs, items, ch, ahead, e):
  %Equal.sym(+List<Spec.Guard>, gs, [], e) : Spec.AllHold(grammar, _, items, ch, ahead)
  Unit{}

law ok_no_rules:
  for f: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  {ownOk(f, Guard.Yes{}, [], fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}

def ok_no_rules(f, fuel, grammar, input, items, n, dot, i, k):
  match f:
    case Nil{}:
      match dot:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+t, +ts}:
      ok_no_rules(ts, fuel, grammar, input, items, n, 1n+dot, i, Sub.endOf(t, k))

law ok_free_empty:
  for +f: +List<Spec.Tree>
  for +free: Guard.Tri
  for +gs: +List<Spec.Guard>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +n: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +freeEq: {free == Guard.Yes{} : Guard.Tri}
  for +gsEq: {gs == [] : +List<Spec.Guard>}
  {ownOk(f, free, gs, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}

def ok_free_empty(f, free, gs, fuel, grammar, input, items, n, dot, i, k, freeEq, gsEq):
  %Equal.sym(Guard.Tri, free, Guard.Yes{}, freeEq) : {ownOk(f, _, gs, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}
  %Equal.sym(+List<Spec.Guard>, gs, [], gsEq) : {ownOk(f, Guard.Yes{}, _, fuel, grammar, input, items, n, dot, i, k) == True{} : Bool}
  ok_no_rules(f, fuel, grammar, input, items, n, dot, i, k)

law hold_back:
  for +grammar: +List<Spec.Production>
  for +gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +a1: +List<Nat>
  for +a2: +List<Nat>
  for +eq: {a1 == a2 : +List<Nat>}
  for h: Spec.AllHold(grammar, gs, items, ch, a2)
  Spec.AllHold(grammar, gs, items, ch, a1)

def hold_back(grammar, gs, items, ch, a1, a2, eq, h):
  %Equal.sym(+List<Nat>, a1, a2, eq) : Spec.AllHold(grammar, gs, items, ch, _)
  h

law hold_fwd:
  for +grammar: +List<Spec.Production>
  for +gs: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +a1: +List<Nat>
  for +a2: +List<Nat>
  for +eq: {a1 == a2 : +List<Nat>}
  for h: Spec.AllHold(grammar, gs, items, ch, a1)
  Spec.AllHold(grammar, gs, items, ch, a2)

def hold_fwd(grammar, gs, items, ch, a1, a2, eq, h):
  %eq : Spec.AllHold(grammar, gs, items, ch, _)
  h

# ---- Direction 1 at a node or pick: its rules hold ----

law owner_holds:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(k, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, ownItems(o, grammar, index)) == True{} : Bool}
  for +all: {Spec.allIn(Spec.walk(ch, False{}, index, prefix, 0n, k, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
  Spec.AllHold(grammar, ownGuards(o, gm, index), ownItems(o, grammar, index), ch, List.append(&2, Nat, Spec.leaves(ch), next))

def owner_holds(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, ch, k, next, pos, fit, all):
  +items = ownItems(o, grammar, index)
  +ok = kept_own(ch, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 0n, k, k, own_sub(ch, index, prefix, 0n, k, k, Guard.guardKept(s, fuel, grammar, gm, input), all))
  h = holds_at(ch, ownFree(o, gm, index), ownGuards(o, gm, index), fuel, grammar, input, items, List.length(&2, Spec.Item, items), k, next, pos, Fits.fits_count(ch, grammar, items, fit), ok)
  hold_back(grammar, ownGuards(o, gm, index), items, ch, List.append(&2, Nat, Spec.leaves(ch), next), Lemma.dropN(k, input), pos, h)

# ---- Direction 2 at a node or pick: its own steps are kept ----

law owner_kept:
  for +o: Own
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +index: Nat
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(ownRpath(o), []) : +List<Nat>}
  for +facts: OwnFacts(o, grammar, index)
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
  for +ch: +List<Spec.Tree>
  for +k: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(k, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, ownItems(o, grammar, index)) == True{} : Bool}
  for +allS: {Spec.allIn(Spec.walk(ch, False{}, index, prefix, 0n, k, k), s) == True{} : Bool}
  for holds: Spec.AllHold(grammar, ownGuards(o, gm, index), ownItems(o, grammar, index), ch, List.append(&2, Nat, Spec.leaves(ch), next))
  {Spec.allIn(ownSteps(ch, index, prefix, 0n, k, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def owner_kept(o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, ch, k, next, pos, fit, allS, holds):
  +items = ownItems(o, grammar, index)
  +gs = ownGuards(o, gm, index)
  +free = ownFree(o, gm, index)
  +n = List.length(&2, Spec.Item, items)
  +ownS = own_sub(ch, index, prefix, 0n, k, k, s, allS)
  +kn = known_own(ch, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, okAll, 0n, k, k, ownS)
  +freeEq = free_of_known(ch, free, gs, fuel, grammar, input, items, n, k, k, kn)
  h2 = hold_fwd(grammar, gs, items, ch, List.append(&2, Nat, Spec.leaves(ch), next), Lemma.dropN(k, input), pos, holds)
  +ok = ok_with(ch, gs, free, fuel, grammar, input, items, n, k, next, pos, Fits.fits_count(ch, grammar, items, fit), split_all(gs, grammar, items, ch, Lemma.dropN(k, input), h2), freeEq, kn)
  own_kept(ch, o, fuel, grammar, gm, input, index, prefix, pEq, facts, s, 0n, k, k, ownS, ok)

# ======== DIRECTION 1: A TREE OF KEPT STEPS IS ADMISSIBLE ========

def AdmReady(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def AdmDone(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>, +after: +List<Nat>) -> Type:
  match rounds:
    case False{}:
      Spec.Admissible(grammar, gm, forest, items, index, prefix, dot, after)
    case True{}:
      Spec.RoundsAdmissible(grammar, gm, forest, alts, index, prefix, after)

def AdmIH(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @after: +List<Nat> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> AdmReady(rounds, grammar, gm, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts) -> AdmDone(rounds, grammar, gm, forest, items, index, prefix, dot, alts, after)

# The rules on the alternative of the bracket at a path, read along an equal path.
law guards_path:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +index: Nat
  for +p1: +List<Nat>
  for +p2: +List<Nat>
  for +eq: {p1 == p2 : +List<Nat>}
  for +a: Nat
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for h: Spec.AllHold(grammar, Spec.altGuards(gm, index, p2, a), items, ch, ahead)
  Spec.AllHold(grammar, Spec.altGuards(gm, index, p1, a), items, ch, ahead)

def guards_path(grammar, gm, index, p1, p2, eq, a, items, ch, ahead, h):
  %Equal.sym(+List<Nat>, p1, p2, eq) : Spec.AllHold(grammar, Spec.altGuards(gm, index, _, a), items, ch, ahead)
  h

# The children of a node or pick, and their position.
law pos_children:
  for +lch: +List<Nat>
  for +lts: +List<Nat>
  for +after: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +pos: {List.append(&2, Nat, List.append(&2, Nat, lch, lts), after) == Lemma.dropN(k, input) : +List<Nat>}
  {List.append(&2, Nat, lch, List.append(&2, Nat, lts, after)) == Lemma.dropN(k, input) : +List<Nat>}

def pos_children(lch, lts, after, input, k, pos):
  Equal.trans(+List<Nat>, List.append(&2, Nat, lch, List.append(&2, Nat, lts, after)), List.append(&2, Nat, List.append(&2, Nat, lch, lts), after), Lemma.dropN(k, input), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lch, lts), after), List.append(&2, Nat, lch, List.append(&2, Nat, lts, after)), G.nat_append_assoc(lch, lts, after)), pos)

law adm_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: AdmIH(grammar, gm, input, fuel, s, ch)
  for ihTs: AdmIH(grammar, gm, input, fuel, s, ts)
  AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after)

def adm_node(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
          +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +posCh = pos_children(w, lts, after, input, k, pos)
          +posTs = pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          (owner_holds(OProd{}, fuel, grammar, gm, input, q, [], {==}, {==}, s, ch, k, next, posCh, fitCh, allCh),
            (ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, next, {==}, posCh, ({==}, (fitCh, allCh))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))

law adm_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: AdmIH(grammar, gm, input, fuel, s, ch)
  for ihTs: AdmIH(grammar, gm, input, fuel, s, ts)
  AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after)

def adm_pick(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
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
          +posCh = pos_children(w, lts, after, input, k, pos)
          +posTs = pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
          +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
          +o = {OAlt{rpath, dot, a, Spec.Group{}, balts} : Own}
          (guards_path(grammar, gm, index, path, Gll.reverseOnto(rpath, [dot]), pathEq, a, Spec.altOf(balts, a), ch, List.append(&2, Nat, w, next), owner_holds(o, fuel, grammar, gm, input, index, pre, pEqA, itemEq, s, ch, k, next, posCh, fitCh, allCh)),
            (ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, allCh2))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
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
          +posCh = pos_children(w, lts, after, input, k, pos)
          +posTs = pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
          +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
          +o = {OAlt{rpath, dot, a, Spec.Optional{}, balts} : Own}
          (guards_path(grammar, gm, index, path, Gll.reverseOnto(rpath, [dot]), pathEq, a, Spec.altOf(balts, a), ch, List.append(&2, Nat, w, next), owner_holds(o, fuel, grammar, gm, input, index, pre, pEqA, itemEq, s, ch, k, next, posCh, fitCh, allCh)),
            (ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, allCh2))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, allTs)))))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))

law adm_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: AdmIH(grammar, gm, input, fuel, s, ts)
  AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after)

def adm_leaf(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), Guard.guardKept(s, fuel, grammar, gm, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, after, pEq, pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Leaf{k0} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))

law adm_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihTs: AdmIH(grammar, gm, input, fuel, s, ts)
  AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after)

def adm_skip(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Skip{} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, allTs)))

law adm_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihRs: AdmIH(grammar, gm, input, fuel, s, rs)
  for ihTs: AdmIH(grammar, gm, input, fuel, s, ts)
  AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after)

def adm_loop(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
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
          +posRs = pos_children(w, lts, after, input, k, pos)
          +posTs = pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, allRs)))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, allTs))))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
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
          +posRs = pos_children(w, lts, after, input, k, pos)
          +posTs = pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, allRs)))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, allTs))))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, all0)):
          Empty.absurd(AdmDone(False{}, grammar, gm, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))

law adm_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(True{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts)
  for ihCh: AdmIH(grammar, gm, input, fuel, s, ch)
  for ihRest: AdmIH(grammar, gm, input, fuel, s, rest)
  AdmDone(True{}, grammar, gm, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, after)

def adm_round(rpath, grammar, gm, input, fuel, s, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(AdmDone(True{}, grammar, gm, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, after), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, all0))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lr, after)
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +allCh = R.in_app_left(wCh, wRest, kept, allW)
          +allRest = R.in_app_right(wCh, wRest, kept, allW)
          +posCh = pos_children(w, lr, after, input, k, pos)
          +posRest = pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +o = {OAlt{outer, m, a, kind, alts} : Own}
          +gsO = Spec.altGuards(gm, index, Gll.reverseOnto(m <> outer, []), a)
          +items2 = Spec.altOf(alts, a)
          +ok = kept_own(ch, o, fuel, grammar, gm, input, index, pre, pEqA, loopIt, s, 0n, i, k, own_sub(ch, index, pre, 0n, i, k, kept, allCh))
          +freeEq = free_of_ok(ch, Guard.loopFree(kind, gsO), gsO, fuel, grammar, input, items2, List.length(&2, Spec.Item, items2), i, k, ok)
          +gsEq = loop_free_empty(kind, gsO, isL, freeEq)
          +gsEq2 = Equal.trans(+List<Spec.Guard>, Spec.altGuards(gm, index, prefix, a), gsO, [], Equal.cong(+List<Nat>, +List<Spec.Guard>, v => Spec.altGuards(gm, index, v, a), prefix, Gll.reverseOnto(m <> outer, []), pEq), gsEq)
          (no_rules_hold(grammar, Spec.altGuards(gm, index, prefix, a), items2, ch, List.append(&2, Nat, w, next), gsEq2),
            (ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, next, pEqA, posCh, (itemsEqR, (fitCh, allCh))),
              ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, after, pEq, posRest, (loopIt, (isL, (fitRest, allRest))))))

law adm_nil:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +after: +List<Nat>
  Spec.Admissible(grammar, gm, [], items, index, prefix, dot, after)

def adm_nil(items, grammar, gm, index, prefix, dot, after):
  match items:
    case Nil{}:
      Unit{}
    case Con{it, rest}:
      Unit{}

law adm_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
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
  for ready: AdmReady(rounds, grammar, gm, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts)
  AdmDone(rounds, grammar, gm, forest, items, index, prefix, dot, alts, after)

def adm_walk(forest, rounds, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, items, kind, alts, after, pEq, pos, ready):
  match forest rounds:
    case Nil{} False{}:
      adm_nil(items, grammar, gm, index, prefix, dot, after)
    case Nil{} True{}:
      Unit{}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      adm_leaf(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ts, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      adm_node(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ch, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ts, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      adm_pick(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ch, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ts, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      adm_skip(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ts, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      adm_loop(items, grammar, gm, input, fuel, s, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(rs, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ts, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      adm_round(rpath, grammar, gm, input, fuel, s, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(ch, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => adm_walk(rest, ri, grammar, gm, input, fuel, s, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(AdmDone(True{}, grammar, gm, Spec.Leaf{k0} <> rest, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(AdmDone(True{}, grammar, gm, Spec.Node{q, ch} <> rest, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(AdmDone(True{}, grammar, gm, Spec.Skip{} <> rest, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, all0))):
          Empty.absurd(AdmDone(True{}, grammar, gm, Spec.Loop{rs} <> rest, items, index, prefix, dot, alts, after), Lemma.false_is_not_true(fit0))

# ======== DIRECTION 2: AN ADMISSIBLE TREE USES ONLY KEPT STEPS ========

def KeepReady(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +after: +List<Nat>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), s) == True{} : Bool} & {Spec.allIn(ownSteps(forest, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool} & Spec.Admissible(grammar, gm, forest, items, index, prefix, dot, after)
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), s) == True{} : Bool} & Spec.RoundsAdmissible(grammar, gm, forest, alts, index, prefix, after)

def KeepDone(rounds: Bool, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Data:
  {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def KeepIH(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @after: +List<Nat> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> KeepReady(rounds, grammar, gm, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after) -> KeepDone(rounds, grammar, gm, input, fuel, s, forest, index, prefix, dot, i, k)

law guards_path_back:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +index: Nat
  for +p1: +List<Nat>
  for +p2: +List<Nat>
  for +eq: {p1 == p2 : +List<Nat>}
  for +a: Nat
  for +items: +List<Spec.Item>
  for +ch: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for h: Spec.AllHold(grammar, Spec.altGuards(gm, index, p1, a), items, ch, ahead)
  Spec.AllHold(grammar, Spec.altGuards(gm, index, p2, a), items, ch, ahead)

def guards_path_back(grammar, gm, index, p1, p2, eq, a, items, ch, ahead, h):
  %eq : Spec.AllHold(grammar, Spec.altGuards(gm, index, _, a), items, ch, ahead)
  h

# A node or pick: its own step, the steps inside it, and the rest.
law keep_join:
  for +x: Spec.Bsr
  for +wCh: +List<Spec.Bsr>
  for +wTs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +mx: {Spec.bsrMember(x, set) == True{} : Bool}
  for +hc: {Spec.allIn(wCh, set) == True{} : Bool}
  for +ht: {Spec.allIn(wTs, set) == True{} : Bool}
  {Spec.allIn(x <> List.append(&2, Spec.Bsr, wCh, wTs), set) == True{} : Bool}

def keep_join(x, wCh, wTs, set, mx, hc, ht):
  Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wTs), set), mx, G.all_in_app(wCh, wTs, set, hc, ht))

law keep_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihCh: KeepIH(grammar, gm, input, fuel, s, ch)
  for ihTs: KeepIH(grammar, gm, input, fuel, s, ts)
  KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k)

def keep_node(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hN, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
              +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = pos_children(w, lts, after, input, k, pos)
              +posTs = pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
              +ownCh = owner_kept(OProd{}, fuel, grammar, gm, input, q, [], {==}, {==}, s, okAll, ch, k, next, posCh, fitCh, allCh, hN)
              +kCh = ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, next, {==}, posCh, ({==}, (fitCh, (allCh, (ownCh, admCh)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              keep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law keep_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihCh: KeepIH(grammar, gm, input, fuel, s, ch)
  for ihTs: KeepIH(grammar, gm, input, fuel, s, ts)
  KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)

def keep_pick(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hP, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
              +pre = List.append(&2, Nat, prefix, [dot, a])
              +path = List.append(&2, Nat, prefix, [dot])
              +pre2 = List.append(&2, Nat, path, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
              +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = pos_children(w, lts, after, input, k, pos)
              +posTs = pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
              +assoc = G.nat_append_assoc(prefix, [dot], [a])
              +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), allCh)
              +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
              +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
              +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
              +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
              +o = {OAlt{rpath, dot, a, Spec.Group{}, balts} : Own}
              hP2 = guards_path_back(grammar, gm, index, path, Gll.reverseOnto(rpath, [dot]), pathEq, a, Spec.altOf(balts, a), ch, List.append(&2, Nat, w, next), hP)
              +ownCh = owner_kept(o, fuel, grammar, gm, input, index, pre2, pEq2, itemEq, s, okAll, ch, k, next, posCh, fitCh, allCh2, hP2)
              +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, (allCh2, (ownCh, admCh)))))
              +kCh = Equal.trans(Bool, Spec.allIn(wCh, kept), Spec.allIn(wCh2, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              keep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hP, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
              +pre = List.append(&2, Nat, prefix, [dot, a])
              +path = List.append(&2, Nat, prefix, [dot])
              +pre2 = List.append(&2, Nat, path, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
              +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = pos_children(w, lts, after, input, k, pos)
              +posTs = pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
              +assoc = G.nat_append_assoc(prefix, [dot], [a])
              +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), allCh)
              +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
              +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
              +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
              +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
              +o = {OAlt{rpath, dot, a, Spec.Optional{}, balts} : Own}
              hP2 = guards_path_back(grammar, gm, index, path, Gll.reverseOnto(rpath, [dot]), pathEq, a, Spec.altOf(balts, a), ch, List.append(&2, Nat, w, next), hP)
              +ownCh = owner_kept(o, fuel, grammar, gm, input, index, pre2, pEq2, itemEq, s, okAll, ch, k, next, posCh, fitCh, allCh2, hP2)
              +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, pEq2, posCh, (itemsEq2, (fitCh, (allCh2, (ownCh, admCh)))))
              +kCh = Equal.trans(Bool, Spec.allIn(wCh, kept), Spec.allIn(wCh2, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              keep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law keep_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihTs: KeepIH(grammar, gm, input, fuel, s, ts)
  KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k)

def keep_leaf(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, 1n+k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, 1n+k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, 1n+k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, after, pEq, pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), kept), mx, kTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law keep_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihTs: KeepIH(grammar, gm, input, fuel, s, ts)
  KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k)

def keep_skip(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Skip{} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), kept), mx, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Skip{} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
          +kept = Guard.guardKept(s, fuel, grammar, gm, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, pEq, pos_tail(Spec.Skip{}, ts, after, input, k, pos), (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), kept), mx, kTs)

law keep_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihRs: KeepIH(grammar, gm, input, fuel, s, rs)
  for ihTs: KeepIH(grammar, gm, input, fuel, s, ts)
  KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k)

def keep_loop(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (admRs, admTs):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
              +w = Spec.leaves(rs)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
              +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
              +path = List.append(&2, Nat, prefix, [dot])
              +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), s, allW)
              +allRs = R.in_app_left(wRs, wTs, s, allIn2)
              +allTs = R.in_app_right(wRs, wTs, s, allIn2)
              +posRs = pos_children(w, lts, after, input, k, pos)
              +posTs = pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
              +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
              +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, (allRs, admRs)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              keep_join(hx, wRs, wTs, kept, mx, kRs, kTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (admRs, admTs):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(ownSteps(Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
              +w = Spec.leaves(rs)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
              +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
              +path = List.append(&2, Nat, prefix, [dot])
              +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), s, allW)
              +allRs = R.in_app_left(wRs, wTs, s, allIn2)
              +allTs = R.in_app_right(wRs, wTs, s, allIn2)
              +posRs = pos_children(w, lts, after, input, k, pos)
              +posTs = pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
              +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
              +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, next, pEqL, posRs, (itemEq, ({==}, (fitRs, (allRs, admRs)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, pEq, posTs, (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              keep_join(hx, wRs, wTs, kept, mx, kRs, kTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(KeepDone(False{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law keep_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(True{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  for ihCh: KeepIH(grammar, gm, input, fuel, s, ch)
  for ihRest: KeepIH(grammar, gm, input, fuel, s, rest)
  KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k)

def keep_round(rpath, grammar, gm, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, (all0, adm0)))):
          match adm0:
            case (hR, (admCh, admRest)):
              +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
              +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +w = Spec.leaves(ch)
              +lr = Spec.leaves(rest)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lr, after)
              +kept = Guard.guardKept(s, fuel, grammar, gm, input)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
              +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
              +pre = List.append(&2, Nat, prefix, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
              +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
              +allCh = R.in_app_left(wCh, wRest, s, allW)
              +allRest = R.in_app_right(wCh, wRest, s, allW)
              +posCh = pos_children(w, lr, after, input, k, pos)
              +posRest = pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
              +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
              +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
              +o = {OAlt{outer, m, a, kind, alts} : Own}
              +gsO = Spec.altGuards(gm, index, Gll.reverseOnto(m <> outer, []), a)
              +items2 = Spec.altOf(alts, a)
              +n2 = List.length(&2, Spec.Item, items2)
              +ownS = own_sub(ch, index, pre, 0n, i, k, s, allCh)
              +kn = known_own(ch, o, fuel, grammar, gm, input, index, pre, pEqA, loopIt, s, okAll, 0n, i, k, ownS)
              +freeEq = free_of_known(ch, Guard.loopFree(kind, gsO), gsO, fuel, grammar, input, items2, n2, i, k, kn)
              +gsEq = loop_free_empty(kind, gsO, isL, freeEq)
              +ok = ok_free_empty(ch, Guard.loopFree(kind, gsO), gsO, fuel, grammar, input, items2, n2, 0n, i, k, freeEq, gsEq)
              +ownCh = own_kept(ch, o, fuel, grammar, gm, input, index, pre, pEqA, loopIt, s, 0n, i, k, ownS, ok)
              +kCh = ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, next, pEqA, posCh, (itemsEqR, (fitCh, (allCh, (ownCh, admCh)))))
              +kRest = ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, after, pEq, posRest, (loopIt, (isL, (fitRest, (allRest, admRest)))))
              G.all_in_app(wCh, wRest, kept, kCh, kRest)

law keep_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
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
  for ready: KeepReady(rounds, grammar, gm, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after)
  KeepDone(rounds, grammar, gm, input, fuel, s, forest, index, prefix, dot, i, k)

def keep_walk(forest, rounds, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, items, kind, alts, after, pEq, pos, ready):
  match forest rounds:
    case Nil{} False{}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          own0
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      keep_leaf(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, k0, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ts, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      keep_node(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, q, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ch, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ts, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      keep_pick(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, a, ch, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ch, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ts, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      keep_skip(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ts, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      keep_loop(items, grammar, gm, input, fuel, s, okAll, index, rpath, prefix, dot, i, k, kind, alts, after, rs, ts, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(rs, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ts, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      keep_round(rpath, grammar, gm, input, fuel, s, okAll, index, prefix, dot, i, k, items, kind, alts, after, a, ch, rest, pEq, pos, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(ch, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => pe => po => rd => keep_walk(rest, ri, grammar, gm, input, fuel, s, okAll, ix, rx, px, dx, cx, kx, its, kd, ax, af, pe, po, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Leaf{k0} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Node{q, ch} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Skip{} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(KeepDone(True{}, grammar, gm, input, fuel, s, Spec.Loop{rs} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

# ======== THE LAW ========

# A parse tree that uses only kept steps is admissible.
law admissible_of_kept:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for allT: {Spec.allIn(Spec.steps(tree, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}
  Spec.Admissible(grammar, gm, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])

def admissible_of_kept(grammar, gm, start, input, fuel, s, tree, fitting, spelled, allT):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd(Spec.Admissible(grammar, gm, [Spec.Leaf{k}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []), Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      +both = fitting
      +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, both)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +all = {allT : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}}
      +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
      (owner_holds(OProd{}, fuel, grammar, gm, input, q, [], {==}, {==}, s, ch, 0n, [], pos, fitCh, all),
        (adm_walk(ch, False{}, grammar, gm, input, fuel, s, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], [], {==}, pos, ({==}, (fitCh, all))), Unit{}))
    case Spec.Pick{a, ch}:
      Empty.absurd(Spec.Admissible(grammar, gm, [Spec.Pick{a, ch}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []), Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd(Spec.Admissible(grammar, gm, [Spec.Skip{}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []), Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd(Spec.Admissible(grammar, gm, [Spec.Loop{rs}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []), Lemma.false_is_not_true(fitting))

# An admissible parse tree uses only kept steps.
law kept_of_admissible:
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okAll: {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}
  for +eqE: {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}
  for tree: Spec.Tree
  for +fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for adm: Spec.Admissible(grammar, gm, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])
  {Spec.allIn(Spec.steps(tree, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}

def kept_of_admissible(grammar, gm, start, input, fuel, s, okAll, eqE, tree, fitting, spelled, adm):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Leaf{k}, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      match adm:
        case (hN, (admCh, unit)):
          +both = fitting
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, both)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
          +allS = {Sub.exact_steps_in(fuel, grammar, start, input, s, eqE)(Spec.Node{q, ch}, fitting, spelled) : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), s) == True{} : Bool}}
          +ownCh = owner_kept(OProd{}, fuel, grammar, gm, input, q, [], {==}, {==}, s, okAll, ch, 0n, [], pos, fitCh, allS, hN)
          keep_walk(ch, False{}, grammar, gm, input, fuel, s, okAll, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], [], {==}, pos, ({==}, (fitCh, (allS, (ownCh, admCh)))))
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Pick{a, ch}, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Skip{}, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Loop{rs}, 0n), Guard.guardKept(s, fuel, grammar, gm, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))

law embeds_admissible:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +gm: +List<Spec.GuardMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for facts: GuardFacts(fuel, grammar, gm, start, input, set)
  Spec.EmbedsAdmissible(grammar, gm, start, input, set)

def embeds_admissible(fuel, grammar, gm, start, input, set, facts):
  match facts:
    case (s0, (eqE0, (okAll0, keptEq0))):
      +s = {s0 : +List<Spec.Bsr>}
      +eqE = {eqE0 : {Exact.exactSteps(fuel, grammar, start, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}}
      +okAll = {okAll0 : {Guard.allKnown(s, fuel, grammar, gm, input) == True{} : Bool}}
      +keptEq = {keptEq0 : {Guard.guardKept(s, fuel, grammar, gm, input) == set : +List<Spec.Bsr>}}
      %keptEq : Spec.EmbedsAdmissible(grammar, gm, start, input, _)
      +tree => +fitting => +spelled =>
        (allK => admissible_of_kept(grammar, gm, start, input, fuel, s, tree, fitting, spelled, allK),
          adm => kept_of_admissible(grammar, gm, start, input, fuel, s, okAll, eqE, tree, fitting, spelled, adm))

# The law guards_exact.
def Laws.guards_exact(fuel, grammar, guards, start, input, set, got):
  +f = fuel
  embeds_admissible(f, grammar, guards, start, input, set, guard_found(Exact.exactSteps(f, grammar, start, input), f, grammar, guards, start, input, set, {==}, got))
