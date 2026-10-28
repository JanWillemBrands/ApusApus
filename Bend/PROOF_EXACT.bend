import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./LEMMAS.bend as Lemma

# THE EXACT PARSER'S SET IS EXACT.
#
# Nothing missing comes from PROOF_PRUNE.bend. No dead wood comes from the witness
# check: every kept step is a step of a witness tree, and every witness tree passed
# SPEC.bend's own `fits` and `leaves`.

def ParseTreeWith(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +element: Spec.Bsr) -> Type:
  &tree: Spec.Tree -> {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool} & {Spec.leaves([tree]) == input : +List<Nat>} & {Spec.bsrMember(element, Spec.steps(tree, 0n)) == True{} : Bool}

# ---- A covered step has a witness ----

law found_here:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +t: Spec.Tree
  for ok: {Exact.treeOk(grammar, start, input, t) == True{} : Bool}
  for m: {Spec.bsrMember(e, Spec.steps(t, 0n)) == True{} : Bool}
  ParseTreeWith(grammar, start, input, e)

def found_here(grammar, start, input, e, t, ok, m):
  +both = ok
  +fitsT = Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}])
  +spelled = Gll.natsEq(Spec.leaves([t]), input)
  (t, (Lemma.and_true_left(fitsT, spelled, both), (G.nats_eq_sound(Spec.leaves([t]), input, Lemma.and_true_right_side(fitsT, spelled, both)), m)))

law find_pick:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +t: Spec.Tree
  for -rest: +List<Spec.Tree>
  for cases: Either<{Spec.bsrMember(e, Spec.steps(t, 0n)) == True{} : Bool}, {Exact.coveredBy(e, rest) == True{} : Bool}>
  for ok: {Exact.treeOk(grammar, start, input, t) == True{} : Bool}
  for searchRest: {Exact.coveredBy(e, rest) == True{} : Bool} -> ParseTreeWith(grammar, start, input, e)
  ParseTreeWith(grammar, start, input, e)

def find_pick(grammar, start, input, e, t, rest, cases, ok, searchRest):
  match cases:
    case Inl{here}:
      found_here(grammar, start, input, e, t, ok, here)
    case Inr{later}:
      searchRest(later)

law find_tree:
  for ws: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for treesOk: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for cov: {Exact.coveredBy(e, ws) == True{} : Bool}
  ParseTreeWith(grammar, start, input, e)

def find_tree(ws, grammar, start, input, e, treesOk, cov):
  match ws:
    case Nil{}:
      Empty.absurd(ParseTreeWith(grammar, start, input, e), Lemma.false_is_not_true(cov))
    case Con{+t, +rest}:
      +both = treesOk
      find_pick(grammar, start, input, e, t, rest, Lemma.or_true_cases(Spec.bsrMember(e, Spec.steps(t, 0n)), Exact.coveredBy(e, rest), cov),
        Lemma.and_true_left(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), both),
        later => find_tree(rest, grammar, start, input, e, Lemma.and_true_right_side(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), both), later))

law cover_pick:
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for +ws: +List<Spec.Tree>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +xCov: {Exact.coveredBy(x, ws) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Exact.coveredBy(e, ws) == True{} : Bool}
  {Exact.coveredBy(e, ws) == True{} : Bool}

def cover_pick(e, x, rest, ws, cases, xCov, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Exact.coveredBy(e, ws), Exact.coveredBy(x, ws), True{}, Equal.cong(Spec.Bsr, Bool, v => Exact.coveredBy(v, ws), e, x, same), xCov)
    case Inr{later}:
      searchRest(later)

law covered_of:
  for ps: +List<Spec.Bsr>
  for +ws: +List<Spec.Tree>
  for +e: Spec.Bsr
  for all: {Exact.allCovered(ps, ws) == True{} : Bool}
  for m: {Spec.bsrMember(e, ps) == True{} : Bool}
  {Exact.coveredBy(e, ws) == True{} : Bool}

def covered_of(ps, ws, e, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Exact.coveredBy(e, ws) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      +both = all
      cover_pick(e, x, rest, ws, G.ebnf_member_cases(e, x, rest, m),
        Lemma.and_true_left(Exact.coveredBy(x, ws), Exact.allCovered(rest, ws), both),
        later => covered_of(rest, ws, e, Lemma.and_true_right_side(Exact.coveredBy(x, ws), Exact.allCovered(rest, ws), both), later))

# ---- No dead wood ----

law exact_only:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Spec.Bsr>
  for +ws: +List<Spec.Tree>
  for +set: +List<Spec.Bsr>
  for +same: {ps == set : +List<Spec.Bsr>}
  for +treesOk: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +allCov: {Exact.allCovered(ps, ws) == True{} : Bool}
  Spec.OnlyParseSteps(grammar, start, input, set)

def exact_only(grammar, start, input, ps, ws, set, same, treesOk, allCov):
  +element => inSet =>
    inPs = Equal.trans(Bool, Spec.bsrMember(element, ps), Spec.bsrMember(element, set), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.bsrMember(element, v), ps, set, same), inSet)
    find_tree(ws, grammar, start, input, element, treesOk, covered_of(ps, ws, element, allCov, inPs))

# ---- From the exact parser's answer ----

law exact_pick_facts:
  for ok: Bool
  for +ps: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for got: {Exact.exactPick(ok, ps) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {ok == True{} : Bool} & {ps == set : +List<Spec.Bsr>}

def exact_pick_facts(ok, ps, set, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{ps}, Some{set}, got))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {ps == set : +List<Spec.Bsr>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law exact_facts:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Spec.Bsr>
  for +eqF: {Prune.prunedSteps(fuel, grammar, start, input) == Some{ps} : Maybe<&2, +List<Spec.Bsr>>}
  for +set: +List<Spec.Bsr>
  for facts: {Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)) == True{} : Bool} & {ps == set : +List<Spec.Bsr>}
  Spec.IsExactBsr(grammar, start, input, set)

def exact_facts(fuel, grammar, start, input, ps, eqF, set, facts):
  match facts:
    case (ok0, same0):
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      +ok = {ok0 : {Exact.witnessed(grammar, start, input, ps, ws) == True{} : Bool}}
      +same = {same0 : {ps == set : +List<Spec.Bsr>}}
      +treesOk = Lemma.and_true_left(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), ok)
      +allCov = Lemma.and_true_right_side(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), ok)
      +eqSet = Equal.trans(Maybe<&2, +List<Spec.Bsr>>, Prune.prunedSteps(fuel, grammar, start, input), Some{ps}, Some{set}, eqF, Equal.cong(+List<Spec.Bsr>, Maybe<&2, +List<Spec.Bsr>>, v => Some{v}, ps, set, same))
      (exact_only(grammar, start, input, ps, ws, set, same, treesOk, allCov), P.pruned_every(fuel, grammar, start, input, set, eqSet))

law exact_both:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Spec.Bsr>
  for +eqF: {Prune.prunedSteps(fuel, grammar, start, input) == Some{ps} : Maybe<&2, +List<Spec.Bsr>>}
  for +set: +List<Spec.Bsr>
  for facts: {Bool.and(Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)), Exact.allTokensOk(ps, grammar, input)) == True{} : Bool} & {ps == set : +List<Spec.Bsr>}
  Spec.IsExactBsr(grammar, start, input, set)

def exact_both(fuel, grammar, start, input, ps, eqF, set, facts):
  match facts:
    case (ok, same):
      +w = Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps))
      exact_facts(fuel, grammar, start, input, ps, eqF, set, (Lemma.and_true_left(w, Exact.allTokensOk(ps, grammar, input), ok), same))

law exact_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +eqF: {Prune.prunedSteps(fuel, grammar, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Exact.exactFrom(found, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def exact_found(found, fuel, grammar, start, input, set, eqF, got):
  match found:
    case Some{+ps}:
      exact_both(fuel, grammar, start, input, ps, eqF, set, exact_pick_facts(Bool.and(Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)), Exact.allTokensOk(ps, grammar, input)), ps, set, got))
    case None{}:
      Empty.absurd(Spec.IsExactBsr(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# The law gll_bsr_exact.
def Laws.gll_bsr_exact(fuel, grammar, start, input, set, got):
  +f = fuel
  exact_found(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input, set, {==}, got)
