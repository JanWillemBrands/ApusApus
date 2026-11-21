import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P

# THE EXACT PARSER IS EXACT. Nothing is missing: its set is the pruned set, and pruning
# keeps every step of every parse tree (PROOF_PRUNE.bend). No dead wood: every step is a
# step of a witness tree, and the check has made sure each witness is a parse tree.

# ---- A covered step has a witness ----

def covered_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ws: +List<Core.Tree>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  +here: {Witness.coveredBy(y, ws) == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {Witness.coveredBy(x, ws) == True{} : Bool})
  -> {Witness.coveredBy(x, ws) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {Witness.coveredBy(_, ws) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law covered_of:
  for ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +x: Core.Bsr
  for +all: {Exact.allCovered(ps, ws) == True{} : Bool}
  for +m: {Core.member(x, ps) == True{} : Bool}
  {Witness.coveredBy(x, ws) == True{} : Bool}

def covered_of(ps, ws, x, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Witness.coveredBy(x, ws) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      covered_pick(x, y, rest, ws, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        Lemma.and_true_left(Witness.coveredBy(y, ws), Exact.allCovered(rest, ws), all),
        later => covered_of(rest, ws, x, Lemma.and_true_right_side(Witness.coveredBy(y, ws), Exact.allCovered(rest, ws), all), later))

def Witnessed(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr) -> Type:
  &tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) & {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}

def found_pick(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +t: Core.Tree, +rest: +List<Core.Tree>,
  +ok: {Exact.treeOk(grammar, start, input, t) == True{} : Bool},
  cases: Either<{Core.member(x, Core.steps([t], 0n)) == True{} : Bool}, {Witness.coveredBy(x, rest) == True{} : Bool}>,
  later: {Witness.coveredBy(x, rest) == True{} : Bool} -> Witnessed(grammar, start, input, x)) -> Witnessed(grammar, start, input, x):
  match cases:
    case Inl{+m}:
      +rr = Lemma.and_true_left(Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input)), ok)
      +rl = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input), Lemma.and_true_right_side(Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input)), ok))
      {(t, ((rr, rl), m)) : Witnessed(grammar, start, input, x)}
    case Inr{c}:
      later(c)

law found:
  for ws: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +c: {Witness.coveredBy(x, ws) == True{} : Bool}
  Witnessed(grammar, start, input, x)

def found(ws, grammar, start, input, x, okAll, c):
  match ws:
    case Nil{}:
      Empty.absurd(Witnessed(grammar, start, input, x), Lemma.false_is_not_true(c))
    case Con{+t, +rest}:
      found_pick(grammar, start, input, x, t, rest, Lemma.and_true_left(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), okAll),
        Lemma.or_true_cases(Core.member(x, Core.steps([t], 0n)), Witness.coveredBy(x, rest), c),
        later => found(rest, grammar, start, input, x, Lemma.and_true_right_side(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), okAll), later))

# ---- The theorem ----

law only_ps:
  for +ps: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +es: {ps == set : +List<Core.Bsr>}
  for +m: {Core.member(x, set) == True{} : Bool}
  {Core.member(x, ps) == True{} : Bool}

def only_ps(ps, set, x, es, m):
  %Equal.sym(+List<Core.Bsr>, ps, set, es) : {Core.member(x, _) == True{} : Bool}
  m

def only_one(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +set: +List<Core.Bsr>, +ws: +List<Core.Tree>,
  +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool},
  +cov: {Exact.allCovered(ps, ws) == True{} : Bool},
  +es: {ps == set : +List<Core.Bsr>},
  +x: Core.Bsr, +m: {Core.member(x, set) == True{} : Bool}) -> Witnessed(grammar, start, input, x):
  found(ws, grammar, start, input, x, okAll, covered_of(ps, ws, x, cov, only_ps(ps, set, x, es, m)))

def exact_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +ep: {Prune.prunedSteps(fuel, grammar, start, input) == Some{ps} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {b == Bool.and(Exact.allTreesOk(Witness.witnesses(fuel, grammar, start, input, ps), grammar, start, input), Exact.allCovered(ps, Witness.witnesses(fuel, grammar, start, input, ps))) : Bool},
  +e: {Exact.exactPick(b, ps) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.IsExact(grammar, start, input, set):
  match b:
    case True{}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      +both = Equal.sym(Bool, True{}, Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), eb)
      +okAll = Lemma.and_true_left(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), both)
      +cov = Lemma.and_true_right_side(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), both)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{ps}, Some{set}, e)
      +ep2 = Equal.trans(Maybe<&2, +List<Core.Bsr>>, Prune.prunedSteps(fuel, grammar, start, input), Some{ps}, Some{set}, ep, Equal.cong(+List<Core.Bsr>, Maybe<&2, +List<Core.Bsr>>, v => Some{v}, ps, set, es))
      (P.prune_every_parse_step(fuel, grammar, start, input, set, ep2),
       x => m => only_one(grammar, start, input, ps, set, ws, okAll, cov, es, x, m))
    case False{}:
      Empty.absurd(Core.IsExact(grammar, start, input, set), G.none_not_some(set, e))

def exact_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +em: {Prune.prunedSteps(fuel, grammar, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Exact.exactFrom(m, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.IsExact(grammar, start, input, set):
  match m:
    case Some{+ps}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      exact_pick(Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), fuel, grammar, start, input, ps, set, em, {==}, e)
    case None{}:
      Empty.absurd(Core.IsExact(grammar, start, input, set), G.none_not_some(set, e))

# THE EXACT PARSER IS EXACT: whenever `exactSteps` hands out a set, it holds exactly the steps
# of the parse trees of the input.
law gll_bsr_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.IsExact(grammar, start, input, set)

def gll_bsr_exact(fuel, grammar, start, input, set, got):
  +f = fuel
  exact_parts(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input, set, {==}, got)
