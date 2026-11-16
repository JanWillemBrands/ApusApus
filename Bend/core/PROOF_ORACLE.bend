import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./WITNESS.bend as Witness
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_DECIDE.bend as D
import ./PROOF_GUARD.bend as PG
import ./PROOF_PREFER.bend as PP

# THE ORACLE KEEPS EXACTLY THE CHOSEN TREES. The oracle keeps a step of the exact set when
# phase 1 and phase 2 both answer Yes, and answers nothing when some verdict is Unknown. A
# Yes is right and a No is right (PROOF_GUARD.bend, PROOF_PREFER.bend), so a kept step is
# chosen, and a chosen step is kept. A parse tree's steps are all in the exact set; so its
# steps are all kept exactly when each of them keeps its rules and completes no beaten node.

# ======== ONE STEP ========

def yes_pair(+x: Core.Bsr, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>,
  both: {Guard.stepTri(fuel, grammar, gmarks, input, x) == Guard.Yes{} : Guard.Tri} & {Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x) == Guard.Yes{} : Guard.Tri})
  -> Oracle.StepOk(grammar, gmarks, rmarks, start, input, x):
  match both:
    case (g, r):
      (PG.step_yes(x, fuel, grammar, gmarks, input, g), PP.free_yes(x, fuel, grammar, gmarks, rmarks, input, r))

law step_yes:
  for +x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +e: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}
  Oracle.StepOk(grammar, gmarks, rmarks, start, input, x)

def step_yes(x, fuel, grammar, gmarks, rmarks, start, input, e):
  yes_pair(x, fuel, grammar, gmarks, rmarks, start, input, D.and_yes(Guard.stepTri(fuel, grammar, gmarks, input, x), Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x), e))

def no_side(+x: Core.Bsr, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>,
  cases: Either<{Guard.stepTri(fuel, grammar, gmarks, input, x) == Guard.No{} : Guard.Tri}, {Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x) == Guard.No{} : Guard.Tri}>,
  g: Guard.StepOk(grammar, gmarks, input, x), f: Prefer.Free(grammar, gmarks, rmarks, input, x)) -> Empty:
  match cases:
    case Inl{e1}:
      PG.step_no(x, fuel, grammar, gmarks, input, e1, g)
    case Inr{e2}:
      PP.free_no(x, fuel, grammar, gmarks, rmarks, input, e2, f)

law step_no:
  for +x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +e: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.No{} : Guard.Tri}
  for h: Oracle.StepOk(grammar, gmarks, rmarks, start, input, x)
  Empty

def step_no(x, fuel, grammar, gmarks, rmarks, start, input, e, h):
  match h:
    case (g, f):
      no_side(x, fuel, grammar, gmarks, rmarks, start, input, D.and_no_cases(Guard.stepTri(fuel, grammar, gmarks, input, x), Prefer.rankTri(fuel, grammar, gmarks, rmarks, input, x), e), g, f)

# ======== THE FILTER ========

law tri_cast:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +y: Core.Bsr
  for +t: Guard.Tri
  for +same: {x == y : Core.Bsr}
  for +h: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y) == t : Guard.Tri}
  {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == t : Guard.Tri}

def tri_cast(fuel, grammar, gmarks, rmarks, start, input, x, y, t, same, h):
  %Equal.sym(Core.Bsr, x, y, same) : {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, _) == t : Guard.Tri}
  h

def kept_head(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +eb: {True{} == Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)) : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}>,
  later: {Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool} -> {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri})
  -> {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}:
  match cases:
    case Inl{e}:
      tri_cast(fuel, grammar, gmarks, rmarks, start, input, x, y, Guard.Yes{}, G.bsr_eq_sound(x, y, e), PG.yes_of(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y), Equal.sym(Bool, True{}, Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), eb)))
    case Inr{m}:
      later(m)

def kept_cases(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +eb: {b == Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)) : Bool},
  +m: {Core.member(x, Oracle.keepIf(b, y, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input))) == True{} : Bool},
  later: {Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool} -> {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri})
  -> {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}:
  match b:
    case True{}:
      kept_head(fuel, grammar, gmarks, rmarks, start, input, x, y, rest, eb, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)), m), later)
    case False{}:
      later(m)

# A kept step was answered Yes.
law kept_yes:
  for ex: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}
  {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}

def kept_yes(ex, fuel, grammar, gmarks, rmarks, start, input, x, m):
  match ex:
    case Nil{}:
      Empty.absurd({Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      kept_cases(Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), fuel, grammar, gmarks, rmarks, start, input, x, y, rest, {==}, m, later => kept_yes(rest, fuel, grammar, gmarks, rmarks, start, input, x, later))

def keep_cases(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +eb: {b == Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)) : Bool},
  +yx: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool})
  -> {Core.member(x, Oracle.keepIf(b, y, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input))) == True{} : Bool}:
  match b cases:
    case True{} Inl{e}:
      Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)), e)
    case True{} Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)), later(m))
    case False{} Inl{e}:
      +yy = tri_cast(fuel, grammar, gmarks, rmarks, start, input, y, x, Guard.Yes{}, Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)), yx)
      +isy = Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y), Guard.Yes{}, yy)
      Empty.absurd({Core.member(x, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), True{}, eb, isy)))
    case False{} Inr{m}:
      later(m)

# A step of the exact set answered Yes is kept.
law yes_kept:
  for ex: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, ex) == True{} : Bool}
  for +yx: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == Guard.Yes{} : Guard.Tri}
  {Core.member(x, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}

def yes_kept(ex, fuel, grammar, gmarks, rmarks, start, input, x, m, yx):
  match ex:
    case Nil{}:
      Empty.absurd({Core.member(x, []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      keep_cases(Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), fuel, grammar, gmarks, rmarks, start, input, x, y, rest, {==}, yx,
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m), later => yes_kept(rest, fuel, grammar, gmarks, rmarks, start, input, x, later, yx))

law or_false_l:
  for x: Bool
  for +y: Bool
  for +e: {Bool.or(x, y) == False{} : Bool}
  {x == False{} : Bool}

def or_false_l(x, y, e):
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.true_is_not_false(e))
    case False{}:
      {==}

law or_false_r:
  for x: Bool
  for +y: Bool
  for +e: {Bool.or(x, y) == False{} : Bool}
  {y == False{} : Bool}

def or_false_r(x, y, e):
  match x:
    case True{}:
      Empty.absurd({y == False{} : Bool}, Lemma.true_is_not_false(e))
    case False{}:
      e

def unknown_cases(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +here: {Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)) == False{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)) == False{} : Bool})
  -> {Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)) == False{} : Bool}:
  match cases:
    case Inl{e}:
      +same = G.bsr_eq_sound(x, y, e)
      %Equal.sym(Core.Bsr, x, y, same) : {Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, _)) == False{} : Bool}
      here
    case Inr{m}:
      later(m)

# No step of the exact set was answered Unknown, when the oracle answered.
law not_unknown:
  for ex: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, ex) == True{} : Bool}
  for +nu: {Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool}
  {Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)) == False{} : Bool}

def not_unknown(ex, fuel, grammar, gmarks, rmarks, start, input, x, m, nu):
  match ex:
    case Nil{}:
      Empty.absurd({Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)) == False{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      unknown_cases(fuel, grammar, gmarks, rmarks, start, input, x, y, rest, or_false_l(Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), Oracle.anyUnknown(rest, fuel, grammar, gmarks, rmarks, start, input), nu),
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        later => not_unknown(rest, fuel, grammar, gmarks, rmarks, start, input, x, later, or_false_r(Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, y)), Oracle.anyUnknown(rest, fuel, grammar, gmarks, rmarks, start, input), nu)))

# ======== EVERY STEP OF A PARSE TREE IS IN THE EXACT SET ========

def keep_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ns: +List<Prune.Seg>, +ps: +List<Core.Bsr>,
  +ec: {Check.checkedSteps(fuel, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {b == Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns) : Bool},
  +e: {Prune.prunePick(b, ys, ns) == Some{ps} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}) -> {Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}:
  match b:
    case True{}:
      +n = List.length(&2, Nat, input)
      +hn = Equal.sym(Bool, True{}, Prune.needsClosed(grammar, start, n, ys, ns), eb)
      +roots = Lemma.and_true_left(Prune.allSegsIn(Prune.rootSegs(grammar, start, n), ns), Prune.allStepsOk(ys, grammar, ns), hn)
      +ok = Lemma.and_true_right_side(Prune.allSegsIn(Prune.rootSegs(grammar, start, n), ns), Prune.allStepsOk(ys, grammar, ns), hn)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Prune.keep(ys, ns)}, Some{ps}, e)
      +inYs = P.run_steps(Gll.parse(fuel, grammar, start, input), grammar, start, input, ys, ec, tree, rr)
      %es : {Core.allIn(Core.steps([tree], 0n), _) == True{} : Bool}
      P.tree_kept(tree, grammar, start, input, ys, ns, ok, roots, inYs, rr, rl)
    case False{}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}, G.none_not_some(ps, e))

def needs_pick(nm: Maybe<&2, +List<Prune.Seg>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Core.Bsr>, +ps: +List<Core.Bsr>,
  +ec: {Check.checkedSteps(fuel, grammar, start, input) == Some{ys} : Maybe<&2, +List<Core.Bsr>>},
  +e: {Prune.pruneChecked(nm, grammar, start, List.length(&2, Nat, input), ys) == Some{ps} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}) -> {Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}:
  match nm:
    case Some{+ns}:
      keep_pick(Prune.needsClosed(grammar, start, List.length(&2, Nat, input), ys, ns), fuel, grammar, start, input, ys, ns, ps, ec, {==}, e, tree, rr, rl)
    case None{}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}, G.none_not_some(ps, e))

def checked_pick(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>,
  +em: {Check.checkedSteps(fuel, grammar, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Prune.pruneSteps(m, fuel, grammar, start, input) == Some{ps} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}) -> {Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}:
  match m:
    case Some{+ys}:
      needs_pick(Prune.needsOf(fuel, grammar, start, List.length(&2, Nat, input), ys), fuel, grammar, start, input, ys, ps, em, e, tree, rr, rl)
    case None{}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}, G.none_not_some(ps, e))

law exact_eq:
  for b: Bool
  for +ps: +List<Core.Bsr>
  for +ex: +List<Core.Bsr>
  for +e: {Exact.exactPick(b, ps) == Some{ex} : Maybe<&2, +List<Core.Bsr>>}
  {ps == ex : +List<Core.Bsr>}

def exact_eq(b, ps, ex, e):
  match b:
    case True{}:
      Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{ps}, Some{ex}, e)
    case False{}:
      Empty.absurd({ps == ex : +List<Core.Bsr>}, G.none_not_some(ex, e))

def exact_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ex: +List<Core.Bsr>,
  +em: {Prune.prunedSteps(fuel, grammar, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Exact.exactFrom(m, fuel, grammar, start, input) == Some{ex} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}) -> {Core.allIn(Core.steps([tree], 0n), ex) == True{} : Bool}:
  match m:
    case Some{+ps}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      +es = exact_eq(Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), ps, ex, e)
      +inPs = checked_pick(Check.checkedSteps(fuel, grammar, start, input), fuel, grammar, start, input, ps, {==}, em, tree, rr, rl)
      %es : {Core.allIn(Core.steps([tree], 0n), _) == True{} : Bool}
      inPs
    case None{}:
      Empty.absurd({Core.allIn(Core.steps([tree], 0n), ex) == True{} : Bool}, G.none_not_some(ex, e))

# Every step of a parse tree of the input is in the exact parser's set.
law exact_all:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ex: +List<Core.Bsr>
  for +e: {Exact.exactSteps(fuel, grammar, start, input) == Some{ex} : Maybe<&2, +List<Core.Bsr>>}
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Core.allIn(Core.steps([tree], 0n), ex) == True{} : Bool}

def exact_all(fuel, grammar, start, input, ex, e, tree, rr, rl):
  exact_parts(Prune.prunedSteps(fuel, grammar, start, input), fuel, grammar, start, input, ex, {==}, e, tree, rr, rl)

# ======== THE WALKS OVER A TREE'S STEPS ========

law fwd:
  for xs: +List<Core.Bsr>
  for +ex: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +all: {Core.allIn(xs, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}
  Oracle.AllStepsOk(grammar, gmarks, rmarks, start, input, xs)

def fwd(xs, ex, fuel, grammar, gmarks, rmarks, start, input, all):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +kept = Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)
      +m = Lemma.and_true_left(Core.member(x, kept), Core.allIn(rest, kept), all)
      (step_yes(x, fuel, grammar, gmarks, rmarks, start, input, kept_yes(ex, fuel, grammar, gmarks, rmarks, start, input, x, m)),
       fwd(rest, ex, fuel, grammar, gmarks, rmarks, start, input, Lemma.and_true_right_side(Core.member(x, kept), Core.allIn(rest, kept), all)))

def verdict_kept(t: Guard.Tri, +ex: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr,
  +et: {Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x) == t : Guard.Tri},
  +m: {Core.member(x, ex) == True{} : Bool},
  +nu: {Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool},
  ok: Oracle.StepOk(grammar, gmarks, rmarks, start, input, x)) -> {Core.member(x, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}:
  match t:
    case Guard.Yes{}:
      yes_kept(ex, fuel, grammar, gmarks, rmarks, start, input, x, m, et)
    case Guard.No{}:
      Empty.absurd({Core.member(x, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}, step_no(x, fuel, grammar, gmarks, rmarks, start, input, et, ok))
    case Guard.Unknown{}:
      +isU = Equal.cong(Guard.Tri, Bool, v => Guard.isUnknown(v), Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x), Guard.Unknown{}, et)
      Empty.absurd({Core.member(x, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool},
        Lemma.true_is_not_false(Equal.trans(Bool, True{}, Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)), False{}, Equal.sym(Bool, Guard.isUnknown(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x)), True{}, isU), not_unknown(ex, fuel, grammar, gmarks, rmarks, start, input, x, m, nu))))

def back_pair(+x: Core.Bsr, +rest: +List<Core.Bsr>, +ex: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>,
  adm: Oracle.AllStepsOk(grammar, gmarks, rmarks, start, input, x <> rest),
  +inEx: {Core.allIn(x <> rest, ex) == True{} : Bool},
  +nu: {Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool},
  later: Oracle.AllStepsOk(grammar, gmarks, rmarks, start, input, rest) -> {Core.allIn(rest, ex) == True{} : Bool} -> {Core.allIn(rest, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool})
  -> {Core.allIn(x <> rest, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}:
  match adm:
    case (ok, okRest):
      +kept = Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)
      +m = Lemma.and_true_left(Core.member(x, ex), Core.allIn(rest, ex), inEx)
      +head = verdict_kept(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, x), ex, fuel, grammar, gmarks, rmarks, start, input, x, {==}, m, nu, ok)
      Lemma.and_true_intro(Core.member(x, kept), Core.allIn(rest, kept), head, later(okRest, Lemma.and_true_right_side(Core.member(x, ex), Core.allIn(rest, ex), inEx)))

law back:
  for xs: +List<Core.Bsr>
  for +ex: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for adm: Oracle.AllStepsOk(grammar, gmarks, rmarks, start, input, xs)
  for +inEx: {Core.allIn(xs, ex) == True{} : Bool}
  for +nu: {Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool}
  {Core.allIn(xs, Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)) == True{} : Bool}

def back(xs, ex, fuel, grammar, gmarks, rmarks, start, input, adm, inEx, nu):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      back_pair(x, rest, ex, fuel, grammar, gmarks, rmarks, start, input, adm, inEx, nu, a => i => back(rest, ex, fuel, grammar, gmarks, rmarks, start, input, a, i, nu))

# ======== THE THEOREM ========

law to_kept:
  for +xs: +List<Core.Bsr>
  for +kept: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +es: {kept == set : +List<Core.Bsr>}
  for +h: {Core.allIn(xs, set) == True{} : Bool}
  {Core.allIn(xs, kept) == True{} : Bool}

def to_kept(xs, kept, set, es, h):
  %Equal.sym(+List<Core.Bsr>, kept, set, es) : {Core.allIn(xs, _) == True{} : Bool}
  h

law to_set:
  for +xs: +List<Core.Bsr>
  for +kept: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +es: {kept == set : +List<Core.Bsr>}
  for +h: {Core.allIn(xs, kept) == True{} : Bool}
  {Core.allIn(xs, set) == True{} : Bool}

def to_set(xs, kept, set, es, h):
  %es : {Core.allIn(xs, _) == True{} : Bool}
  h

def embed_tree(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +ex: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +ee: {Exact.exactSteps(fuel, grammar, start, input) == Some{ex} : Maybe<&2, +List<Core.Bsr>>},
  +nu: {Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) == False{} : Bool},
  +es: {Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input) == set : +List<Core.Bsr>},
  +tree: Core.Tree, pt: Core.ParseTree(grammar, start, input, tree))
  -> ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
     (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}):
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = rl0
      +xs = Core.steps([tree], 0n)
      +kept = Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)
      (h => fwd(xs, ex, fuel, grammar, gmarks, rmarks, start, input, to_kept(xs, kept, set, es, h)),
       a => to_set(xs, kept, set, es, back(xs, ex, fuel, grammar, gmarks, rmarks, start, input, a, exact_all(fuel, grammar, start, input, ex, ee, tree, rr, rl), nu)))

def oracle_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +ex: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +ee: {Exact.exactSteps(fuel, grammar, start, input) == Some{ex} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {b == Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input) : Bool},
  +e: {Oracle.oraclePick(b, ex, fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set):
  match b:
    case False{}:
      +nu = Equal.sym(Bool, False{}, Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input), eb)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Oracle.keepYes(ex, fuel, grammar, gmarks, rmarks, start, input)}, Some{set}, e)
      tree => pt => embed_tree(fuel, grammar, gmarks, rmarks, start, input, ex, set, ee, nu, es, tree, pt)
    case True{}:
      Empty.absurd(Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set), G.none_not_some(set, e))

def oracle_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +em: {Exact.exactSteps(fuel, grammar, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Oracle.oracleFrom(m, fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set):
  match m:
    case Some{+ex}:
      oracle_pick(Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input), fuel, grammar, gmarks, rmarks, start, input, ex, set, em, {==}, e)
    case None{}:
      Empty.absurd(Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set), G.none_not_some(set, e))

# THE ORACLE KEEPS EXACTLY THE CHOSEN TREES: whenever it hands out a set, a parse tree of
# the input uses only steps of that set exactly when every one of its steps keeps the rules
# it decides and completes no beaten node.
law oracle_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set)

def oracle_exact(fuel, grammar, gmarks, rmarks, start, input, set, got):
  +f = fuel
  oracle_parts(Exact.exactSteps(f, grammar, start, input), f, grammar, gmarks, rmarks, start, input, set, {==}, got)
