import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./EXACT.bend as Exact
import ./WITNESS.bend as Witness
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./EXTENT.bend as Extent
import ./PROOF_GLL.bend as G
import ./PROOF_EXACT.bend as X
import ./PROOF_ORACLE.bend as PO

# THE SELECTING ORACLE KEEPS EXACTLY THE SELECTED TREES. The chosen set is exact: it holds
# every step of every chosen tree (oracle_exact), and every one of its steps lies on a
# chosen tree (its checked witnesses). So the readings in the set are the readings, and
# `chains` finds all of them. A step is out exactly when two of them show it, which is what
# `beaten` looks for.

# ======== SMALL FACTS ========

law succ_not_zero:
  for +n: Nat
  for +e: {1n+n == 0n : Nat}
  Empty

def succ_not_zero(n, e):
  Lemma.false_is_not_true(Equal.cong(Nat, Bool, v => Nat.is_eq(v, 0n), 1n+n, 0n, e))

law succ_inj:
  for +a: Nat
  for +b: Nat
  for +e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, v => Lemma.predOf(v), 1n+a, 1n+b, e)

law eq_is_eq:
  for +a: Nat
  for +b: Nat
  for +e: {a == b : Nat}
  {Nat.is_eq(a, b) == True{} : Bool}

def eq_is_eq(a, b, e):
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

law rev_rev:
  for xs: +List<Nat>
  for +acc: +List<Nat>
  {Extent.revOnto(Extent.revOnto(xs, acc), []) == Extent.revOnto(acc, xs) : +List<Nat>}

def rev_rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      rev_rev(rest, x <> acc)

# ======== THE CHOSEN SET IS EXACT ========

def Within(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr) -> Type:
  &tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) & {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} & {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}

def within_pick(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr, +t: Core.Tree, +rest: +List<Core.Tree>,
  +ok: {Extent.treeIn(grammar, start, input, set, t) == True{} : Bool},
  cases: Either<{Core.member(x, Core.steps([t], 0n)) == True{} : Bool}, {Witness.coveredBy(x, rest) == True{} : Bool}>,
  later: {Witness.coveredBy(x, rest) == True{} : Bool} -> Within(grammar, start, input, set, x)) -> Within(grammar, start, input, set, x):
  match cases:
    case Inl{+m}:
      +rd0 = {Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) : Bool}
      +le0 = {Nat.is_eq(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input)) : Bool}
      +tok = Lemma.and_true_left(Exact.treeOk(grammar, start, input, t), Core.allIn(Core.steps([t], 0n), set), ok)
      +inS = Lemma.and_true_right_side(Exact.treeOk(grammar, start, input, t), Core.allIn(Core.steps([t], 0n), set), ok)
      +rr = Lemma.and_true_left(rd0, le0, tok)
      +rl = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input), Lemma.and_true_right_side(rd0, le0, tok))
      {(t, ((rr, rl), (inS, m))) : Within(grammar, start, input, set, x)}
    case Inr{c}:
      later(c)

law within:
  for ws: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +okAll: {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool}
  for +c: {Witness.coveredBy(x, ws) == True{} : Bool}
  Within(grammar, start, input, set, x)

def within(ws, grammar, start, input, set, x, okAll, c):
  match ws:
    case Nil{}:
      Empty.absurd(Within(grammar, start, input, set, x), Lemma.false_is_not_true(c))
    case Con{+t, +rest}:
      +here = {Extent.treeIn(grammar, start, input, set, t) : Bool}
      +more = {Extent.allTreesIn(rest, grammar, start, input, set) : Bool}
      within_pick(grammar, start, input, set, x, t, rest, Lemma.and_true_left(here, more, okAll),
        Lemma.or_true_cases(Core.member(x, Core.steps([t], 0n)), Witness.coveredBy(x, rest), c),
        later => within(rest, grammar, start, input, set, x, Lemma.and_true_right_side(here, more, okAll), later))

# The parts of an answer of chosenSteps: the oracle's own set, and the witness checks.
def Parts(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Type:
  {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>} &
  {Extent.allTreesIn(Witness.witnesses(fuel, grammar, start, input, set), grammar, start, input, set) == True{} : Bool} &
  {Exact.allCovered(set, Witness.witnesses(fuel, grammar, start, input, set)) == True{} : Bool}

def parts_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +s0: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +em: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{s0} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {Bool.and(Extent.allTreesIn(Witness.witnesses(fuel, grammar, start, input, s0), grammar, start, input, s0), Exact.allCovered(s0, Witness.witnesses(fuel, grammar, start, input, s0))) == b : Bool},
  +e: {Exact.exactPick(b, s0) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Parts(fuel, grammar, gmarks, rmarks, start, input, set):
  match b:
    case True{}:
      +es = PO.exact_eq(True{}, s0, set, e)
      +ws = Witness.witnesses(fuel, grammar, start, input, s0)
      +ok = Lemma.and_true_left(Extent.allTreesIn(ws, grammar, start, input, s0), Exact.allCovered(s0, ws), eb)
      +cov = Lemma.and_true_right_side(Extent.allTreesIn(ws, grammar, start, input, s0), Exact.allCovered(s0, ws), eb)
      %es : Parts(fuel, grammar, gmarks, rmarks, start, input, _)
      {(em, (ok, cov)) : Parts(fuel, grammar, gmarks, rmarks, start, input, s0)}
    case False{}:
      Empty.absurd(Parts(fuel, grammar, gmarks, rmarks, start, input, set), G.none_not_some(set, e))

def parts_from(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +em: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Extent.coverFrom(m, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Parts(fuel, grammar, gmarks, rmarks, start, input, set):
  match m:
    case Some{+s0}:
      +ws = Witness.witnesses(fuel, grammar, start, input, s0)
      parts_pick(Bool.and(Extent.allTreesIn(ws, grammar, start, input, s0), Exact.allCovered(s0, ws)), fuel, grammar, gmarks, rmarks, start, input, s0, set, em, {==}, e)
    case None{}:
      Empty.absurd(Parts(fuel, grammar, gmarks, rmarks, start, input, set), G.none_not_some(set, e))

law parts:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Parts(fuel, grammar, gmarks, rmarks, start, input, set)

def parts(fuel, grammar, gmarks, rmarks, start, input, set, got):
  +f = fuel
  parts_from(Oracle.oracleSteps(f, grammar, gmarks, rmarks, start, input), f, grammar, gmarks, rmarks, start, input, set, {==}, got)

def embeds_of(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  p: Parts(fuel, grammar, gmarks, rmarks, start, input, set)) -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set):
  match p:
    case (em, rest):
      PO.oracle_exact(fuel, grammar, gmarks, rmarks, start, input, set, em)

def back_of(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +tree: Core.Tree,
  both: ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}),
  ch: Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}:
  match both:
    case (f, b):
      b(ch)

def fwd_of(+grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +tree: Core.Tree,
  both: ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}),
  +h: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}) -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree):
  match both:
    case (f, b):
      f(h)

# A chosen tree's steps are in the chosen set, and a tree with all its steps there is chosen.
law chosen_in:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +tree: Core.Tree
  for pt: Core.ParseTree(grammar, start, input, tree)
  for ch: Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)
  {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}

def chosen_in(fuel, grammar, gmarks, rmarks, start, input, set, got, tree, pt, ch):
  back_of(grammar, gmarks, rmarks, start, input, set, tree, embeds_of(fuel, grammar, gmarks, rmarks, start, input, set, parts(fuel, grammar, gmarks, rmarks, start, input, set, got))(tree, pt), ch)

law in_chosen:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +tree: Core.Tree
  for pt: Core.ParseTree(grammar, start, input, tree)
  for +h: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)

def in_chosen(fuel, grammar, gmarks, rmarks, start, input, set, got, tree, pt, h):
  fwd_of(grammar, gmarks, rmarks, start, input, set, tree, embeds_of(fuel, grammar, gmarks, rmarks, start, input, set, parts(fuel, grammar, gmarks, rmarks, start, input, set, got))(tree, pt), h)

def within_pt(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +t: Core.Tree, +inS: {Core.allIn(Core.steps([t], 0n), set) == True{} : Bool}, +m: {Core.member(x, Core.steps([t], 0n)) == True{} : Bool},
  pt: Core.ParseTree(grammar, start, input, t)) -> Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x):
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = rl0
      ch = in_chosen(fuel, grammar, gmarks, rmarks, start, input, set, got, t, {(rr, rl) : Core.ParseTree(grammar, start, input, t)}, inS)
      {(t, ((rr, rl), (ch, m))) : Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x)}

def step_within(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  w: Within(grammar, start, input, set, x)) -> Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x):
  match w:
    case (t0, (pt, (inS0, m0))):
      within_pt(fuel, grammar, gmarks, rmarks, start, input, set, x, got, t0, inS0, m0, pt)

def step_parts(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +m: {Core.member(x, set) == True{} : Bool},
  p: Parts(fuel, grammar, gmarks, rmarks, start, input, set)) -> Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x):
  match p:
    case (em, (ok0, cov0)):
      +ws = Witness.witnesses(fuel, grammar, start, input, set)
      +ok = {ok0 : {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool}}
      +cov = {cov0 : {Exact.allCovered(set, ws) == True{} : Bool}}
      step_within(fuel, grammar, gmarks, rmarks, start, input, set, x, got, within(ws, grammar, start, input, set, x, ok, X.covered_of(set, ws, x, cov, m)))

# Every step of the chosen set lies on a chosen tree.
law chosen_step:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +x: Core.Bsr
  for +m: {Core.member(x, set) == True{} : Bool}
  Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x)

def chosen_step(fuel, grammar, gmarks, rmarks, start, input, set, got, x, m):
  step_parts(fuel, grammar, gmarks, rmarks, start, input, set, x, got, m, parts(fuel, grammar, gmarks, rmarks, start, input, set, got))

# A step of a chosen tree is in the chosen set.
def chosen_member(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  cs: Extent.ChosenStep(grammar, gmarks, rmarks, start, input, x)) -> {Core.member(x, set) == True{} : Bool}:
  match cs:
    case (t0, (pt, (ch, m0))):
      +t = t0
      +m = {m0 : {Core.member(x, Core.steps([t], 0n)) == True{} : Bool}}
      G.all_in_member(Core.steps([t], 0n), set, x, chosen_in(fuel, grammar, gmarks, rmarks, start, input, set, got, t, pt, ch), m)

# ======== READINGS AND THE SET ========

def all_chosen_pair(+x: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  ac: Extent.AllChosen(grammar, gmarks, rmarks, start, input, x <> rest),
  later: Extent.AllChosen(grammar, gmarks, rmarks, start, input, rest) -> {Core.allIn(rest, set) == True{} : Bool}) -> {Core.allIn(x <> rest, set) == True{} : Bool}:
  match ac:
    case (cs, more):
      Lemma.and_true_intro(Core.member(x, set), Core.allIn(rest, set), chosen_member(fuel, grammar, gmarks, rmarks, start, input, set, x, got, cs), later(more))

law all_chosen_in:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for ac: Extent.AllChosen(grammar, gmarks, rmarks, start, input, xs)
  {Core.allIn(xs, set) == True{} : Bool}

def all_chosen_in(xs, fuel, grammar, gmarks, rmarks, start, input, set, got, ac):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      all_chosen_pair(x, rest, fuel, grammar, gmarks, rmarks, start, input, set, got, ac, r => all_chosen_in(rest, fuel, grammar, gmarks, rmarks, start, input, set, got, r))

law in_all_chosen:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +h: {Core.allIn(xs, set) == True{} : Bool}
  Extent.AllChosen(grammar, gmarks, rmarks, start, input, xs)

def in_all_chosen(xs, fuel, grammar, gmarks, rmarks, start, input, set, got, h):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      (chosen_step(fuel, grammar, gmarks, rmarks, start, input, set, got, x, Lemma.and_true_left(Core.member(x, set), Core.allIn(rest, set), h)),
       in_all_chosen(rest, fuel, grammar, gmarks, rmarks, start, input, set, got, Lemma.and_true_right_side(Core.member(x, set), Core.allIn(rest, set), h)))

def reading_in(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +ks: +List<Nat>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  r: Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, ks)) -> {Extent.readingIn(grammar, set, q, i, ks) == True{} : Bool}:
  match r:
    case (len0, ac):
      +len = len0
      Lemma.and_true_intro(Nat.is_eq(List.length(&2, Nat, ks), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))), Core.allIn(Extent.stepsOf(q, i, ks), set),
        eq_is_eq(List.length(&2, Nat, ks), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), len),
        all_chosen_in(Extent.stepsOf(q, i, ks), fuel, grammar, gmarks, rmarks, start, input, set, got, ac))

def in_reading(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +ks: +List<Nat>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +h: {Extent.readingIn(grammar, set, q, i, ks) == True{} : Bool}) -> Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, ks):
  +le = {Nat.is_eq(List.length(&2, Nat, ks), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +al = {Core.allIn(Extent.stepsOf(q, i, ks), set) : Bool}
  ({Lemma.nat_eq_sound(List.length(&2, Nat, ks), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Lemma.and_true_left(le, al, h)) : {List.length(&2, Nat, ks) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}},
   in_all_chosen(Extent.stepsOf(q, i, ks), fuel, grammar, gmarks, rmarks, start, input, set, got, Lemma.and_true_right_side(le, al, h)))

# ======== chains FINDS EVERY READING IN THE SET ========

def PathIn(+path: +List<Nat>, paths: +List<+List<Nat>>) -> Type:
  match paths:
    case Nil{}:
      Empty
    case Con{+r, rest}:
      Either<{path == r : +List<Nat>}, PathIn(path, rest)>

law join_left:
  for a: +List<+List<Nat>>
  for +b: +List<+List<Nat>>
  for +path: +List<Nat>
  for h: PathIn(path, a)
  PathIn(path, Extent.joinPaths(a, b))

def join_left(a, b, path, h):
  match a:
    case Nil{}:
      Empty.absurd(PathIn(path, Extent.joinPaths([], b)), h)
    case Con{+x, +rest}:
      match h:
        case Inl{e}:
          Inl{e}
        case Inr{m}:
          Inr{join_left(rest, b, path, m)}

law join_right:
  for a: +List<+List<Nat>>
  for +b: +List<+List<Nat>>
  for +path: +List<Nat>
  for h: PathIn(path, b)
  PathIn(path, Extent.joinPaths(a, b))

def join_right(a, b, path, h):
  match a:
    case Nil{}:
      h
    case Con{+x, +rest}:
      Inr{join_right(rest, b, path, h)}

def add_here(b: Bool, +path: +List<Nat>, +rest: +List<+List<Nat>>, +hb: {b == True{} : Bool}) -> PathIn(path, Extent.addPath(b, path, rest)):
  match b:
    case True{}:
      Inl{{==}}
    case False{}:
      Empty.absurd(PathIn(path, rest), Lemma.false_is_not_true(hb))

def add_later(b: Bool, +path: +List<Nat>, +other: +List<Nat>, +rest: +List<+List<Nat>>, h: PathIn(path, rest)) -> PathIn(path, Extent.addPath(b, other, rest)):
  match b:
    case True{}:
      Inr{h}
    case False{}:
      h

def grow_cases(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +q: Nat, +p: Nat, +i: Nat, +rev: +List<Nat>,
  +f: {Extent.fitsStep(q, p, i, Extent.prevOf(i, rev), x) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> PathIn(Extent.stepEnd(x) <> rev, Extent.growOne(rest, q, p, i, rev)))
  -> PathIn(Extent.stepEnd(x) <> rev, Extent.growOne(y <> rest, q, p, i, rev)):
  match cases:
    case Inl{e}:
      +same = G.bsr_eq_sound(x, y, e)
      +prev = Extent.prevOf(i, rev)
      +fy = Equal.trans(Bool, Extent.fitsStep(q, p, i, prev, y), Extent.fitsStep(q, p, i, prev, x), True{}, Equal.sym(Bool, Extent.fitsStep(q, p, i, prev, x), Extent.fitsStep(q, p, i, prev, y), Equal.cong(Core.Bsr, Bool, v => Extent.fitsStep(q, p, i, prev, v), x, y, same)), f)
      %Equal.sym(Core.Bsr, x, y, same) : PathIn(Extent.stepEnd(_) <> rev, Extent.addPath(Extent.fitsStep(q, p, i, prev, y), Extent.stepEnd(y) <> rev, Extent.growOne(rest, q, p, i, rev)))
      add_here(Extent.fitsStep(q, p, i, prev, y), Extent.stepEnd(y) <> rev, Extent.growOne(rest, q, p, i, rev), fy)
    case Inr{m}:
      add_later(Extent.fitsStep(q, p, i, Extent.prevOf(i, rev), y), Extent.stepEnd(x) <> rev, Extent.stepEnd(y) <> rev, Extent.growOne(rest, q, p, i, rev), later(m))

law grow_has:
  for xs: +List<Core.Bsr>
  for +q: Nat
  for +p: Nat
  for +i: Nat
  for +rev: +List<Nat>
  for +x: Core.Bsr
  for +m: {Core.member(x, xs) == True{} : Bool}
  for +f: {Extent.fitsStep(q, p, i, Extent.prevOf(i, rev), x) == True{} : Bool}
  PathIn(Extent.stepEnd(x) <> rev, Extent.growOne(xs, q, p, i, rev))

def grow_has(xs, q, p, i, rev, x, m, f):
  match xs:
    case Nil{}:
      Empty.absurd(PathIn(Extent.stepEnd(x) <> rev, []), Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      grow_cases(x, y, rest, q, p, i, rev, f, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m), m2 => grow_has(rest, q, p, i, rev, x, m2, f))

law expand_has:
  for states: +List<+List<Nat>>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +p: Nat
  for +i: Nat
  for +rev: +List<Nat>
  for +new: +List<Nat>
  for inS: PathIn(rev, states)
  for h: PathIn(new, Extent.growOne(set, q, p, i, rev))
  PathIn(new, Extent.expand(states, set, q, p, i))

def expand_has(states, set, q, p, i, rev, new, inS, h):
  match states:
    case Nil{}:
      Empty.absurd(PathIn(new, []), inS)
    case Con{+r, +rest}:
      match inS:
        case Inl{e}:
          %e : PathIn(new, Extent.joinPaths(Extent.growOne(set, q, p, i, _), Extent.expand(rest, set, q, p, i)))
          join_left(Extent.growOne(set, q, p, i, rev), Extent.expand(rest, set, q, p, i), new, h)
        case Inr{m}:
          join_right(Extent.growOne(set, q, p, i, r), Extent.expand(rest, set, q, p, i), new, expand_has(rest, set, q, p, i, rev, new, m, h))

law fits_own:
  for +q: Nat
  for +p: Nat
  for +i: Nat
  for +prev: Nat
  for +k: Nat
  {Extent.fitsStep(q, p, i, prev, Core.Bsr{q, 1n+p, i, prev, k}) == True{} : Bool}

def fits_own(q, p, i, prev, k):
  Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(1n+p, 1n+p), Bool.and(Nat.is_eq(i, i), Nat.is_eq(prev, prev))), Lemma.nat_eq_refl(q),
    Lemma.and_true_intro(Nat.is_eq(1n+p, 1n+p), Bool.and(Nat.is_eq(i, i), Nat.is_eq(prev, prev)), Lemma.nat_eq_refl(1n+p),
      Lemma.and_true_intro(Nat.is_eq(i, i), Nat.is_eq(prev, prev), Lemma.nat_eq_refl(i), Lemma.nat_eq_refl(prev))))

law run_has:
  for items: +List<Core.Sym>
  for ks: +List<Nat>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +p: Nat
  for +i: Nat
  for +states: +List<+List<Nat>>
  for +rev: +List<Nat>
  for +len: {List.length(&2, Nat, ks) == List.length(&2, Core.Sym, items) : Nat}
  for inS: PathIn(rev, states)
  for +inSet: {Core.allIn(Extent.ownOf(ks, q, i, p, Extent.prevOf(i, rev)), set) == True{} : Bool}
  PathIn(Extent.revOnto(ks, rev), Extent.run(items, set, q, p, i, states))

def run_has(items, ks, set, q, p, i, states, rev, len, inS, inSet):
  match items ks:
    case Nil{} Nil{}:
      inS
    case Nil{} Con{+k, +rest}:
      Empty.absurd(PathIn(Extent.revOnto(k <> rest, rev), states), succ_not_zero(List.length(&2, Nat, rest), len))
    case Con{+it, +more} Nil{}:
      Empty.absurd(PathIn(rev, Extent.run(it <> more, set, q, p, i, states)), succ_not_zero(List.length(&2, Core.Sym, more), Equal.sym(Nat, 0n, 1n+List.length(&2, Core.Sym, more), len)))
    case Con{+it, +more} Con{+k, +rest}:
      +prev = Extent.prevOf(i, rev)
      +x = {Core.Bsr{q, 1n+p, i, prev, k} : Core.Bsr}
      +tail = {Core.allIn(Extent.ownOf(rest, q, i, 1n+p, k), set) : Bool}
      +mx = Lemma.and_true_left(Core.member(x, set), tail, inSet)
      next = expand_has(states, set, q, p, i, rev, k <> rev, inS, grow_has(set, q, p, i, rev, x, mx, fits_own(q, p, i, prev, k)))
      run_has(more, rest, set, q, 1n+p, i, Extent.expand(states, set, q, p, i), k <> rev,
        succ_inj(List.length(&2, Nat, rest), List.length(&2, Core.Sym, more), len), next, Lemma.and_true_right_side(Core.member(x, set), tail, inSet))

# ======== THE PAIR SEARCH ========

def with_cases(+r: +List<Nat>, +rest: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>, +r2: +List<Nat>,
  inC: Either<{r2 == r : +List<Nat>}, PathIn(r2, rest)>,
  +ok: {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r2, [])) == True{} : Bool},
  later: PathIn(r2, rest) -> {Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool})
  -> {Extent.anyWith(r <> rest, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool}:
  match inC:
    case Inl{e}:
      %e : {Bool.or(Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(_, [])), Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1)) == True{} : Bool}
      Lemma.or_true_left_intro(Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r2, [])), Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1), ok)
    case Inr{m}:
      Lemma.or_true_right_intro(Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r, [])), Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1), later(m))

law with_has:
  for cs: +List<+List<Nat>>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +ks1: +List<Nat>
  for +r2: +List<Nat>
  for inC: PathIn(r2, cs)
  for +ok: {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r2, [])) == True{} : Bool}
  {Extent.anyWith(cs, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool}

def with_has(cs, grammar, emarks, set, q, d, i, k, j, ks1, r2, inC, ok):
  match cs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, inC)
    case Con{+r, +rest}:
      with_cases(r, rest, grammar, emarks, set, q, d, i, k, j, ks1, r2, inC, ok, m => with_has(rest, grammar, emarks, set, q, d, i, k, j, ks1, r2, m, ok))

def pair_cases(+r: +List<Nat>, +rest: +List<+List<Nat>>, +all: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +r1: +List<Nat>,
  inC: Either<{r1 == r : +List<Nat>}, PathIn(r1, rest)>,
  +ok: {Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, [])) == True{} : Bool},
  later: PathIn(r1, rest) -> {Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool})
  -> {Extent.anyPair(r <> rest, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool}:
  match inC:
    case Inl{e}:
      %e : {Bool.or(Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(_, [])), Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j)) == True{} : Bool}
      Lemma.or_true_left_intro(Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, [])), Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j), ok)
    case Inr{m}:
      Lemma.or_true_right_intro(Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r, [])), Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j), later(m))

law pair_has:
  for cs: +List<+List<Nat>>
  for +all: +List<+List<Nat>>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +r1: +List<Nat>
  for inC: PathIn(r1, cs)
  for +ok: {Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, [])) == True{} : Bool}
  {Extent.anyPair(cs, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool}

def pair_has(cs, all, grammar, emarks, set, q, d, i, k, j, r1, inC, ok):
  match cs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, inC)
    case Con{+r, +rest}:
      pair_cases(r, rest, all, grammar, emarks, set, q, d, i, k, j, r1, inC, ok, m => pair_has(rest, all, grammar, emarks, set, q, d, i, k, j, r1, m, ok))

def Found(+grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>) -> Type:
  &ks2: +List<Nat> -> {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, ks2) == True{} : Bool}

def with_pick(+r2: +List<Nat>, +rest: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>,
  cases: Either<{Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r2, [])) == True{} : Bool}, {Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool}>,
  later: {Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool} -> Found(grammar, emarks, set, q, d, i, k, j, ks1)) -> Found(grammar, emarks, set, q, d, i, k, j, ks1):
  match cases:
    case Inl{e}:
      {(Extent.revOnto(r2, []), e) : Found(grammar, emarks, set, q, d, i, k, j, ks1)}
    case Inr{m}:
      later(m)

law with_found:
  for cs: +List<+List<Nat>>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +ks1: +List<Nat>
  for +h: {Extent.anyWith(cs, grammar, emarks, set, q, d, i, k, j, ks1) == True{} : Bool}
  Found(grammar, emarks, set, q, d, i, k, j, ks1)

def with_found(cs, grammar, emarks, set, q, d, i, k, j, ks1, h):
  match cs:
    case Nil{}:
      Empty.absurd(Found(grammar, emarks, set, q, d, i, k, j, ks1), Lemma.false_is_not_true(h))
    case Con{+r2, +rest}:
      with_pick(r2, rest, grammar, emarks, set, q, d, i, k, j, ks1,
        Lemma.or_true_cases(Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(r2, [])), Extent.anyWith(rest, grammar, emarks, set, q, d, i, k, j, ks1), h),
        m => with_found(rest, grammar, emarks, set, q, d, i, k, j, ks1, m))

def TwoReadings(+grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Type:
  &ks1: +List<Nat> -> Found(grammar, emarks, set, q, d, i, k, j, ks1)

def pair_pick(+r1: +List<Nat>, +rest: +List<+List<Nat>>, +all: +List<+List<Nat>>, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  cases: Either<{Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, [])) == True{} : Bool}, {Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool}>,
  later: {Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool} -> TwoReadings(grammar, emarks, set, q, d, i, k, j)) -> TwoReadings(grammar, emarks, set, q, d, i, k, j):
  match cases:
    case Inl{e}:
      {(Extent.revOnto(r1, []), with_found(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, []), e)) : TwoReadings(grammar, emarks, set, q, d, i, k, j)}
    case Inr{m}:
      later(m)

law pair_found:
  for cs: +List<+List<Nat>>
  for +all: +List<+List<Nat>>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +h: {Extent.anyPair(cs, all, grammar, emarks, set, q, d, i, k, j) == True{} : Bool}
  TwoReadings(grammar, emarks, set, q, d, i, k, j)

def pair_found(cs, all, grammar, emarks, set, q, d, i, k, j, h):
  match cs:
    case Nil{}:
      Empty.absurd(TwoReadings(grammar, emarks, set, q, d, i, k, j), Lemma.false_is_not_true(h))
    case Con{+r1, +rest}:
      pair_pick(r1, rest, all, grammar, emarks, set, q, d, i, k, j,
        Lemma.or_true_cases(Extent.anyWith(all, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(r1, [])), Extent.anyPair(rest, all, grammar, emarks, set, q, d, i, k, j), h),
        m => pair_found(rest, all, grammar, emarks, set, q, d, i, k, j, m))

# ======== beaten IS RIGHT ========

def out_of(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +ks1: +List<Nat>, +ks2: +List<Nat>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +ok: {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, ks2) == True{} : Bool}) -> Extent.Out(grammar, gmarks, rmarks, emarks, start, input, Core.Bsr{q, d, i, k, j}):
  +r1 = {Extent.readingIn(grammar, set, q, i, ks1) : Bool}
  +r2 = {Extent.readingIn(grammar, set, q, i, ks2) : Bool}
  +en = {Nat.is_eq(Extent.endOf(ks1, i), Extent.endOf(ks2, i)) : Bool}
  +mm = {Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)) : Bool}
  +bt = {Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i) : Bool}
  +h1 = Lemma.and_true_right_side(r1, Bool.and(r2, Bool.and(en, Bool.and(mm, bt))), ok)
  +h2 = Lemma.and_true_right_side(r2, Bool.and(en, Bool.and(mm, bt)), h1)
  +h3 = Lemma.and_true_right_side(en, Bool.and(mm, bt), h2)
  read1 = in_reading(fuel, grammar, gmarks, rmarks, start, input, set, q, i, ks1, got, Lemma.and_true_left(r1, Bool.and(r2, Bool.and(en, Bool.and(mm, bt))), ok))
  read2 = in_reading(fuel, grammar, gmarks, rmarks, start, input, set, q, i, ks2, got, Lemma.and_true_left(r2, Bool.and(en, Bool.and(mm, bt)), h1))
  +ends = Lemma.nat_eq_sound(Extent.endOf(ks1, i), Extent.endOf(ks2, i), Lemma.and_true_left(en, Bool.and(mm, bt), h2))
  {(ks1, (ks2, (read1, (read2, (ends, (Lemma.and_true_left(mm, bt, h3), Lemma.and_true_right_side(mm, bt, h3))))))) : Extent.Out(grammar, gmarks, rmarks, emarks, start, input, Core.Bsr{q, d, i, k, j})}

def out_found(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  pr: TwoReadings(grammar, emarks, set, q, d, i, k, j)) -> Extent.Out(grammar, gmarks, rmarks, emarks, start, input, Core.Bsr{q, d, i, k, j}):
  match pr:
    case (ks10, (ks20, ok0)):
      +ks1 = ks10
      +ks2 = ks20
      +ok = {ok0 : {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, ks2) == True{} : Bool}}
      out_of(fuel, grammar, gmarks, rmarks, emarks, start, input, set, q, d, i, k, j, ks1, ks2, got, ok)

# A step `beaten` finds is out.
law best_no:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +h: {Extent.beaten(grammar, emarks, set, x) == True{} : Bool}
  Extent.Out(grammar, gmarks, rmarks, emarks, start, input, x)

def best_no(x, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, h):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      +cs = Extent.chains(set, grammar, q, i)
      out_found(fuel, grammar, gmarks, rmarks, emarks, start, input, set, q, d, i, k, j, got, pair_found(cs, cs, grammar, emarks, set, q, d, i, k, j, h))

def found_both(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +a: Nat, +r1: +List<Nat>, +b: Nat, +r2: +List<Nat>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  read1: Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, a <> r1),
  read2: Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, b <> r2),
  +ends: {Extent.endOf(a <> r1, i) == Extent.endOf(b <> r2, i) : Nat},
  +mm: {Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, a <> r1)) == True{} : Bool},
  +bt: {Extent.beatsAt(a <> r1, b <> r2, emarks, grammar, q, d, 0n, i, i) == True{} : Bool})
  -> {Extent.beaten(grammar, emarks, set, Core.Bsr{q, d, i, k, j}) == True{} : Bool}:
  +ks1 = {a <> r1 : +List<Nat>}
  +ks2 = {b <> r2 : +List<Nat>}
  +in1 = reading_in(fuel, grammar, gmarks, rmarks, start, input, set, q, i, ks1, got, read1)
  +in2 = reading_in(fuel, grammar, gmarks, rmarks, start, input, set, q, i, ks2, got, read2)
  +le1 = {Nat.is_eq(List.length(&2, Nat, ks1), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +le2 = {Nat.is_eq(List.length(&2, Nat, ks2), List.length(&2, Core.Sym, Core.rhsOf(grammar, q))) : Bool}
  +al1 = {Core.allIn(Extent.stepsOf(q, i, ks1), set) : Bool}
  +al2 = {Core.allIn(Extent.stepsOf(q, i, ks2), set) : Bool}
  +cs = Extent.chains(set, grammar, q, i)
  p1 = run_has(Core.rhsOf(grammar, q), ks1, set, q, 0n, i, [[]], [], Lemma.nat_eq_sound(List.length(&2, Nat, ks1), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Lemma.and_true_left(le1, al1, in1)), Inl{{==}}, Lemma.and_true_right_side(le1, al1, in1))
  p2 = run_has(Core.rhsOf(grammar, q), ks2, set, q, 0n, i, [[]], [], Lemma.nat_eq_sound(List.length(&2, Nat, ks2), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Lemma.and_true_left(le2, al2, in2)), Inl{{==}}, Lemma.and_true_right_side(le2, al2, in2))
  +en = eq_is_eq(Extent.endOf(ks1, i), Extent.endOf(ks2, i), ends)
  +ok = {Lemma.and_true_intro(Extent.readingIn(grammar, set, q, i, ks1), Bool.and(Extent.readingIn(grammar, set, q, i, ks2), Bool.and(Nat.is_eq(Extent.endOf(ks1, i), Extent.endOf(ks2, i)), Bool.and(Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)), Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i)))), in1,
    Lemma.and_true_intro(Extent.readingIn(grammar, set, q, i, ks2), Bool.and(Nat.is_eq(Extent.endOf(ks1, i), Extent.endOf(ks2, i)), Bool.and(Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)), Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i))), in2,
      Lemma.and_true_intro(Nat.is_eq(Extent.endOf(ks1, i), Extent.endOf(ks2, i)), Bool.and(Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)), Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i)), en,
        Lemma.and_true_intro(Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)), Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i), mm, bt)))) : {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, ks2) == True{} : Bool}}
  +rr2 = rev_rev(ks2, [])
  +rr1 = rev_rev(ks1, [])
  +ok2 = {(%Equal.sym(+List<Nat>, Extent.revOnto(Extent.revOnto(ks2, []), []), ks2, rr2) : {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, _) == True{} : Bool}
    ok) : {Extent.pairOk(grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(Extent.revOnto(ks2, []), [])) == True{} : Bool}}
  +w = with_has(cs, grammar, emarks, set, q, d, i, k, j, ks1, Extent.revOnto(ks2, []), p2, ok2)
  +w2 = {(%Equal.sym(+List<Nat>, Extent.revOnto(Extent.revOnto(ks1, []), []), ks1, rr1) : {Extent.anyWith(cs, grammar, emarks, set, q, d, i, k, j, _) == True{} : Bool}
    w) : {Extent.anyWith(cs, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(Extent.revOnto(ks1, []), [])) == True{} : Bool}}
  pair_has(cs, cs, grammar, emarks, set, q, d, i, k, j, Extent.revOnto(ks1, []), p1, w2)

def lists_cases(ks1: +List<Nat>, ks2: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +h: {Extent.beaten(grammar, emarks, set, Core.Bsr{q, d, i, k, j}) == False{} : Bool},
  read1: Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, ks1),
  read2: Extent.Reading(grammar, gmarks, rmarks, start, input, q, i, ks2),
  +ends: {Extent.endOf(ks1, i) == Extent.endOf(ks2, i) : Nat},
  +mm: {Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)) == True{} : Bool},
  +bt: {Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i) == True{} : Bool}) -> Empty:
  match ks1:
    case Nil{}:
      Lemma.false_is_not_true(bt)
    case Con{+a, +r1}:
      match ks2:
        case Nil{}:
          Lemma.false_is_not_true(bt)
        case Con{+b, +r2}:
          +yes = found_both(fuel, grammar, gmarks, rmarks, emarks, start, input, set, q, d, i, k, j, a, r1, b, r2, got, read1, read2, ends, mm, bt)
          Lemma.true_is_not_false(Equal.trans(Bool, True{}, Extent.beaten(grammar, emarks, set, Core.Bsr{q, d, i, k, j}), False{}, Equal.sym(Bool, Extent.beaten(grammar, emarks, set, Core.Bsr{q, d, i, k, j}), True{}, yes), h))

def out_cases(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +h: {Extent.beaten(grammar, emarks, set, Core.Bsr{q, d, i, k, j}) == False{} : Bool},
  o: Extent.Out(grammar, gmarks, rmarks, emarks, start, input, Core.Bsr{q, d, i, k, j})) -> Empty:
  match o:
    case (ks10, (ks20, (read1, (read2, (ends0, (mm0, bt0)))))):
      +ks1 = ks10
      +ks2 = ks20
      +ends = {ends0 : {Extent.endOf(ks1, i) == Extent.endOf(ks2, i) : Nat}}
      +mm = {mm0 : {Core.member(Core.Bsr{q, d, i, k, j}, Extent.stepsOf(q, i, ks1)) == True{} : Bool}}
      +bt = {bt0 : {Extent.beatsAt(ks1, ks2, emarks, grammar, q, d, 0n, i, i) == True{} : Bool}}
      lists_cases(ks1, ks2, fuel, grammar, gmarks, rmarks, emarks, start, input, set, q, d, i, k, j, got, h, read1, read2, ends, mm, bt)

# A step `beaten` does not find is not out.
law best_yes:
  for x: Core.Bsr
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +h: {Extent.beaten(grammar, emarks, set, x) == False{} : Bool}
  for o: Extent.Out(grammar, gmarks, rmarks, emarks, start, input, x)
  Empty

def best_yes(x, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, h, o):
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      out_cases(fuel, grammar, gmarks, rmarks, emarks, start, input, set, q, d, i, k, j, got, h, o)

# ======== THE FILTER ========

def KeptFacts(+grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +x: Core.Bsr, +xs: +List<Core.Bsr>) -> Type:
  {Core.member(x, xs) == True{} : Bool} & {Extent.beaten(grammar, emarks, set, x) == False{} : Bool}

law not_true_false:
  for b: Bool
  for +e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_true_false(b, e):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(e))
    case False{}:
      {==}

def lift_facts(+grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  f: KeptFacts(grammar, emarks, set, x, rest)) -> KeptFacts(grammar, emarks, set, x, y <> rest):
  match f:
    case (mr, nb):
      (Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, rest), mr), nb)

def head_facts(+grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +ny: {Extent.beaten(grammar, emarks, set, y) == False{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, Extent.keepBest(rest, grammar, emarks, set)) == True{} : Bool}>,
  later: {Core.member(x, Extent.keepBest(rest, grammar, emarks, set)) == True{} : Bool} -> KeptFacts(grammar, emarks, set, x, rest)) -> KeptFacts(grammar, emarks, set, x, y <> rest):
  match cases:
    case Inl{+e}:
      +same = G.bsr_eq_sound(x, y, e)
      +nx = {(%Equal.sym(Core.Bsr, x, y, same) : {Extent.beaten(grammar, emarks, set, _) == False{} : Bool}
        ny) : {Extent.beaten(grammar, emarks, set, x) == False{} : Bool}}
      (Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, rest), e), nx)
    case Inr{m}:
      lift_facts(grammar, emarks, set, x, y, rest, later(m))

def kept_cases(b: Bool, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +eb: {b == Bool.not(Extent.beaten(grammar, emarks, set, y)) : Bool},
  +m: {Core.member(x, Oracle.keepIf(b, y, Extent.keepBest(rest, grammar, emarks, set))) == True{} : Bool},
  later: {Core.member(x, Extent.keepBest(rest, grammar, emarks, set)) == True{} : Bool} -> KeptFacts(grammar, emarks, set, x, rest)) -> KeptFacts(grammar, emarks, set, x, y <> rest):
  match b:
    case True{}:
      +ny = not_true_false(Extent.beaten(grammar, emarks, set, y), Equal.sym(Bool, True{}, Bool.not(Extent.beaten(grammar, emarks, set, y)), eb))
      head_facts(grammar, emarks, set, x, y, rest, ny, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, Extent.keepBest(rest, grammar, emarks, set)), m), later)
    case False{}:
      lift_facts(grammar, emarks, set, x, y, rest, later(m))

law kept_facts:
  for xs: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +m: {Core.member(x, Extent.keepBest(xs, grammar, emarks, set)) == True{} : Bool}
  KeptFacts(grammar, emarks, set, x, xs)

def kept_facts(xs, grammar, emarks, set, x, m):
  match xs:
    case Nil{}:
      Empty.absurd(KeptFacts(grammar, emarks, set, x, []), Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      kept_cases(Bool.not(Extent.beaten(grammar, emarks, set, y)), grammar, emarks, set, x, y, rest, {==}, m, m2 => kept_facts(rest, grammar, emarks, set, x, m2))

def keep_cases(b: Bool, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +set: +List<Core.Bsr>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  +eb: {b == Bool.not(Extent.beaten(grammar, emarks, set, y)) : Bool},
  +nb: {Extent.beaten(grammar, emarks, set, x) == False{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, Extent.keepBest(rest, grammar, emarks, set)) == True{} : Bool})
  -> {Core.member(x, Oracle.keepIf(b, y, Extent.keepBest(rest, grammar, emarks, set))) == True{} : Bool}:
  match b cases:
    case True{} Inl{e}:
      Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, Extent.keepBest(rest, grammar, emarks, set)), e)
    case True{} Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, Extent.keepBest(rest, grammar, emarks, set)), later(m))
    case False{} Inl{e}:
      +same = G.bsr_eq_sound(x, y, e)
      +ny = {(%same : {Extent.beaten(grammar, emarks, set, _) == False{} : Bool}
        nb) : {Extent.beaten(grammar, emarks, set, y) == False{} : Bool}}
      +nt = Equal.cong(Bool, Bool, v => Bool.not(v), Extent.beaten(grammar, emarks, set, y), False{}, ny)
      Empty.absurd({Core.member(x, Extent.keepBest(rest, grammar, emarks, set)) == True{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Bool.not(Extent.beaten(grammar, emarks, set, y)), True{}, eb, nt)))
    case False{} Inr{m}:
      later(m)

law best_kept:
  for xs: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +emarks: +List<Extent.ExtentMark>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +m: {Core.member(x, xs) == True{} : Bool}
  for +nb: {Extent.beaten(grammar, emarks, set, x) == False{} : Bool}
  {Core.member(x, Extent.keepBest(xs, grammar, emarks, set)) == True{} : Bool}

def best_kept(xs, grammar, emarks, set, x, m, nb):
  match xs:
    case Nil{}:
      Empty.absurd({Core.member(x, []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      keep_cases(Bool.not(Extent.beaten(grammar, emarks, set, y)), grammar, emarks, set, x, y, rest, {==}, nb,
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m), m2 => best_kept(rest, grammar, emarks, set, x, m2, nb))

def decide(b: Bool, +x: Core.Bsr, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +eb: {Extent.beaten(grammar, emarks, set, x) == b : Bool},
  nx: Extent.Out(grammar, gmarks, rmarks, emarks, start, input, x) -> Empty) -> {Extent.beaten(grammar, emarks, set, x) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Extent.beaten(grammar, emarks, set, x) == False{} : Bool}, nx(best_no(x, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, eb)))
    case False{}:
      eb

# ======== THE WALKS OVER A TREE'S STEPS ========

def fwd_more(+x: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +ms: {Core.member(x, set) == True{} : Bool}, +nb: {Extent.beaten(grammar, emarks, set, x) == False{} : Bool},
  more: {Core.allIn(rest, set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, rest))
  -> {Core.allIn(x <> rest, set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, x <> rest):
  match more:
    case (ar0, br):
      +ar = {ar0 : {Core.allIn(rest, set) == True{} : Bool}}
      (Lemma.and_true_intro(Core.member(x, set), Core.allIn(rest, set), ms, ar), (o => best_yes(x, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, nb, o), br))

def fwd_pair(+x: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  kf: KeptFacts(grammar, emarks, set, x, set),
  more: {Core.allIn(rest, set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, rest))
  -> {Core.allIn(x <> rest, set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, x <> rest):
  match kf:
    case (ms0, nb0):
      fwd_more(x, rest, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, ms0, nb0, more)

law fwd:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +h: {Core.allIn(xs, Extent.keepBest(set, grammar, emarks, set)) == True{} : Bool}
  {Core.allIn(xs, set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, xs)

def fwd(xs, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, h):
  match xs:
    case Nil{}:
      ({==}, Unit{})
    case Con{+x, +rest}:
      +kept = Extent.keepBest(set, grammar, emarks, set)
      fwd_pair(x, rest, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got,
        kept_facts(set, grammar, emarks, set, x, Lemma.and_true_left(Core.member(x, kept), Core.allIn(rest, kept), h)),
        fwd(rest, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, Lemma.and_true_right_side(Core.member(x, kept), Core.allIn(rest, kept), h)))

def back_pair(+x: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +inS: {Core.allIn(x <> rest, set) == True{} : Bool},
  ab: Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, x <> rest),
  later: {Core.allIn(rest, set) == True{} : Bool} -> Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, rest) -> {Core.allIn(rest, Extent.keepBest(set, grammar, emarks, set)) == True{} : Bool})
  -> {Core.allIn(x <> rest, Extent.keepBest(set, grammar, emarks, set)) == True{} : Bool}:
  match ab:
    case (nx, abr):
      +kept = Extent.keepBest(set, grammar, emarks, set)
      +m = Lemma.and_true_left(Core.member(x, set), Core.allIn(rest, set), inS)
      +nb = decide(Extent.beaten(grammar, emarks, set, x), x, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, {==}, nx)
      Lemma.and_true_intro(Core.member(x, kept), Core.allIn(rest, kept), best_kept(set, grammar, emarks, set, x, m, nb),
        later(Lemma.and_true_right_side(Core.member(x, set), Core.allIn(rest, set), inS), abr))

law back:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +inS: {Core.allIn(xs, set) == True{} : Bool}
  for ab: Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, xs)
  {Core.allIn(xs, Extent.keepBest(set, grammar, emarks, set)) == True{} : Bool}

def back(xs, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, inS, ab):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      back_pair(x, rest, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, inS, ab, i2 => a2 => back(rest, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, i2, a2))

# ======== THE THEOREM ========

def sel_fwd(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree, pt: Core.ParseTree(grammar, start, input, tree),
  f: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} & Extent.AllBest(grammar, gmarks, rmarks, emarks, start, input, Core.steps([tree], 0n)))
  -> Extent.Selected(grammar, gmarks, rmarks, emarks, start, input, tree):
  match f:
    case (inS0, best):
      +inS = {inS0 : {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}}
      (in_chosen(fuel, grammar, gmarks, rmarks, start, input, set, got, tree, pt, inS), best)

def sel_back(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree, pt: Core.ParseTree(grammar, start, input, tree),
  s: Extent.Selected(grammar, gmarks, rmarks, emarks, start, input, tree)) -> {Core.allIn(Core.steps([tree], 0n), Extent.keepBest(set, grammar, emarks, set)) == True{} : Bool}:
  match s:
    case (ch, ab):
      +inS = chosen_in(fuel, grammar, gmarks, rmarks, start, input, set, got, tree, pt, ch)
      back(Core.steps([tree], 0n), fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, inS, ab)

def select_tree(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +set3: +List<Core.Bsr>,
  +got: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +es: {Extent.keepBest(set, grammar, emarks, set) == set3 : +List<Core.Bsr>},
  +tree: Core.Tree, pt: Core.ParseTree(grammar, start, input, tree))
  -> ({Core.allIn(Core.steps([tree], 0n), set3) == True{} : Bool} -> Extent.Selected(grammar, gmarks, rmarks, emarks, start, input, tree)) &
     (Extent.Selected(grammar, gmarks, rmarks, emarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set3) == True{} : Bool}):
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = rl0
      +xs = Core.steps([tree], 0n)
      +kept = Extent.keepBest(set, grammar, emarks, set)
      (h => sel_fwd(fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, tree, {(rr, rl) : Core.ParseTree(grammar, start, input, tree)},
          fwd(xs, fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, PO.to_kept(xs, kept, set3, es, h))),
       s => PO.to_set(xs, kept, set3, es, sel_back(fuel, grammar, gmarks, rmarks, emarks, start, input, set, got, tree, {(rr, rl) : Core.ParseTree(grammar, start, input, tree)}, s)))

def select_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +emarks: +List<Extent.ExtentMark>, +start: Nat, +input: +List<Nat>, +set3: +List<Core.Bsr>,
  +em: {Extent.chosenSteps(fuel, grammar, gmarks, rmarks, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +e: {Extent.selectFrom(m, grammar, emarks) == Some{set3} : Maybe<&2, +List<Core.Bsr>>}) -> Extent.EmbedsSelected(grammar, gmarks, rmarks, emarks, start, input, set3):
  match m:
    case Some{+set}:
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Extent.keepBest(set, grammar, emarks, set)}, Some{set3}, e)
      tree => pt => select_tree(fuel, grammar, gmarks, rmarks, emarks, start, input, set, set3, em, es, tree, pt)
    case None{}:
      Empty.absurd(Extent.EmbedsSelected(grammar, gmarks, rmarks, emarks, start, input, set3), G.none_not_some(set3, e))

# THE MARKS SELECT EXACTLY THE SELECTED TREES: whenever the selecting oracle hands out a set,
# a parse tree of the input uses only steps of that set exactly when phases 1 and 2 keep it
# and none of its steps is out.
law extent_exact:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set3: +List<Core.Bsr>
  for +got: {Extent.selectedSteps(fuel, grammar, gmarks, rmarks, emarks, start, input) == Some{set3} : Maybe<&2, +List<Core.Bsr>>}
  Extent.EmbedsSelected(grammar, gmarks, rmarks, emarks, start, input, set3)

def extent_exact(fuel, grammar, gmarks, rmarks, emarks, start, input, set3, got):
  +f = fuel
  select_parts(Extent.chosenSteps(f, grammar, gmarks, rmarks, start, input), f, grammar, gmarks, rmarks, emarks, start, input, set3, {==}, got)
