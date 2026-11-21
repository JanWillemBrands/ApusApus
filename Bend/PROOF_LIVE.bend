import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./WITNESS.bend as Witness
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./EXTENT.bend as Extent
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C
import ./PROOF_WITNESS.bend as WC
import ./PROOF_ORACLE.bend as PO

# THE LIVE SET EMBEDS THE CHOSEN TREES (EXTENT.bend, `liveFrom`). A step of the oracle's set
# is dropped only when it lies on none of the trees found so far and the witness search
# inside the set has closed facts and no root forest; then no parse tree all of whose steps
# are in the set contains it (`root_found`). So every chosen tree keeps all its steps, and
# the live set embeds exactly the chosen trees.

def keptOf(out: Extent.Live) -> +List<Core.Bsr>:
  match out:
    case Extent.Live{ok, +kept, trees}:
      kept

def okOf(out: Extent.Live) -> Bool:
  match out:
    case Extent.Live{+ok, kept, trees}:
      ok

def treesOf(out: Extent.Live) -> +List<Core.Tree>:
  match out:
    case Extent.Live{ok, kept, +trees}:
      trees

# ======== ONE STEP OF THE PASS ========

def lc_true(+x: Core.Bsr, +y: Core.Bsr, +kept: +List<Core.Bsr>, cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, kept) == True{} : Bool}>)
  -> Either<({Core.bsrEq(x, y) == True{} : Bool} & {True{} == True{} : Bool}), {Core.member(x, kept) == True{} : Bool}>:
  match cases:
    case Inl{e}:
      Inl{(e, {==})}
    case Inr{m}:
      Inr{m}

# A kept step is the step added, which is kept, or one kept later.
law lc_cases:
  for k: Bool
  for c: Bool
  for +x: Core.Bsr
  for +y: Core.Bsr
  for +out: Extent.Live
  for +h: {Core.member(x, keptOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}
  Either<({Core.bsrEq(x, y) == True{} : Bool} & {k == True{} : Bool}), {Core.member(x, keptOf(out)) == True{} : Bool}>

def lc_cases(k, c, x, y, out, h):
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          lc_true(x, y, kept, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, kept), h))
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Inr{h}

law lc_keep:
  for k: Bool
  for c: Bool
  for +x: Core.Bsr
  for +y: Core.Bsr
  for +out: Extent.Live
  for +h: {Core.member(x, keptOf(out)) == True{} : Bool}
  {Core.member(x, keptOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}

def lc_keep(k, c, x, y, out, h):
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, kept), h)
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          h

# The step added is kept when the pass answers and closed facts mean it is kept.
law lc_head:
  for k: Bool
  for c: Bool
  for +y: Core.Bsr
  for +out: Extent.Live
  for +hok: {okOf(Extent.liveCons(k, c, y, out)) == True{} : Bool}
  for hk: {c == True{} : Bool} -> {k == True{} : Bool}
  {Core.member(y, keptOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}

def lc_head(k, c, y, out, hok, hk):
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Lemma.or_true_left_intro(Core.bsrEq(y, y), Core.member(y, kept), C.bsr_eq_refl(y))
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Empty.absurd({Core.member(y, kept) == True{} : Bool}, Lemma.false_is_not_true(hk(Lemma.and_true_left(c, ok, hok))))

law lc_ok_tail:
  for k: Bool
  for c: Bool
  for +y: Core.Bsr
  for +out: Extent.Live
  for +hok: {okOf(Extent.liveCons(k, c, y, out)) == True{} : Bool}
  {okOf(out) == True{} : Bool}

def lc_ok_tail(k, c, y, out, hok):
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          hok
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Lemma.and_true_right_side(c, ok, hok)

# ======== A STEP OF A TREE INSIDE THE SET IS KEPT OR HAS OPEN FACTS ========

def trees_root(m: Maybe<&2, +List<Core.Tree>>, +h: {WC.isTrees(m) == True{} : Bool}) -> {Extent.hasRoot(m) == True{} : Bool}:
  match m:
    case Some{+ts}:
      {==}
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

# Covered, or the search finds a root once its facts are closed.
law closed_root:
  for cov: Bool
  for tree: Core.Tree
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +y: Core.Bsr
  for +hin: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +my: {Core.member(y, Core.steps([tree], 0n)) == True{} : Bool}
  for +cl: {Witness.closedW(set, grammar, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)) == True{} : Bool}
  {Bool.or(cov, Extent.hasRoot(Extent.rootIf(cov, grammar, start, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)))) == True{} : Bool}

def closed_root(cov, tree, fuel, grammar, start, input, set, y, hin, rr, rl, my, cl):
  match cov:
    case True{}:
      {==}
    case False{}:
      +F = Witness.fixpoint(fuel, set, grammar, input, y, [])
      trees_root(Witness.rootFor(grammar, grammar, y, 0n, start, List.length(&2, Nat, input), F), WC.root_found(tree, grammar, start, input, set, y, F, cl, hin, rr, rl, my))

def mem_to(+x: Core.Bsr, +y: Core.Bsr, +ex: {x == y : Core.Bsr}, +s: +List<Core.Bsr>, +h: {Core.member(x, s) == True{} : Bool}) -> {Core.member(y, s) == True{} : Bool}:
  %ex : {Core.member(_, s) == True{} : Bool}
  h

def lm_pick(+k: Bool, +c: Bool, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +out: Extent.Live,
  +hok: {okOf(Extent.liveCons(k, c, y, out)) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  head: {x == y : Core.Bsr} -> {c == True{} : Bool} -> {k == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {okOf(out) == True{} : Bool} -> {Core.member(x, keptOf(out)) == True{} : Bool})
  -> {Core.member(x, keptOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      +ex = G.bsr_eq_sound(x, y, e)
      %Equal.sym(Core.Bsr, x, y, ex) : {Core.member(_, keptOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}
      lc_head(k, c, y, out, hok, head(ex))
    case Inr{m}:
      lc_keep(k, c, x, y, out, later(m, lc_ok_tail(k, c, y, out, hok)))

# A step of a parse tree inside the set is live when the pass answers.
law live_mem:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +tree: Core.Tree
  for +x: Core.Bsr
  for +m: {Core.member(x, xs) == True{} : Bool}
  for +hok: {okOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set)) == True{} : Bool}
  for +hin: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +mx: {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}
  {Core.member(x, keptOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set))) == True{} : Bool}

def live_mem(xs, ws, fuel, grammar, start, input, set, tree, x, m, hok, hin, rr, rl, mx):
  match xs:
    case Nil{}:
      Empty.absurd({Core.member(x, []) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +cov = {Witness.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      +out = Extent.liveRun(rest, Witness.addWitness(r, ws), fuel, grammar, start, input, set)
      lm_pick(Bool.or(cov, Extent.hasRoot(r)), Witness.closedW(set, grammar, input, y, F), x, y, rest, out, hok,
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        ex => cl => closed_root(cov, tree, fuel, grammar, start, input, set, y, hin, rr, rl, mem_to(x, y, ex, Core.steps([tree], 0n), mx), cl),
        mr => ho => live_mem(rest, Witness.addWitness(r, ws), fuel, grammar, start, input, set, tree, x, mr, ho, hin, rr, rl, mx))

# ======== A LIVE STEP IS A STEP OF THE SET ========

def ks_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +k: Bool, +out: Extent.Live,
  cases: Either<({Core.bsrEq(x, y) == True{} : Bool} & {k == True{} : Bool}), {Core.member(x, keptOf(out)) == True{} : Bool}>,
  later: {Core.member(x, keptOf(out)) == True{} : Bool} -> {Core.member(x, rest) == True{} : Bool})
  -> {Core.member(x, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{p}:
      match p:
        case (+e, hk):
          Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, rest), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, rest), later(m))

law kl_sub:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +h: {Core.member(x, keptOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set))) == True{} : Bool}
  {Core.member(x, xs) == True{} : Bool}

def kl_sub(xs, ws, fuel, grammar, start, input, set, x, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      +cov = {Witness.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      +K = {Bool.or(cov, Extent.hasRoot(r)) : Bool}
      +out = Extent.liveRun(rest, Witness.addWitness(r, ws), fuel, grammar, start, input, set)
      ks_pick(x, y, rest, K, out, lc_cases(K, Witness.closedW(set, grammar, input, y, F), x, y, out, h),
        m => kl_sub(rest, Witness.addWitness(r, ws), fuel, grammar, start, input, set, x, m))

# ======== THE LIVE SET ========

def liveOf(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Extent.Live:
  Extent.liveRun(set, [], fuel, grammar, start, input, set)

law all_kl_sub:
  for ys: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +h: {Core.allIn(ys, keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}
  {Core.allIn(ys, set) == True{} : Bool}

def all_kl_sub(ys, fuel, grammar, start, input, set, h):
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +KS = keptOf(liveOf(fuel, grammar, start, input, set))
      Lemma.and_true_intro(Core.member(y, set), Core.allIn(rest, set),
        kl_sub(set, [], fuel, grammar, start, input, set, y, Lemma.and_true_left(Core.member(y, KS), Core.allIn(rest, KS), h)),
        all_kl_sub(rest, fuel, grammar, start, input, set, Lemma.and_true_right_side(Core.member(y, KS), Core.allIn(rest, KS), h)))

law all_live:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +tree: Core.Tree
  for +hsub: {Core.allIn(xs, Core.steps([tree], 0n)) == True{} : Bool}
  for +hin: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +hok: {okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}
  {Core.allIn(xs, keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}

def all_live(xs, fuel, grammar, start, input, set, tree, hsub, hin, rr, rl, hok):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +mx = Lemma.and_true_left(Core.member(x, Core.steps([tree], 0n)), Core.allIn(rest, Core.steps([tree], 0n)), hsub)
      +ms = G.all_in_member(Core.steps([tree], 0n), set, x, hin, mx)
      +KS = keptOf(liveOf(fuel, grammar, start, input, set))
      Lemma.and_true_intro(Core.member(x, KS), Core.allIn(rest, KS), live_mem(set, [], fuel, grammar, start, input, set, tree, x, ms, hok, hin, rr, rl, mx),
        all_live(rest, fuel, grammar, start, input, set, tree, Lemma.and_true_right_side(Core.member(x, Core.steps([tree], 0n)), Core.allIn(rest, Core.steps([tree], 0n)), hsub), hin, rr, rl, hok))

# ======== THE LIVE SET EMBEDS THE CHOSEN TREES ========

def live_tree(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +hok: {okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool},
  both: ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}))
  -> ({Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}):
  match both:
    case (f, b):
      (a => f(all_kl_sub(Core.steps([tree], 0n), fuel, grammar, start, input, set, a)),
        c => all_live(Core.steps([tree], 0n), fuel, grammar, start, input, set, tree, C.step_refl(Core.steps([tree], 0n)), b(c), rr, rl, hok))

def live_pt2(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +hok: {okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}, emb: Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set))
  -> ({Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}):
  live_tree(fuel, grammar, start, input, set, gmarks, rmarks, tree, rr, rl, hok, emb(tree, (rr, rl)))

def live_pt(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +tree: Core.Tree, pt: Core.ParseTree(grammar, start, input, tree),
  +hok: {okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}, emb: Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set))
  -> ({Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool} -> Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree)) &
    (Oracle.Chosen(grammar, gmarks, rmarks, start, input, tree) -> {Core.allIn(Core.steps([tree], 0n), keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}):
  match pt:
    case (rr0, rl0):
      live_pt2(fuel, grammar, start, input, set, gmarks, rmarks, tree, rr0, rl0, hok, emb)

# The live set of an embedding set embeds the chosen trees.
def embeds_live(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +hok: {okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}, emb: Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set))
  -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, keptOf(liveOf(fuel, grammar, start, input, set))):
  tree => pt => live_pt(fuel, grammar, start, input, set, gmarks, rmarks, tree, pt, hok, emb)

def someOr(m: Maybe<&2, +List<Core.Bsr>>, +d: +List<Core.Bsr>) -> +List<Core.Bsr>:
  match m:
    case Some{+x}:
      x
    case None{}:
      d

def ok_eq(ok: Bool, +s: +List<Core.Bsr>, +t: +List<Core.Bsr>, +e: {Extent.okPick(ok, s) == Some{t} : Maybe<&2, +List<Core.Bsr>>}) -> {s == t : +List<Core.Bsr>}:
  match ok:
    case True{}:
      Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => someOr(v, s), Some{s}, Some{t}, e)
    case False{}:
      Empty.absurd({s == t : +List<Core.Bsr>}, G.none_not_some(t, e))

def ok_true(ok: Bool, +s: +List<Core.Bsr>, +t: +List<Core.Bsr>, +e: {Extent.okPick(ok, s) == Some{t} : Maybe<&2, +List<Core.Bsr>>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, G.none_not_some(t, e))

# What a pass that answers hands out: its live steps, and it answered.
law live_eq:
  for out: Extent.Live
  for +t: +List<Core.Bsr>
  for +e: {Extent.livePick(out) == Some{t} : Maybe<&2, +List<Core.Bsr>>}
  {keptOf(out) == t : +List<Core.Bsr>}

def live_eq(out, t, e):
  match out:
    case Extent.Live{+ok, +kept, +trees}:
      ok_eq(ok, kept, t, e)

law live_ok:
  for out: Extent.Live
  for +t: +List<Core.Bsr>
  for +e: {Extent.livePick(out) == Some{t} : Maybe<&2, +List<Core.Bsr>>}
  {okOf(out) == True{} : Bool}

def live_ok(out, t, e):
  match out:
    case Extent.Live{+ok, +kept, +trees}:
      ok_true(ok, kept, t, e)

def lf_some(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +s0: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +eo: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == Some{s0} : Maybe<&2, +List<Core.Bsr>>},
  +el: {Extent.livePick(liveOf(fuel, grammar, start, input, s0)) == Some{set} : Maybe<&2, +List<Core.Bsr>>})
  -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set):
  +L = liveOf(fuel, grammar, start, input, s0)
  %live_eq(L, set, el) : Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, _)
  embeds_live(fuel, grammar, start, input, s0, gmarks, rmarks, live_ok(L, set, el), PO.oracle_exact(fuel, grammar, gmarks, rmarks, start, input, s0, eo))

def lf_from(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +eo: {Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input) == m : Maybe<&2, +List<Core.Bsr>>},
  +el: {Extent.liveFrom(m, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>})
  -> Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set):
  match m:
    case Some{+s0}:
      lf_some(fuel, grammar, gmarks, rmarks, start, input, s0, set, eo, el)
    case None{}:
      Empty.absurd(Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set), G.none_not_some(set, el))

# THE LIVE SET EMBEDS EXACTLY THE CHOSEN TREES: whatever `liveFrom` hands out for the
# oracle's set, a parse tree uses only its steps when, and only when, it is chosen.
law live_embeds:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +el: {Extent.liveFrom(Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input), fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Oracle.EmbedsChosen(grammar, gmarks, rmarks, start, input, set)

def live_embeds(fuel, grammar, gmarks, rmarks, start, input, set, el):
  +f = fuel
  lf_from(Oracle.oracleSteps(f, grammar, gmarks, rmarks, start, input), f, grammar, gmarks, rmarks, start, input, set, {==}, el)
