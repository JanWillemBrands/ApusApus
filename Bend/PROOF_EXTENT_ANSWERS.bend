import Base
import ./LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./WITNESS.bend as W
import ./EXACT.bend as Exact
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./ORACLE.bend as Oracle
import ./EXTENT.bend as Extent
import ./RUN.bend as Run
import ./PROOF_GLL.bend as G
import ./PROOF_COUNT.bend as C
import ./PROOF_RUN.bend as R
import ./PROOF_WITNESS.bend as WC
import ./PROOF_WSOUND.bend as WS
import ./PROOF_WINSIDE.bend as WI
import ./PROOF_LIVE.bend as PL
import ./PROOF_ORACLE_ANSWERS.bend as O

# THE SELECTING ORACLE ANSWERS (EXTENT.bend). With fuel 1 + twice the size of the
# descriptor universe the oracle answers with steps within bounds; every witness search on
# them is closed, so `liveFrom` drops only dead wood and answers; every live step lies on a
# tree the pass found, a parse tree inside the oracle's set whose steps are all live, so the
# witness search inside the live set finds one, and the cover check passes.

# ======== THE SETS LIE WITHIN BOUNDS ========

def ky_b(b: Bool, +e: Core.Bsr, +more: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +he: {Run.stepBound(e, grammar, input) == True{} : Bool}, +hm: {Run.stepsBounded(more, grammar, input) == True{} : Bool})
  -> {Run.stepsBounded(Oracle.keepIf(b, e, more), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(Run.stepBound(e, grammar, input), Run.stepsBounded(more, grammar, input), he, hm)
    case False{}:
      hm

law keep_yes_b:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  for +h: {Run.stepsBounded(xs, grammar, input) == True{} : Bool}
  {Run.stepsBounded(Oracle.keepYes(xs, fuel, grammar, gmarks, rmarks, start, input), grammar, input) == True{} : Bool}

def keep_yes_b(xs, fuel, grammar, gmarks, rmarks, start, input, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +B = {Run.stepBound(e, grammar, input) : Bool}
      ky_b(Guard.isYes(Oracle.stepTri(fuel, grammar, gmarks, rmarks, start, input, e)), e, Oracle.keepYes(rest, fuel, grammar, gmarks, rmarks, start, input), grammar, input,
        Lemma.and_true_left(B, Run.stepsBounded(rest, grammar, input), h), keep_yes_b(rest, fuel, grammar, gmarks, rmarks, start, input, Lemma.and_true_right_side(B, Run.stepsBounded(rest, grammar, input), h)))

def opick_b(b: Bool, +ex: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +h: {Run.stepsBounded(ex, grammar, input) == True{} : Bool})
  -> {O.mBounded(Oracle.oraclePick(b, ex, fuel, grammar, gmarks, rmarks, start, input), grammar, input) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      keep_yes_b(ex, fuel, grammar, gmarks, rmarks, start, input, h)

def ofrom_b(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>, +h: {O.mBounded(m, grammar, input) == True{} : Bool})
  -> {O.mBounded(Oracle.oracleFrom(m, fuel, grammar, gmarks, rmarks, start, input), grammar, input) == True{} : Bool}:
  match m:
    case Some{+ex}:
      opick_b(Oracle.anyUnknown(ex, fuel, grammar, gmarks, rmarks, start, input), ex, fuel, grammar, gmarks, rmarks, start, input, h)
    case None{}:
      {==}

# The oracle's steps lie within bounds.
def oracle_bounded(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +rmarks: +List<Prefer.RankMark>, +start: Nat, +input: +List<Nat>)
  -> {O.mBounded(Oracle.oracleSteps(fuel, grammar, gmarks, rmarks, start, input), grammar, input) == True{} : Bool}:
  ofrom_b(Exact.exactSteps(fuel, grammar, start, input), fuel, grammar, gmarks, rmarks, start, input, O.exact_bounded(fuel, grammar, start, input))

def liveOf(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Extent.Live:
  Extent.liveRun(set, [], fuel, grammar, start, input, set)

def lc_bounded(k: Bool, c: Bool, +y: Core.Bsr, +out: Extent.Live, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +he: {Run.stepBound(y, grammar, input) == True{} : Bool}, +ho: {Run.stepsBounded(PL.keptOf(out), grammar, input) == True{} : Bool})
  -> {Run.stepsBounded(PL.keptOf(Extent.liveCons(k, c, y, out)), grammar, input) == True{} : Bool}:
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Lemma.and_true_intro(Run.stepBound(y, grammar, input), Run.stepsBounded(kept, grammar, input), he, ho)
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          ho

law kept_bounded:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +h: {Run.stepsBounded(xs, grammar, input) == True{} : Bool}
  {Run.stepsBounded(PL.keptOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set)), grammar, input) == True{} : Bool}

def kept_bounded(xs, ws, fuel, grammar, start, input, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +B = {Run.stepBound(y, grammar, input) : Bool}
      +cov = {W.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      lc_bounded(Bool.or(cov, Extent.hasRoot(r)), W.closedW(set, grammar, input, y, F), y, Extent.liveRun(rest, W.addWitness(r, ws), fuel, grammar, start, input, set), grammar, input,
        Lemma.and_true_left(B, Run.stepsBounded(rest, grammar, input), h),
        kept_bounded(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, Lemma.and_true_right_side(B, Run.stepsBounded(rest, grammar, input), h)))

# ======== THE PASS ANSWERS: A STEP NOT COVERED HAS CLOSED FACTS ========

def lc_ok(k: Bool, c: Bool, +y: Core.Bsr, +out: Extent.Live, +hor: {Bool.or(k, c) == True{} : Bool}, +ho: {PL.okOf(out) == True{} : Bool})
  -> {PL.okOf(Extent.liveCons(k, c, y, out)) == True{} : Bool}:
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          ho
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          Lemma.and_true_intro(c, ok, hor, ho)

law search_or:
  for cov: Bool
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +y: Core.Bsr
  for +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}
  {Bool.or(Bool.or(cov, Extent.hasRoot(Extent.rootIf(cov, grammar, start, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)))), W.closedW(set, grammar, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y))) == True{} : Bool}

def search_or(cov, fuel, grammar, start, input, set, y, hy, hf):
  match cov:
    case True{}:
      {==}
    case False{}:
      +F = W.fixpoint(fuel, set, grammar, input, y, [])
      Lemma.or_true_right_intro(Extent.hasRoot(W.rootFor(grammar, grammar, y, 0n, start, List.length(&2, Nat, input), F)), W.closedW(set, grammar, input, y, F), WC.witness_closed(fuel, set, grammar, input, y, hy, hf))

law ok_all:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}
  {PL.okOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set)) == True{} : Bool}

def ok_all(xs, ws, fuel, grammar, start, input, set, hy, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +cov = {W.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      lc_ok(Bool.or(cov, Extent.hasRoot(r)), W.closedW(set, grammar, input, y, F), y, Extent.liveRun(rest, W.addWitness(r, ws), fuel, grammar, start, input, set),
        search_or(cov, fuel, grammar, start, input, set, y, hy, hf),
        ok_all(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, hy, hf))

# ======== EVERY LIVE STEP LIES ON A TREE THE PASS FOUND ========

def kc_trees(k: Bool, c: Bool, +x: Core.Bsr, +y: Core.Bsr, +out: Extent.Live, +h: {W.coveredBy(x, PL.treesOf(out)) == True{} : Bool})
  -> {W.coveredBy(x, PL.treesOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}:
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          h
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          h

def add_grows(m: Maybe<&2, +List<Core.Tree>>, +ws: +List<Core.Tree>, +z: Core.Bsr, +h: {W.coveredBy(z, ws) == True{} : Bool})
  -> {W.coveredBy(z, W.addWitness(m, ws)) == True{} : Bool}:
  match m:
    case Some{+fs}:
      match fs:
        case Nil{}:
          h
        case Con{+t, +more}:
          match more:
            case Nil{}:
              Lemma.or_true_right_intro(Core.member(z, Core.steps([t], 0n)), W.coveredBy(z, ws), h)
            case Con{+t2, +more2}:
              h
    case None{}:
      h

# The trees only grow.
law covered_grows:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +z: Core.Bsr
  for +h: {W.coveredBy(z, ws) == True{} : Bool}
  {W.coveredBy(z, PL.treesOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set))) == True{} : Bool}

def covered_grows(xs, ws, fuel, grammar, start, input, set, z, h):
  match xs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      +cov = {W.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      kc_trees(Bool.or(cov, Extent.hasRoot(r)), W.closedW(set, grammar, input, y, F), z, y, Extent.liveRun(rest, W.addWitness(r, ws), fuel, grammar, start, input, set),
        covered_grows(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, z, add_grows(r, ws, z, h)))

def root_covers(m: Maybe<&2, +List<Core.Tree>>, +ws: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +y: Core.Bsr,
  +hr: {Extent.hasRoot(m) == True{} : Bool}, +hg: {WS.rootGood(m, grammar, input, y, start) == True{} : Bool})
  -> {W.coveredBy(y, W.addWitness(m, ws)) == True{} : Bool}:
  match m:
    case Some{+fs}:
      match fs:
        case Nil{}:
          Empty.absurd({W.coveredBy(y, ws) == True{} : Bool}, Lemma.false_is_not_true(hg))
        case Con{+t, +more}:
          match more:
            case Nil{}:
              Lemma.or_true_left_intro(Core.member(y, Core.steps([t], 0n)), W.coveredBy(y, ws),
                Lemma.and_true_right_side(Exact.treeOk(grammar, start, input, t), Core.member(y, Core.steps([t], 0n)), hg))
            case Con{+t2, +more2}:
              Empty.absurd({W.coveredBy(y, ws) == True{} : Bool}, Lemma.false_is_not_true(hg))
    case None{}:
      Empty.absurd({W.coveredBy(y, ws) == True{} : Bool}, Lemma.false_is_not_true(hr))

# A kept step that was covered stays covered; one kept for its root lies on the tree found.
law kc_head:
  for cov: Bool
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +y: Core.Bsr
  for +ws: +List<Core.Tree>
  for +hcov: {W.coveredBy(y, ws) == cov : Bool}
  for +hk: {Bool.or(cov, Extent.hasRoot(Extent.rootIf(cov, grammar, start, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)))) == True{} : Bool}
  {W.coveredBy(y, W.addWitness(Extent.rootIf(cov, grammar, start, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)), ws)) == True{} : Bool}

def kc_head(cov, fuel, grammar, start, input, set, y, ws, hcov, hk):
  match cov:
    case True{}:
      hcov
    case False{}:
      root_covers(W.witnessFor(fuel, grammar, start, input, set, y), ws, grammar, start, input, y, hk, WS.witness_good(fuel, grammar, start, input, set, y))

def cov_to(+x: Core.Bsr, +y: Core.Bsr, +ex: {x == y : Core.Bsr}, +T: +List<Core.Tree>, +h: {W.coveredBy(y, T) == True{} : Bool}) -> {W.coveredBy(x, T) == True{} : Bool}:
  %Equal.sym(Core.Bsr, x, y, ex) : {W.coveredBy(_, T) == True{} : Bool}
  h

def kc_pick(+k: Bool, +c: Bool, +x: Core.Bsr, +y: Core.Bsr, +out: Extent.Live,
  cases: Either<({Core.bsrEq(x, y) == True{} : Bool} & {k == True{} : Bool}), {Core.member(x, PL.keptOf(out)) == True{} : Bool}>,
  head: {k == True{} : Bool} -> {W.coveredBy(y, PL.treesOf(out)) == True{} : Bool},
  later: {Core.member(x, PL.keptOf(out)) == True{} : Bool} -> {W.coveredBy(x, PL.treesOf(out)) == True{} : Bool})
  -> {W.coveredBy(x, PL.treesOf(Extent.liveCons(k, c, y, out))) == True{} : Bool}:
  match cases:
    case Inl{p}:
      match p:
        case (+e, +hk):
          kc_trees(k, c, x, y, out, cov_to(x, y, G.bsr_eq_sound(x, y, e), PL.treesOf(out), head(hk)))
    case Inr{m}:
      kc_trees(k, c, x, y, out, later(m))

law kept_covered:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +m: {Core.member(x, PL.keptOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set))) == True{} : Bool}
  {W.coveredBy(x, PL.treesOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set))) == True{} : Bool}

def kept_covered(xs, ws, fuel, grammar, start, input, set, x, m):
  match xs:
    case Nil{}:
      Empty.absurd({W.coveredBy(x, ws) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +cov = {W.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      +K = {Bool.or(cov, Extent.hasRoot(r)) : Bool}
      +CL = {W.closedW(set, grammar, input, y, F) : Bool}
      +out = Extent.liveRun(rest, W.addWitness(r, ws), fuel, grammar, start, input, set)
      kc_pick(K, CL, x, y, out, PL.lc_cases(K, CL, x, y, out, m),
        hk => covered_grows(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, y, kc_head(cov, fuel, grammar, start, input, set, y, ws, {==}, hk)),
        m2 => kept_covered(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, x, m2))

# ======== THE TREES FOUND ARE PARSE TREES INSIDE THE SET ========

def kg_trees(k: Bool, c: Bool, +y: Core.Bsr, +out: Extent.Live, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +h: {Extent.allTreesIn(PL.treesOf(out), grammar, start, input, set) == True{} : Bool})
  -> {Extent.allTreesIn(PL.treesOf(Extent.liveCons(k, c, y, out)), grammar, start, input, set) == True{} : Bool}:
  match k:
    case True{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          h
    case False{}:
      match out:
        case Extent.Live{+ok, +kept, +trees}:
          h

def root_adds(m: Maybe<&2, +List<Core.Tree>>, +ws: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +y: Core.Bsr,
  +hg: {WS.rootGood(m, grammar, input, y, start) == True{} : Bool}, +hi: {WI.rootIn(m, set) == True{} : Bool},
  +h: {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool})
  -> {Extent.allTreesIn(W.addWitness(m, ws), grammar, start, input, set) == True{} : Bool}:
  match m:
    case Some{+fs}:
      match fs:
        case Nil{}:
          h
        case Con{+t, +more}:
          match more:
            case Nil{}:
              +OK = {Exact.treeOk(grammar, start, input, t) : Bool}
              +IN = {Core.allIn(Core.steps([t], 0n), set) : Bool}
              Lemma.and_true_intro(Extent.treeIn(grammar, start, input, set, t), Extent.allTreesIn(ws, grammar, start, input, set),
                Lemma.and_true_intro(OK, IN, Lemma.and_true_left(OK, Core.member(y, Core.steps([t], 0n)), hg), Lemma.and_true_left(IN, True{}, hi)), h)
            case Con{+t2, +more2}:
              h
    case None{}:
      h

law add_good:
  for cov: Bool
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +y: Core.Bsr
  for +ws: +List<Core.Tree>
  for +h: {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool}
  {Extent.allTreesIn(W.addWitness(Extent.rootIf(cov, grammar, start, input, y, Extent.searchIf(cov, fuel, grammar, input, set, y)), ws), grammar, start, input, set) == True{} : Bool}

def add_good(cov, fuel, grammar, start, input, set, y, ws, h):
  match cov:
    case True{}:
      h
    case False{}:
      root_adds(W.witnessFor(fuel, grammar, start, input, set, y), ws, grammar, start, input, set, y, WS.witness_good(fuel, grammar, start, input, set, y), WI.witness_in(fuel, grammar, start, input, set, y), h)

law trees_good:
  for xs: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +h: {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool}
  {Extent.allTreesIn(PL.treesOf(Extent.liveRun(xs, ws, fuel, grammar, start, input, set)), grammar, start, input, set) == True{} : Bool}

def trees_good(xs, ws, fuel, grammar, start, input, set, h):
  match xs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      +cov = {W.coveredBy(y, ws) : Bool}
      +F = Extent.searchIf(cov, fuel, grammar, input, set, y)
      +r = Extent.rootIf(cov, grammar, start, input, y, F)
      kg_trees(Bool.or(cov, Extent.hasRoot(r)), W.closedW(set, grammar, input, y, F), y, Extent.liveRun(rest, W.addWitness(r, ws), fuel, grammar, start, input, set), grammar, start, input, set,
        trees_good(rest, W.addWitness(r, ws), fuel, grammar, start, input, set, add_good(cov, fuel, grammar, start, input, set, y, ws, h)))

# ======== THE SEARCH INSIDE THE LIVE SET FINDS EVERY LIVE STEP ========

# A step of a parse tree inside the set has a tree inside the live set.
def found_tree(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr, +t: Core.Tree,
  +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool},
  +hok: {PL.okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool},
  +ok: {Exact.treeOk(grammar, start, input, t) == True{} : Bool},
  +mx: {Core.member(x, Core.steps([t], 0n)) == True{} : Bool},
  +hin: {Core.allIn(Core.steps([t], 0n), set) == True{} : Bool})
  -> {WC.isTrees(W.witnessFor(fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set)), x)) == True{} : Bool}:
  +RR = {Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) : Bool}
  +RL = {Nat.is_eq(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input)) : Bool}
  +rr = Lemma.and_true_left(RR, RL, ok)
  +rl = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves([t])), List.length(&2, Nat, input), Lemma.and_true_right_side(RR, RL, ok))
  +LIVE = PL.keptOf(liveOf(fuel, grammar, start, input, set))
  +inL = PL.all_live(Core.steps([t], 0n), fuel, grammar, start, input, set, t, C.step_refl(Core.steps([t], 0n)), hin, rr, rl, hok)
  +Fx = W.fixpoint(fuel, LIVE, grammar, input, x, [])
  WC.root_found(t, grammar, start, input, LIVE, x, Fx, WC.witness_closed(fuel, LIVE, grammar, input, x, kept_bounded(set, [], fuel, grammar, start, input, set, hy), hf), inL, rr, rl, mx)

def found_or(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +x: Core.Bsr, +t: Core.Tree, +rest: +List<Core.Tree>,
  +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool},
  +hok: {PL.okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool},
  +hg: {Extent.treeIn(grammar, start, input, set, t) == True{} : Bool},
  cases: Either<{Core.member(x, Core.steps([t], 0n)) == True{} : Bool}, {W.coveredBy(x, rest) == True{} : Bool}>,
  later: {W.coveredBy(x, rest) == True{} : Bool} -> {WC.isTrees(W.witnessFor(fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set)), x)) == True{} : Bool})
  -> {WC.isTrees(W.witnessFor(fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set)), x)) == True{} : Bool}:
  match cases:
    case Inl{mx}:
      +OK = {Exact.treeOk(grammar, start, input, t) : Bool}
      +IN = {Core.allIn(Core.steps([t], 0n), set) : Bool}
      found_tree(fuel, grammar, start, input, set, x, t, hy, hf, hok, Lemma.and_true_left(OK, IN, hg), mx, Lemma.and_true_right_side(OK, IN, hg))
    case Inr{m}:
      later(m)

law covered_found:
  for ts: +List<Core.Tree>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +x: Core.Bsr
  for +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}
  for +hok: {PL.okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}
  for +hc: {W.coveredBy(x, ts) == True{} : Bool}
  for +hg: {Extent.allTreesIn(ts, grammar, start, input, set) == True{} : Bool}
  {WC.isTrees(W.witnessFor(fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set)), x)) == True{} : Bool}

def covered_found(ts, fuel, grammar, start, input, set, x, hy, hf, hok, hc, hg):
  match ts:
    case Nil{}:
      Empty.absurd({WC.isTrees(W.witnessFor(fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set)), x)) == True{} : Bool}, Lemma.false_is_not_true(hc))
    case Con{+t, +rest}:
      +TI = {Extent.treeIn(grammar, start, input, set, t) : Bool}
      found_or(fuel, grammar, start, input, set, x, t, rest, hy, hf, hok, Lemma.and_true_left(TI, Extent.allTreesIn(rest, grammar, start, input, set), hg),
        Lemma.or_true_cases(Core.member(x, Core.steps([t], 0n)), W.coveredBy(x, rest), hc),
        m => covered_found(rest, fuel, grammar, start, input, set, x, hy, hf, hok, m, Lemma.and_true_right_side(TI, Extent.allTreesIn(rest, grammar, start, input, set), hg)))

law all_found_live:
  for xs: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +hsub: {Core.allIn(xs, PL.keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}
  for +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}
  for +hok: {PL.okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool}
  {WS.allFound(xs, fuel, grammar, start, input, PL.keptOf(liveOf(fuel, grammar, start, input, set))) == True{} : Bool}

def all_found_live(xs, fuel, grammar, start, input, set, hsub, hy, hf, hok):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +LIVE = PL.keptOf(liveOf(fuel, grammar, start, input, set))
      +mx = Lemma.and_true_left(Core.member(x, LIVE), Core.allIn(rest, LIVE), hsub)
      +TS = PL.treesOf(liveOf(fuel, grammar, start, input, set))
      Lemma.and_true_intro(WC.isTrees(W.witnessFor(fuel, grammar, start, input, LIVE, x)), WS.allFound(rest, fuel, grammar, start, input, LIVE),
        covered_found(TS, fuel, grammar, start, input, set, x, hy, hf, hok, kept_covered(set, [], fuel, grammar, start, input, set, x, mx), trees_good(set, [], fuel, grammar, start, input, set, {==})),
        all_found_live(rest, fuel, grammar, start, input, set, Lemma.and_true_right_side(Core.member(x, LIVE), Core.allIn(rest, LIVE), hsub), hy, hf, hok))

# ======== THE COVER CHECK PASSES ========

law trees_in_ok:
  for ws: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +h1: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +h2: {WI.treesIn(ws, set) == True{} : Bool}
  {Extent.allTreesIn(ws, grammar, start, input, set) == True{} : Bool}

def trees_in_ok(ws, grammar, start, input, set, h1, h2):
  match ws:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      +OK = {Exact.treeOk(grammar, start, input, t) : Bool}
      +IN = {Core.allIn(Core.steps([t], 0n), set) : Bool}
      Lemma.and_true_intro(Extent.treeIn(grammar, start, input, set, t), Extent.allTreesIn(rest, grammar, start, input, set),
        Lemma.and_true_intro(OK, IN, Lemma.and_true_left(OK, Exact.allTreesOk(rest, grammar, start, input), h1), Lemma.and_true_left(IN, WI.treesIn(rest, set), h2)),
        trees_in_ok(rest, grammar, start, input, set, Lemma.and_true_right_side(OK, Exact.allTreesOk(rest, grammar, start, input), h1), Lemma.and_true_right_side(IN, WI.treesIn(rest, set), h2)))

def epick_a(b: Bool, +s: +List<Core.Bsr>, +eb: {b == True{} : Bool}) -> {R.isAnswer(Exact.exactPick(b, s)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(eb))

def cover_live(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>, +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}, +hok: {PL.okOf(liveOf(fuel, grammar, start, input, set)) == True{} : Bool})
  -> {R.isAnswer(Extent.coverFrom(Some{PL.keptOf(liveOf(fuel, grammar, start, input, set))}, fuel, grammar, start, input)) == True{} : Bool}:
  +S2 = PL.keptOf(liveOf(fuel, grammar, start, input, set))
  +ws = W.witnesses(fuel, grammar, start, input, S2)
  +co = WS.cover_ok(S2, fuel, grammar, start, input, S2, [], {==}, all_found_live(S2, fuel, grammar, start, input, set, C.step_refl(S2), hy, hf, hok))
  +TO = {Exact.allTreesOk(ws, grammar, start, input) : Bool}
  +CV = {Exact.allCovered(S2, ws) : Bool}
  epick_a(Bool.and(Extent.allTreesIn(ws, grammar, start, input, S2), CV), S2,
    Lemma.and_true_intro(Extent.allTreesIn(ws, grammar, start, input, S2), CV,
      trees_in_ok(ws, grammar, start, input, S2, Lemma.and_true_left(TO, CV, co), WI.cover_in(S2, fuel, grammar, start, input, S2, [], {==})),
      Lemma.and_true_right_side(TO, CV, co)))

def ok_some(ok: Bool, +kept: +List<Core.Bsr>, +h: {ok == True{} : Bool}) -> {Extent.okPick(ok, kept) == Some{kept} : Maybe<&2, +List<Core.Bsr>>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({None{} == Some{kept} : Maybe<&2, +List<Core.Bsr>>}, Lemma.false_is_not_true(h))

# A pass that answers hands out its live steps.
law live_some:
  for out: Extent.Live
  for +h: {PL.okOf(out) == True{} : Bool}
  {Extent.livePick(out) == Some{PL.keptOf(out)} : Maybe<&2, +List<Core.Bsr>>}

def live_some(out, h):
  match out:
    case Extent.Live{+ok, +kept, +trees}:
      ok_some(ok, kept, h)

def chosen_some(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +hy: {Run.stepsBounded(set, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool})
  -> {R.isAnswer(Extent.coverFrom(Extent.livePick(liveOf(fuel, grammar, start, input, set)), fuel, grammar, start, input)) == True{} : Bool}:
  +L = liveOf(fuel, grammar, start, input, set)
  +hok = ok_all(set, [], fuel, grammar, start, input, set, hy, hf)
  %Equal.sym(Maybe<&2, +List<Core.Bsr>>, Extent.livePick(L), Some{PL.keptOf(L)}, live_some(L, hok)) : {R.isAnswer(Extent.coverFrom(_, fuel, grammar, start, input)) == True{} : Bool}
  cover_live(fuel, grammar, start, input, set, hy, hf, hok)

def chosen_from(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  +hs: {R.isAnswer(m) == True{} : Bool}, +hb: {O.mBounded(m, grammar, input) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool})
  -> {R.isAnswer(Extent.coverFrom(Extent.liveFrom(m, fuel, grammar, start, input), fuel, grammar, start, input)) == True{} : Bool}:
  match m:
    case Some{+set}:
      chosen_some(fuel, grammar, start, input, set, hb, hf)
    case None{}:
      Empty.absurd({R.isAnswer(None{}) == True{} : Bool}, Lemma.false_is_not_true(hs))

def select_a(m: Maybe<&2, +List<Core.Bsr>>, +grammar: +List<Core.Production>, +emarks: +List<Extent.ExtentMark>, +h: {R.isAnswer(m) == True{} : Bool})
  -> {R.isAnswer(Extent.selectFrom(m, grammar, emarks)) == True{} : Bool}:
  match m:
    case Some{+set}:
      {==}
    case None{}:
      Empty.absurd({R.isAnswer(None{}) == True{} : Bool}, Lemma.false_is_not_true(h))

# THE CHOSEN SET AND THE SELECTING ORACLE ANSWER: with fuel 1 + twice the size of the
# descriptor universe, `chosenSteps` and `selectedSteps` hand out their sets, on every
# grammar, marks and input.
law chosen_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Extent.chosenSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, start, input)) == True{} : Bool}

def chosen_answers(grammar, gmarks, rmarks, start, input):
  +F = {1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) : Nat}
  chosen_from(Oracle.oracleSteps(F, grammar, gmarks, rmarks, start, input), F, grammar, start, input,
    O.oracle_answers(grammar, gmarks, rmarks, start, input), oracle_bounded(F, grammar, gmarks, rmarks, start, input), Lemma.le_refl(F))

law extent_answers:
  for +grammar: +List<Core.Production>
  for +gmarks: +List<Guard.GuardMark>
  for +rmarks: +List<Prefer.RankMark>
  for +emarks: +List<Extent.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  {R.isAnswer(Extent.selectedSteps(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), grammar, gmarks, rmarks, emarks, start, input)) == True{} : Bool}

def extent_answers(grammar, gmarks, rmarks, emarks, start, input):
  +F = {1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))) : Nat}
  select_a(Extent.chosenSteps(F, grammar, gmarks, rmarks, start, input), grammar, emarks, chosen_answers(grammar, gmarks, rmarks, start, input))
