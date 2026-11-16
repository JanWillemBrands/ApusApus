import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PREFER.bend as Prefer
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_LL1.bend as L
import ./PROOF_TABLES.bend as PT

# THE PREDICTING PARSER MISSES NOTHING. A node of q at k in a parse tree predicts the token
# at k (PROOF_LL1.bend), so that token is in q's predict set by the closed tables
# (PROOF_TABLES.bend): prediction admits every node of every parse tree. A state closed for
# the admitted descriptors then has every step of the tree (PROOF_GLL.bend, walked with the
# predictor).

# ======== THE PREDICT SETS ========

law set_at:
  for g: +List<Core.Production>
  for q: Nat
  for +z: Nat
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +hl: {Core.lhsIs(g, q, z) == True{} : Bool}
  {Gll.setAt(Pr.predictSets(g, firsts, follows, nulls), q) == T.predictOf(Gll.lhsOf(g, q), Core.rhsOf(g, q), firsts, follows, nulls) : +List<Maybe<&2, Nat>>}

def set_at(g, q, z, firsts, follows, nulls, hl):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Gll.setAt(Pr.predictSets([], firsts, follows, nulls), q0) == T.predictOf(Gll.lhsOf([], q0), Core.rhsOf([], q0), firsts, follows, nulls) : +List<Maybe<&2, Nat>>}, Lemma.false_is_not_true(hl))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      set_at(rest, n, z, firsts, follows, nulls, hl)

law tok_eq_of:
  for a: Maybe<&2, Nat>
  for b: Maybe<&2, Nat>
  for +h: {T.maybeEq(a, b) == True{} : Bool}
  {Gll.tokEq(a, b) == True{} : Bool}

def tok_eq_of(a, b, h):
  match a b:
    case None{} None{}:
      {==}
    case Some{+x} Some{+y}:
      h
    case None{} Some{+y}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Some{+x} None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def tok_pick(+y: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>,
  cases: Either<{T.maybeEq(n, y) == True{} : Bool}, {T.maybeIn(n, rest) == True{} : Bool}>,
  later: {T.maybeIn(n, rest) == True{} : Bool} -> {Gll.tokIn(n, rest) == True{} : Bool}) -> {Gll.tokIn(n, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Gll.tokEq(n, y), Gll.tokIn(n, rest), tok_eq_of(n, y, e))
    case Inr{m}:
      Lemma.or_true_right_intro(Gll.tokEq(n, y), Gll.tokIn(n, rest), later(m))

law tok_in_of:
  for xs: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +h: {T.maybeIn(n, xs) == True{} : Bool}
  {Gll.tokIn(n, xs) == True{} : Bool}

def tok_in_of(xs, n, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      tok_pick(y, rest, n, Lemma.or_true_cases(T.maybeEq(n, y), T.maybeIn(n, rest), h), m => tok_in_of(rest, n, m))

# ======== EVERY NODE OF A PARSE TREE IS ADMITTED ========

law admits_walk:
  for fs: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +nulls: +List<Nat>
  for +root: Core.Tree
  for +rr: {Core.reads([root], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([root])) == List.length(&2, Nat, input) : Nat}
  for +cn: {Prefer.nullsClosed(grammar, nulls) == True{} : Bool}
  for +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool}
  for +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool}
  for +cs: {T.followHas(start, None{}, follows) == True{} : Bool}
  for +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool}
  for +k: Nat
  for +rd: {Core.reads(fs, grammar, items, input, k) == True{} : Bool}
  for +inR: {Core.allIn(Core.steps(fs, k), Core.steps([root], 0n)) == True{} : Bool}
  {Check.admitsAll(fs, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, input, k) == True{} : Bool}

def admits_walk(fs, items, grammar, start, input, firsts, follows, nulls, root, rr, rl, cn, cf, cfo, cs, cr, k, rd, inR):
  match fs items:
    case Nil{} +its:
      {==}
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, rd))
      admits_walk(ts, rest, grammar, start, input, firsts, follows, nulls, root, rr, rl, cn, cf, cfo, cs, cr, 1n+k, rt, inR)
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Check.admitsAll(Core.Leaf{a} <> ts, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, input, k) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      Empty.absurd({Check.admitsAll(Core.Leaf{a} <> ts, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, input, k) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({Check.admitsAll(Core.Node{q, ch} <> ts, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, input, k) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Check.admitsAll(Core.Node{q, ch} <> ts, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, input, k) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      +sets = Pr.predictSets(grammar, firsts, follows, nulls)
      +pred = {Gll.Allowed{sets} : Gll.Pred}
      +S = {Core.steps([root], 0n) : +List<Core.Bsr>}
      +far = Nat.add(k, Core.width(Core.Node{q, ch}))
      +head = {Bool.and(Core.lhsIs(grammar, q, z), Core.needOk(need, Core.width(Core.Node{q, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), rd)
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, q, z), Core.needOk(need, Core.width(Core.Node{q, ch})), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), rd)
      +below = P.in_app_right(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), S, inR)
      +io = P.in_app_left(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), S, inR)
      +ic = P.in_app_left(Core.steps(ch, k), Core.steps(ts, far), S, below)
      +it = P.in_app_right(Core.steps(ch, k), Core.steps(ts, far), S, below)
      p = L.predicts_node(Core.leaves(ch), grammar, start, input, root, rr, rl, q, ch, k, {==}, rc, io)
      +m = PT.predicts_in(grammar, start, firsts, follows, nulls, q, Core.tokAt(input, k), cn, cf, cfo, cs, cr, p)
      +ti = tok_in_of(T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls), Core.tokAt(input, k), m)
      +ad = {(%Equal.sym(+List<Maybe<&2, Nat>>, Gll.setAt(sets, q), T.predictOf(Gll.lhsOf(grammar, q), Core.rhsOf(grammar, q), firsts, follows, nulls), set_at(grammar, q, z, firsts, follows, nulls, hl)) : {Gll.tokIn(Core.tokAt(input, k), _) == True{} : Bool}
        ti) : {Gll.admits(pred, q, Core.tokAt(input, k)) == True{} : Bool}}
      Lemma.and_true_intro(Gll.admits(pred, q, Core.tokAt(input, k)), Bool.and(Check.admitsAll(ch, pred, input, k), Check.admitsAll(ts, pred, input, far)), ad,
        Lemma.and_true_intro(Check.admitsAll(ch, pred, input, k), Check.admitsAll(ts, pred, input, far),
          admits_walk(ch, Core.rhsOf(grammar, q), grammar, start, input, firsts, follows, nulls, root, rr, rl, cn, cf, cfo, cs, cr, k, rc, ic),
          admits_walk(ts, rest, grammar, start, input, firsts, follows, nulls, root, rr, rl, cn, cf, cfo, cs, cr, far, rt, it)))

# ======== THE LAW ========

def from_tree(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>,
  +s: Gll.GState, +set: +List<Core.Bsr>,
  +cn: {Prefer.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  +hc: {Check.closedWith(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, s) == True{} : Bool},
  +root: {Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)) == True{} : Bool},
  +es: {Check.stepsOf(s) == set : +List<Core.Bsr>},
  +tree: Core.Tree, +x: Core.Bsr, pt: Core.ParseTree(grammar, start, input, tree),
  +m: {Core.member(x, Core.steps([tree], 0n)) == True{} : Bool}) -> {Core.member(x, set) == True{} : Bool}:
  match pt:
    case (rr0, rl0):
      +rr = rr0
      +rl = {rl0 : {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}}
      +pred = {Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)} : Gll.Pred}
      +ad = admits_walk([tree], [Core.Nonterminal{start, Core.Anything{}}], grammar, start, input, firsts, follows, nulls, tree, rr, rl, cn, cf, cfo, cs, cr, 0n, rr, L.all_in_refl(Core.steps([tree], 0n)))
      %es : {Core.member(x, _) == True{} : Bool}
      G.all_in_member(Core.steps([tree], 0n), Check.stepsOf(s), x, G.tree_steps_with(tree, pred, grammar, start, input, s, hc, root, rr, ad), m)

def state_pick(b: Bool, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>,
  +s: Gll.GState, +set: +List<Core.Bsr>,
  +cn: {Prefer.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  +eb: {b == Bool.and(Check.closedWith(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))) : Bool},
  +e: {Check.checkPick(b, s) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match b:
    case True{}:
      +pred = {Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)} : Gll.Pred}
      +both = Equal.sym(Bool, True{}, Bool.and(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))), eb)
      +hc = Lemma.and_true_left(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +root = Lemma.and_true_right_side(Check.closedWith(pred, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s)), both)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{Check.stepsOf(s)}, Some{set}, e)
      tree => x => pt => m => from_tree(grammar, start, input, firsts, follows, nulls, s, set, cn, cf, cfo, cs, cr, hc, root, es, tree, x, pt, m)
    case False{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

def run_pick(r: Gll.GRun, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +set: +List<Core.Bsr>,
  +cn: {Prefer.nullsClosed(grammar, nulls) == True{} : Bool},
  +cf: {T.firstsClosed(grammar, firsts, nulls) == True{} : Bool},
  +cfo: {T.followsClosed(grammar, firsts, follows, nulls) == True{} : Bool},
  +cs: {T.followHas(start, None{}, follows) == True{} : Bool},
  +cr: {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) == True{} : Bool},
  +e: {Check.runCheckedWith(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, r, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match r:
    case Gll.GDone{+s}:
      state_pick(Bool.and(Check.closedWith(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, s), Gll.keyIn(Gll.CKey{start, 0n}, Check.clustersOf(s))),
        grammar, start, input, firsts, follows, nulls, s, set, cn, cf, cfo, cs, cr, {==}, e)
    case Gll.OutOfFuel{+s}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

def tables_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +set: +List<Core.Bsr>,
  +eb: {b == Pr.tablesClosed(grammar, start, nulls, firsts, follows) : Bool},
  +e: {Pr.predictPick(b, fuel, grammar, start, input, Pr.predictSets(grammar, firsts, follows, nulls)) == Some{set} : Maybe<&2, +List<Core.Bsr>>}) -> Core.EveryParseStep(grammar, start, input, set):
  match b:
    case True{}:
      +ok = Equal.sym(Bool, True{}, Pr.tablesClosed(grammar, start, nulls, firsts, follows), eb)
      +a1 = {Prefer.nullsClosed(grammar, nulls) : Bool}
      +a2 = {T.firstsClosed(grammar, firsts, nulls) : Bool}
      +a3 = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
      +a4 = {T.followHas(start, None{}, follows) : Bool}
      +a5 = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
      +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, a5))), ok)
      +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, a5)), r1)
      +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, a5), r2)
      +sets = Pr.predictSets(grammar, firsts, follows, nulls)
      run_pick(Gll.parseWith(fuel, Gll.Allowed{sets}, grammar, start, input), grammar, start, input, firsts, follows, nulls, set,
        Lemma.and_true_left(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, a5))), ok),
        Lemma.and_true_left(a2, Bool.and(a3, Bool.and(a4, a5)), r1),
        Lemma.and_true_left(a3, Bool.and(a4, a5), r2),
        Lemma.and_true_left(a4, a5, r3),
        Lemma.and_true_right_side(a4, a5, r3), e)
    case False{}:
      Empty.absurd(Core.EveryParseStep(grammar, start, input, set), G.none_not_some(set, e))

# THE PREDICTING PARSER MISSES NOTHING: whenever it hands out a set of steps, every step of
# every parse tree of the input is in it. Prediction never removes a step of a parse tree.
law predict_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Pr.predictedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  Core.EveryParseStep(grammar, start, input, set)

def predict_every_parse_step(fuel, grammar, start, input, set, got):
  +f = fuel
  +nulls = Prefer.growNulls(f, grammar, [])
  +firsts = T.growFirsts(f, grammar, nulls, [])
  +follows = T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}])
  tables_pick(Pr.tablesClosed(grammar, start, nulls, firsts, follows), f, grammar, start, input, nulls, firsts, follows, set, {==}, got)
