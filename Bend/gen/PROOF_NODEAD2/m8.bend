
# ======== A CLUSTER OF A NONTERMINAL ON THE TREE ========

law seed_node:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{q, [], 0n, i, i}}])

def seed_node(grammar, input, root, x, i, q, g, lhsQ, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +sp = {sp0 : G.Spells(g, input, i)}
      +inG = {in0 : {Spec.allIn(Spec.walk(g, False{}, q, [], 0n, i, i), Spec.steps(root, 0n)) == True{} : Bool}}
      ((i, (g, (g, (({==}, (x, (lhsQ, (fit, (sp, inG))))), (fit, (sp, (inG, {==}))))))), {==})

# The tree's own production, started at its node.
law seed_tree:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +q: Nat
  for +nq: {n == q : Nat}
  for +g: +List<Spec.Tree>
  for +lhsN: {Spec.lhsIs(grammar, n, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}])

def seed_tree(grammar, input, root, x, i, n, q, nq, g, lhsN, node):
  +qn = Equal.sym(Nat, n, q, nq)
  %qn : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{_, [], 0n, i, i}}])
  seed_node(grammar, input, root, x, i, q, g, Equal.trans(Bool, Spec.lhsIs(grammar, q, x), Spec.lhsIs(grammar, n, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, v, x), q, n, qn), lhsN), node)

law seed_admitted:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +lhsN: {Spec.lhsIs(grammar, n, x) == True{} : Bool}
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{n, [], 0n, i, i}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]))

def seed_admitted(b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhsN, q, g, lhsQ, node, bEq):
  match b:
    case False{}:
      {==}
    case True{}:
      +next = List.get(&2, Nat, input, i)
      L.either_case({n == q : Nat}, {Nat.is_eq(n, q) == False{} : Bool}, AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]), U.decide(Nat.is_eq(n, q), n, q, {==}),
        +nq => seed_tree(grammar, input, root, x, i, n, q, nq, g, lhsN, node),
        neq => Empty.absurd(AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]),
          Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{},
            Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{},
              L.nonterminal_hits(grammar, t, x, n, q, next, neq, (lhsN, bEq),
                (lhsQ, L.predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, N1.node_predicts(grammar, start, input, root, rootFit, rootSp, i, q, g, node))))), noConf))))

law keep_seed:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +lhs: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +ds: +List<Gll.Desc>
  for +bEq: {Nat.is_eq(lhs, x) == b : Bool}
  for +lhsEq: {Spec.lhsIs(grammar, n, x) == Nat.is_eq(lhs, x) : Bool}
  for +rec: AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, ds))
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.keepDesc(b, Gll.Desc{n, [], 0n, i, i}, ds)))

def keep_seed(b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhs, q, g, lhsQ, node, ds, bEq, lhsEq, rec):
  match b:
    case True{}:
      +d = {Gll.Desc{n, [], 0n, i, i} : Gll.Desc}
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, d), PS.descsWhen(Gll.Predict{t}, grammar, input, ds), grammar, input, root,
        seed_admitted(Gll.admits(Gll.Predict{t}, grammar, input, d), grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, Equal.trans(Bool, Spec.lhsIs(grammar, n, x), Nat.is_eq(lhs, x), True{}, lhsEq, bEq), q, g, lhsQ, node, {==}), rec)
    case False{}:
      rec

# The seeds of a cluster on the tree are on it (counting productions from n).
law seeds_on:
  for prods: +List<Spec.Production>
  for +n: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +sub: {N1.dropProds(n, grammar) == prods : +List<Spec.Production>}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.productionsOf(prods, x, n, i)))

def seeds_on(prods, n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, sub):
  match prods:
    case Nil{}:
      {==}
    case Con{Spec.Production{+lhs, +rhs}, +rest}:
      +rec = seeds_on(rest, 1n+n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, N1.drop_next(grammar, n, Spec.Production{lhs, rhs}, rest, sub))
      keep_seed(Nat.is_eq(lhs, x), grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhs, q, g, lhsQ, node, Gll.productionsOf(rest, x, 1n+n, i), {==}, N1.drop_lhs(grammar, n, lhs, rhs, rest, x, sub), rec)


# ======== A CLUSTER OF A BRACKET ON THE TREE ========

law lt_up:
  for a: Nat
  for n: Nat
  for +h: {Nat.is_lt(a, n) == True{} : Bool}
  {Nat.is_lt(a, 1n+n) == True{} : Bool}

def lt_up(a, n, h):
  match a n:
    case 0n _:
      {==}
    case 1n+b 0n:
      Empty.absurd({Nat.is_lt(1n+b, 1n) == True{} : Bool}, Lemma.lt_zero_false(1n+b, h))
    case 1n+(+b) 1n+(+c):
      lt_up(b, c, h)

law seed_any:
  for kind: Spec.Bracket
  for ff: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}))

def seed_any(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA):
  match kind:
    case Spec.Group{}:
      seed_group(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Optional{}:
      seed_optional(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Closure{}:
      seed_closure(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Positive{}:
      seed_positive(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})

law alts_seed_on:
  for n: Nat
  for +kind: Spec.Bracket
  for +ff: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +hn: {Nat.is_lt(n, 1n+List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(n, index, m <> outer, k, k)))

def alts_seed_on(n, kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, hn):
  match n:
    case 0n:
      {==}
    case 1n+(+a):
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(a, index, m <> outer, k, k)), grammar, input, root,
        seed_any(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, hn),
        alts_seed_on(a, kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, lt_up(a, List.length(&2, +List<Spec.Item>, alts), hn)))

# The seeds of a bracket's cluster on the tree are on it.
law bracket_seeds_on:
  for rp: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +k: Nat
  for +here: clusterOn(grammar, input, root, Gll.CKey{Gll.TBr{index, rp}, k})
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Check.seedsOf(grammar, Gll.CKey{Gll.TBr{index, rp}, k})))

def bracket_seeds_on(rp, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, k, here):
  match rp:
    case Nil{}:
      Empty.absurd(AllOn(grammar, input, root, []), Lemma.false_is_not_true(here))
    case Con{+m, +outer}:
      match here:
        case (kc, (kind, (alts, ((p1, (g1, (ff, (occO, (fitF, (spF, (inF, finF))))))), itEqB)))):
          +itBS = Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itEqB)
          %itBS : AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(Check.altCount(_), index, m <> outer, k, k)))
          alts_seed_on(List.length(&2, +List<Spec.Item>, alts), kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, L.lt_succ_self(List.length(&2, +List<Spec.Item>, alts)))
