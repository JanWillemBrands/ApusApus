
# ======== THE TABLE CHECK RULES OUT CLASHES ========

law clash_empty:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for c: U.Clash(grammar, start)
  Empty

def clash_empty(grammar, start, t, po, noConf, c):
  match c:
    case (point, (first, (second, (next, (neq, (cp1, cp2)))))):
      +none = List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t))
      Lemma.false_is_not_true(Equal.trans(Bool, False{}, none, True{}, Equal.sym(Bool, none, False{}, L.ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2)), noConf))

law same_or_clash:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for -g1: +List<Spec.Tree>
  for -g2: +List<Spec.Tree>
  for r: U.Same(grammar, start, g1, g2)
  {g1 == g2 : +List<Spec.Tree>}

def same_or_clash(grammar, start, t, po, noConf, g1, g2, r):
  match r:
    case Inl{e}:
      e
    case Inr{c}:
      Empty.absurd({g1 == g2 : +List<Spec.Tree>}, clash_empty(grammar, start, t, po, noConf, c))

# ======== TWO NODES OF ONE NONTERMINAL AT ONE POSITION ARE THE SAME ========

law nodes_same_eq:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +k: Nat
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +g1: +List<Spec.Tree>
  for +g2: +List<Spec.Tree>
  for +n1: NodeAt(grammar, input, root, q1, k, g1)
  for +n2: NodeAt(grammar, input, root, q2, k, g2)
  {g1 == g2 : +List<Spec.Tree>}

def nodes_same_eq(grammar, start, t, po, noConf, input, root, rootFit, rootSp, k, q1, q2, qe, g1, g2, n1, n2):
  match n1:
    case (fit10, (sp10, in10)):
      match n2:
        case (fit20, (sp20, in20)):
          +fit1 = {fit10 : {Spec.fits(g1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}}
          +sp1 = {sp10 : G.Spells(g1, input, k)}
          +in1 = {in10 : {Spec.allIn(Spec.walk(g1, False{}, q1, [], 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fit2 = {fit20 : {Spec.fits(g2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}}
          +sp2 = {sp20 : G.Spells(g2, input, k)}
          +in2 = {in20 : {Spec.allIn(Spec.walk(g2, False{}, q2, [], 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fit2b = Equal.trans(Bool, Spec.fits(g2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(g2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(g2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fit2)
          +in2b = Equal.trans(Bool, Spec.allIn(Spec.walk(g2, False{}, q1, [], 0n, k, k), Spec.steps(root, 0n)), Spec.allIn(Spec.walk(g2, False{}, q2, [], 0n, k, k), Spec.steps(root, 0n)), True{},
            Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(g2, False{}, v, [], 0n, k, k), Spec.steps(root, 0n)), q1, q2, qe), in2)
          same_or_clash(grammar, start, t, po, noConf, g1, g2,
            U.compare(g1, False{}, g2, Spec.rhsOf(grammar, q1), grammar, start, input, root, rootFit, rootSp, root, rootFit, rootSp, q1, [], 0n, k, k, k, Spec.Group{}, [], [], False{}, 0n, 0n,
              (fit1, (fit2b, (sp1, (sp2, (in1, (in2b, ({==}, {==})))))))))

# PREDICT of a node's production, at its position.
law node_predicts:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +k: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +node: NodeAt(grammar, input, root, q, k, g)
  Spec.Predicts(grammar, start, Spec.rhsOf(grammar, q), q, [], List.get(&2, Nat, input, k))

def node_predicts(grammar, start, input, root, rootFit, rootSp, k, q, g, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(g)))
      U.predicts_in(List.get(&2, Nat, input, k), grammar, start, input, root, rootFit, rootSp, g, Spec.rhsOf(grammar, q), q, [], [], k, k, e, Spec.walk(g, False{}, q, [], 0n, k, k), fit, sp0, {==}, {==}, {==},
        U.end_walk(g, Spec.rhsOf(grammar, q), 0n, grammar, q, [], k, k, e, fit, {==}, {==}, {==}), in0)

law nodes_same:
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
  for +k: Nat
  for +q1: Nat
  for +q2: Nat
  for +g1: +List<Spec.Tree>
  for +g2: +List<Spec.Tree>
  for +lhs1: {Spec.lhsIs(grammar, q1, x) == True{} : Bool}
  for +lhs2: {Spec.lhsIs(grammar, q2, x) == True{} : Bool}
  for +n1: NodeAt(grammar, input, root, q1, k, g1)
  for +n2: NodeAt(grammar, input, root, q2, k, g2)
  And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>})

def nodes_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, k, q1, q2, g1, g2, lhs1, lhs2, n1, n2):
  +next = List.get(&2, Nat, input, k)
  cp1 = U.nt_cp(Spec.lhsIs(grammar, q1, x), grammar, start, q1, next, lhs1, node_predicts(grammar, start, input, root, rootFit, rootSp, k, q1, g1, n1))
  cp2 = U.nt_cp(Spec.lhsIs(grammar, q2, x), grammar, start, q2, next, lhs2, node_predicts(grammar, start, input, root, rootFit, rootSp, k, q2, g2, n2))
  L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>}), U.decide(Nat.is_eq(q1, q2), q1, q2, {==}),
    +qe => (qe, nodes_same_eq(grammar, start, t, po, noConf, input, root, rootFit, rootSp, k, q1, q2, qe, g1, g2, n1, n2)),
    neq => Empty.absurd(And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>}), clash_empty(grammar, start, t, po, noConf, (Spec.NonterminalAt{x}, (q1, (q2, (next, (neq, (cp1, cp2)))))))))
