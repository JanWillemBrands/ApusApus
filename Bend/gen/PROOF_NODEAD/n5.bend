
# ======== A CLUSTER ON THE TREE STARTS ONLY THE TREE'S PRODUCTION ========

def dropProds(n: Nat, grammar: +List<Spec.Production>) -> +List<Spec.Production>:
  match n grammar:
    case 0n _:
      grammar
    case 1n+m Nil{}:
      []
    case 1n+m Con{p, rest}:
      dropProds(m, rest)

def lhsHead(ps: +List<Spec.Production>) -> Nat:
  match ps:
    case Con{Spec.Production{lhs, rhs}, rest}:
      lhs
    case Nil{}:
      0n

def prodsTail(ps: +List<Spec.Production>) -> +List<Spec.Production>:
  match ps:
    case Con{p, rest}:
      rest
    case Nil{}:
      []

def prodsEmpty(ps: +List<Spec.Production>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      False{}

law drop_lhs:
  for grammar: +List<Spec.Production>
  for n: Nat
  for +lhs: Nat
  for +rhs: +List<Spec.Item>
  for +rest: +List<Spec.Production>
  for +y: Nat
  for +e: {dropProds(n, grammar) == Spec.Production{lhs, rhs} <> rest : +List<Spec.Production>}
  {Spec.lhsIs(grammar, n, y) == Nat.is_eq(lhs, y) : Bool}

def drop_lhs(grammar, n, lhs, rhs, rest, y, e):
  match grammar n:
    case Nil{} 0n:
      Empty.absurd({False{} == Nat.is_eq(lhs, y) : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], Spec.Production{lhs, rhs} <> rest, e)))
    case Nil{} 1n+m:
      Empty.absurd({False{} == Nat.is_eq(lhs, y) : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], Spec.Production{lhs, rhs} <> rest, e)))
    case Con{Spec.Production{+l2, +r2}, +rest2} 0n:
      Equal.cong(Nat, Bool, v => Nat.is_eq(v, y), l2, lhs, Equal.cong(+List<Spec.Production>, Nat, v => lhsHead(v), Spec.Production{l2, r2} <> rest2, Spec.Production{lhs, rhs} <> rest, e))
    case Con{p, +rest2} 1n+(+m):
      drop_lhs(rest2, m, lhs, rhs, rest, y, e)

law drop_next:
  for grammar: +List<Spec.Production>
  for n: Nat
  for +p: Spec.Production
  for +rest: +List<Spec.Production>
  for +e: {dropProds(n, grammar) == p <> rest : +List<Spec.Production>}
  {dropProds(1n+n, grammar) == rest : +List<Spec.Production>}

def drop_next(grammar, n, p, rest, e):
  match grammar n:
    case Nil{} 0n:
      Empty.absurd({[] == rest : +List<Spec.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], p <> rest, e)))
    case Nil{} 1n+m:
      Empty.absurd({[] == rest : +List<Spec.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], p <> rest, e)))
    case Con{+p2, +rest2} 0n:
      Equal.cong(+List<Spec.Production>, +List<Spec.Production>, v => prodsTail(v), p2 <> rest2, p <> rest, e)
    case Con{p2, +rest2} 1n+(+m):
      drop_next(rest2, m, p, rest, e)

law seed_node:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{q, [], 0n, i, i}}])

def seed_node(grammar, input, root, x, i, q, g, lhsQ, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +sp = {sp0 : G.Spells(g, input, i)}
      +inG = {in0 : {Spec.allIn(Spec.walk(g, False{}, q, [], 0n, i, i), Spec.steps(root, 0n)) == True{} : Bool}}
      ((x, (g, (g, (lhsQ, ((fit, (sp, inG)), (fit, (sp, (inG, {==})))))))), {==})

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
  for +node: NodeAt(grammar, input, root, q, i, g)
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
  for +node: NodeAt(grammar, input, root, q, i, g)
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
                (lhsQ, L.predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, node_predicts(grammar, start, input, root, rootFit, rootSp, i, q, g, node))))), noConf))))
