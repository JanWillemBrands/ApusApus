TB = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
'''
TBA = 'grammar, start, t, po, noConf, input, root, rootFit, rootSp'
PR = 'Gll.Predict{t}'
RHS = 'Spec.rhsOf(grammar, index)'
REST = 'Gll.dropFrom(1n+dot, %s)' % RHS
s = ('''
law keep_seed:
  for b: Bool
''' + TB + '''  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +lhs: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, q, i, g)
  for +ds: +List<Gll.Desc>
  for +bEq: {Nat.is_eq(lhs, x) == b : Bool}
  for +lhsEq: {Spec.lhsIs(grammar, n, x) == Nat.is_eq(lhs, x) : Bool}
  for +rec: AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, ds))
  AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, Gll.keepDesc(b, Gll.Desc{n, [], 0n, i, i}, ds)))

def keep_seed(b, %(tba)s, x, i, n, lhs, q, g, lhsQ, node, ds, bEq, lhsEq, rec):
  match b:
    case True{}:
      +d = {Gll.Desc{n, [], 0n, i, i} : Gll.Desc}
      on_append(PS.descWhen(%(pr)s, grammar, input, d), PS.descsWhen(%(pr)s, grammar, input, ds), grammar, input, root,
        seed_admitted(Gll.admits(%(pr)s, grammar, input, d), %(tba)s, x, i, n, Equal.trans(Bool, Spec.lhsIs(grammar, n, x), Nat.is_eq(lhs, x), True{}, lhsEq, bEq), q, g, lhsQ, node, {==}), rec)
    case False{}:
      rec

# The seeds of a cluster on the tree are on it (counting productions from n).
law seeds_on:
  for prods: +List<Spec.Production>
  for +n: Nat
''' + TB + '''  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, q, i, g)
  for +sub: {dropProds(n, grammar) == prods : +List<Spec.Production>}
  AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, Gll.productionsOf(prods, x, n, i)))

def seeds_on(prods, n, %(tba)s, x, i, q, g, lhsQ, node, sub):
  match prods:
    case Nil{}:
      {==}
    case Con{Spec.Production{+lhs, +rhs}, +rest}:
      +rec = seeds_on(rest, 1n+n, %(tba)s, x, i, q, g, lhsQ, node, drop_next(grammar, n, Spec.Production{lhs, rhs}, rest, sub))
      keep_seed(Nat.is_eq(lhs, x), %(tba)s, x, i, n, lhs, q, g, lhsQ, node, Gll.productionsOf(rest, x, 1n+n, i), {==}, drop_lhs(grammar, n, lhs, rhs, rest, x, sub), rec)
''') % {'pr': PR, 'tba': TBA}

# ---- resume ----
s += '''\nlaw U_and_right:\n  for -A: Data\n  for -B: Data\n  for +p: And(A, B)\n  B\n\ndef U_and_right(A, B, p):\n  match p:\n    case (a, b):\n      b\n'''

TREES = [('Nil', 'Nil{}', '[]'), ('Leaf', 'Con{Spec.Leaf{+a}, +ts}', 'Spec.Leaf{a} <> ts'), ('Node', 'Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
         ('Pick', 'Con{Spec.Pick{+a, +ch}, +ts}', 'Spec.Pick{a, ch} <> ts'), ('Skip', 'Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'), ('Loop', 'Con{Spec.Loop{+rs}, +ts}', 'Spec.Loop{rs} <> ts')]
IT = 'Spec.Sym{Spec.Nonterminal{y}}'
GOAL = 'AllOn(grammar, input, root, PS.pairWhen(%s, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end)))' % PR
s += '''
# A caller on the tree, resumed at a pop of its node: the node ends there, so the
# resumed descriptor and its step are on the tree.
law resume_f:
  for f: +List<Spec.Tree>
''' + TB + '''  for +y: Nat
  for +i: Nat
  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +end: Nat
  for +x: Nat
  for +g: +List<Spec.Tree>
  for +lhs: {Spec.lhsIs(grammar, index, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, index, k, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, %(rhs)s)) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +itEq: {Gll.nthItem(%(rhs)s, dot) == Some{%(it)s} : Maybe<&2, Spec.Item>}
  for +pop: NtEnds(grammar, input, root, y, i, end)
  %(goal)s

def resume_f(f, %(tba)s, y, i, index, dot, k, end, x, g, lhs, node, fitF, spF, inF, finF, itEq, pop):
  match f:
''' % {'rhs': RHS, 'it': IT, 'goal': GOAL, 'tba': TBA}
for tk, tpat, texpr in TREES:
    s += '    case %s:\n' % tpat
    ind = ''
    if tk == 'Node':
        s += '      match pop:\n        case (q2, (g2, (lhs2, (node2, ends2)))):\n'
        ind = '    '
    s += ind + '      +dEq = nth_drop(%s, dot, %s, itEq)\n' % (RHS, IT)
    s += ind + '''      +fitF2 = Equal.trans(Bool, Spec.fits(%(f)s, grammar, %(it)s <> %(rest)s), Spec.fits(%(f)s, grammar, Gll.dropFrom(dot, %(rhs)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(f)s, grammar, v), %(it)s <> %(rest)s, Gll.dropFrom(dot, %(rhs)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(rhs)s), %(it)s <> %(rest)s, dEq)), fitF)
''' % {'f': texpr, 'it': IT, 'rest': REST, 'rhs': RHS}
    if ind:
        s = s.replace('\n        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node', '\n            Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node')
    if tk != 'Node':
        s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % GOAL
        continue
    s += '''          +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
          +lch = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +e = Nat.add(i, List.length(&2, Nat, lch))
          +spCh = G.spells_first(input, i, lch, lts, spF)
          +spT = G.spells_second(input, i, lch, lts, spF)
          +here = Spec.at(index, [], 1n+dot, k, i, e)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
          +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, e)
          +inA = all_in_tail_n(here, List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF)
          +inCh = all_in_left_n(wCh, wT, Spec.steps(root, 0n), inA)
          +inT = all_in_right_n(wCh, wT, Spec.steps(root, 0n), inA)
          +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n)), inF)
          +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), G.end_split(i, lch, lts), finF)
          +same = nodes_same(%(tba)s, y, i, q, q2, ch, g2, lhsQ, lhs2, (fitCh, (spCh, inCh)), node2)
          +ge = U_and_right({q == q2 : Nat}, {ch == g2 : +List<Spec.Tree>}, same)
          +eEnd = Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g2))), end, Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g2, ge), ends2)
          %%eEnd : AllOn(grammar, input, root, PS.pairWhen(%(pr)s, grammar, input, Gll.Desc{index, [], 1n+dot, k, _}, Gll.stepAt(index, [], 1n+dot, k, i, _)))
          on_when(Gll.admits(%(pr)s, grammar, input, Gll.Desc{index, [], 1n+dot, k, e}), [Support.FactDescriptor{Gll.Desc{index, [], 1n+dot, k, e}}, Support.FactStep{Gll.stepAt(index, [], 1n+dot, k, i, e)}], grammar, input, root,
            ((x, (g, (ts, (lhs, (node, (fitT, (spT, (inT, finT)))))))), (onS, {==})))
''' % {'rest': REST, 'tba': TBA, 'pr': PR}

s += '''
law resume_on:
  for key: Gll.CKey
  for edge: Gll.Edge
''' + TB + '''  for +end: Nat
  for +here: returnOn(grammar, input, root, key, edge)
  for +pop: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, PS.resumeGives(%(pr)s, grammar, input, key, edge, end))

def resume_on(key, edge, %(tba)s, end, here, pop):
  match key edge:
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, Nil{}, +dot, +k}:
      match here:
        case (d, itEq):
          match d:
            case (x, (g, (f, (lhs, (node, (fitF, (spF, (inF, finF)))))))):
              resume_f(f, %(tba)s, y, i, index, dot, k, end, x, g, lhs, node, fitF, spF, inF, finF, itEq, pop)
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, Con{+a, +r}, +dot, +k}:
      match here:
        case (d, itEq):
          Empty.absurd(AllOn(grammar, input, root, PS.resumeGives(%(pr)s, grammar, input, Gll.CKey{Gll.TNt{y}, i}, Gll.Edge{index, a <> r, dot, k}, end)), Lemma.false_is_not_true(d))
    case Gll.CKey{Gll.TBr{+index, +rpath}, +i} +e:
      Empty.absurd(AllOn(grammar, input, root, PS.resumeGives(%(pr)s, grammar, input, Gll.CKey{Gll.TBr{index, rpath}, i}, e, end)), Lemma.false_is_not_true(here))
''' % {'pr': PR, 'tba': TBA}
open('n6.bend', 'w').write(s)
