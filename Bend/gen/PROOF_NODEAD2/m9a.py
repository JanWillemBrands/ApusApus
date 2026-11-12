exec(open('m5.py').read().split('out = []')[0])
IT = 'Spec.Sym{Spec.Nonterminal{y}}'
GOAL = 'AllOn(grammar, input, root, PS.pairWhen(%s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end)))' % PR
TREES = [('Nil{}', '[]'), ('Con{Spec.Leaf{+a}, +ts}', 'Spec.Leaf{a} <> ts'), ('Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
         ('Con{Spec.Pick{+a, +ch}, +ts}', 'Spec.Pick{a, ch} <> ts'), ('Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'), ('Con{Spec.Loop{+rs}, +ts}', 'Spec.Loop{rs} <> ts')]
s = '''
# ======== RESUMING A CALLER ON THE TREE ========

# At a pop of a nonterminal's node: the caller's node ends there, so the resumed descriptor
# and its step are on the tree.
law resume_nt:
  for f: +List<Spec.Tree>
''' + TB + SEQD.replace('FOREST', 'f') + '''  for +y: Nat
  for +end: Nat
  for +itEq: {Gll.nthItem(%(seq)s, dot) == Some{%(it)s} : Maybe<&2, Spec.Item>}
  for +pop: N1.NtEnds(grammar, input, root, y, i, end)
  %(goal)s

def resume_nt(f, %(tba)s, %(seqa)s, y, end, itEq, pop):
  match f:
''' % {'seq': SEQ, 'it': IT, 'goal': GOAL, 'tba': TBA, 'seqa': SEQA}
for tpat, texpr in TREES:
    s += '    case %s:\n' % tpat
    node = tpat.startswith('Con{Spec.Node')
    ind = '    ' if node else ''
    if node:
        s += '      match pop:\n        case (q2, (g2, (lhs2, (node2, ends2)))):\n'
    s += '\n'.join(ind + l if l else l for l in fit_moved(IT, texpr).rstrip('\n').split('\n')) + '\n'
    if not node:
        s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % GOAL
        continue
    body = '''      +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
      +lch = Spec.leaves(ch)
      +lts = Spec.leaves(ts)
      +e = Nat.add(i, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, i, lch, lts, spF)
      +spT = G.spells_second(input, i, lch, lts, spF)
      +here = Spec.at(index, %(p)s, 1n+dot, k, i, e)
      +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, e)
      +inA = N1.all_in_tail_n(here, List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF)
      +inCh = N1.all_in_left_n(wCh, wT, Spec.steps(root, 0n), inA)
      +inT = N1.all_in_right_n(wCh, wT, Spec.steps(root, 0n), inA)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), G.end_split(i, lch, lts), finF)
      +same = N1.nodes_same(%(tba)s, y, i, q, q2, ch, g2, lhsQ, lhs2, (fitCh, (spCh, inCh)), node2)
      +ge = N1.U_and_right({q == q2 : Nat}, {ch == g2 : +List<Spec.Tree>}, same)
      +eEnd = Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g2))), end, Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g2, ge), ends2)
      %%eEnd : AllOn(grammar, input, root, PS.pairWhen(%(pr)s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, _}, Gll.stepAt(index, rpath, 1n+dot, k, i, _)))
      on_when(Gll.admits(%(pr)s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, e}), [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, e}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, e)}], grammar, input, root,
        (%(desc)s, (%(st)s, {==})))
''' % {'rest': REST, 'p': P, 'tba': TBA, 'pr': PR, 'desc': desc('ts', 'fitT', 'spT', 'inT', 'finT'), 'st': on_step('1n+dot', 'e', 'onAt')}
    s += '\n'.join(ind + l if l else l for l in body.rstrip('\n').split('\n')) + '\n'
open('m9a.bend', 'w').write(s)
