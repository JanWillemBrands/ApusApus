exec(open('m5.py').read().split('out = []')[0])
out = []
GOALI = 'AllOn(grammar, input, root, PS.itemGives(IT, %s, grammar, input, index, rpath, dot, k, i))' % PR
# ---- end of a sequence ----
s = '''
law end_on:
  for rpath: +List<Nat>
''' + TB + '''  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, 0n) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  AllOn(grammar, input, root, PS.itemGives(None{}, %(pr)s, grammar, input, index, rpath, dot, k, i))

def end_on(rpath, %(tba)s, index, dot, k, i, p0, g, occ, inF, finF):
  match rpath:
    case Nil{}:
      match occ:
        case (pk, (x, (lhs, node))):
          +lhsIdx = Equal.trans(Bool, Spec.lhsIs(grammar, index, Gll.lhsOf(grammar, index)), Spec.lhsIs(grammar, index, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, index, v), Gll.lhsOf(grammar, index), x, G.lhs_of_is(grammar, index, x, lhs)), lhs)
          +endP = Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
          +endK = Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), i, Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves(g))), k, p0, Equal.sym(Nat, p0, k, pk)), endP)
          ((index, (g, (lhsIdx, (node, endK)))), empty_on(dot, %(tba)s, index, [], k, i, inF))
    case Con{+a, Nil{}}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, %(pr)s, grammar, input, index, [a], dot, k, i)), Lemma.false_is_not_true(occ))
    case Con{+a, Con{+m, +outer}}:
      +endP = Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
      ((a, (p0, (g, (occ, endP)))), empty_on(dot, %(tba)s, index, a <> (m <> outer), k, i, inF))
''' % {'pr': PR, 'tba': TBA}
s = '''
law empty_on:
  for dot: Nat
''' + TB + '''  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  AllOn(grammar, input, root, Support.emptyStep(dot, index, rpath, k, i))

def empty_on(dot, %(tba)s, index, rpath, k, i, inF):
  match dot:
    case 0n:
      +onAt = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefixOf(rpath), 0n, k, i, i), Spec.steps(root, 0n)), True{}, inF)
      (%(st)s, {==})
    case 1n+d:
      {==}
''' % {'tba': TBA, 'st': on_step('0n', 'i', 'onAt')} + s
out.append(s)

# ---- the item at the dot ----
ITEMS = [('T', 'Some{Spec.Sym{Spec.Terminal{+tm}}}', 'Spec.Sym{Spec.Terminal{tm}}'), ('N', 'Some{Spec.Sym{Spec.Nonterminal{+y}}}', 'Spec.Sym{Spec.Nonterminal{y}}'),
         ('E', 'Some{Spec.Eps{}}', 'Spec.Eps{}'), ('BG', 'Some{Spec.Brack{Spec.Group{}, +alts}}', 'Spec.Brack{Spec.Group{}, alts}'), ('BO', 'Some{Spec.Brack{Spec.Optional{}, +alts}}', 'Spec.Brack{Spec.Optional{}, alts}'),
         ('BC', 'Some{Spec.Brack{Spec.Closure{}, +alts}}', 'Spec.Brack{Spec.Closure{}, alts}'), ('BP', 'Some{Spec.Brack{Spec.Positive{}, +alts}}', 'Spec.Brack{Spec.Positive{}, alts}'), ('Z', 'None{}', None)]
TREES = [('Nil', 'Nil{}', '[]'), ('Leaf', 'Con{Spec.Leaf{+a}, +ts}', 'Spec.Leaf{a} <> ts'), ('Node', 'Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
         ('Pick', 'Con{Spec.Pick{+a, +ch}, +ts}', 'Spec.Pick{a, ch} <> ts'), ('Skip', 'Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'), ('Loop', 'Con{Spec.Loop{+rs}, +ts}', 'Spec.Loop{rs} <> ts')]
s = '''
law item_on:
  for it: Maybe<&2, Spec.Item>
  for f: +List<Spec.Tree>
''' + TB + SEQD.replace('FOREST', 'f') + '''  for +itEq: {Gll.nthItem(%(seq)s, dot) == it : Maybe<&2, Spec.Item>}
  AllOn(grammar, input, root, PS.itemGives(it, %(pr)s, grammar, input, index, rpath, dot, k, i))

def item_on(it, f, %(tba)s, %(seqa)s, itEq):
  match it f:
''' % {'seq': SEQ, 'pr': PR, 'tba': TBA, 'seqa': SEQA}
for ik, ipat, iexpr in ITEMS:
    itx = 'Some{%s}' % iexpr if iexpr else 'None{}'
    goal = GOALI.replace('IT', itx)
    for tk, tpat, texpr in TREES:
        s += '    case %s %s:\n' % (ipat, tpat)
        if ik == 'Z':
            if tk == 'Nil':
                s += '      end_on(rpath, %s, index, dot, k, i, p0, g, occ, inF, finF)\n' % TBA
            else:
                s += '''      +dNil = N1.nth_none_drop(%(seq)s, dot, itEq)
      Empty.absurd(%(goal)s, Fits.fits_cons_nil(%(head)s, ts, grammar, Equal.trans(Bool, Spec.fits(%(f)s, grammar, []), Spec.fits(%(f)s, grammar, Gll.dropFrom(dot, %(seq)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(f)s, grammar, v), [], Gll.dropFrom(dot, %(seq)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(seq)s), [], dNil)), fitF)))
''' % {'seq': SEQ, 'goal': goal, 'head': texpr.split(' <> ')[0], 'f': texpr}
            continue
        if ik.startswith('B'):
            kind = iexpr.split(',')[0][len('Spec.Brack{'):]
            descT = desc('f', 'fitF', 'spF', 'inF', 'finF')
            cr = '(k, (%s, (alts, (%s, itEq))))' % (kind, descT)
            rt = '(%s, (alts, (%s, ({==}, ({==}, itEq)))))' % (kind, descT)
            if ik in ('BG', 'BP'):
                s += '      (%s, (%s, {==}))\n' % (cr, rt)
            else:
                kn = 'optional' if ik == 'BO' else 'closure'
                s += '      (%s, (%s, skip_%s(f, Gll.admits(%s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), %s, %s, alts, itEq, {==})))\n' % (cr, rt, kn, PR, TBA, SEQA)
            continue
        s += fit_moved(iexpr, texpr)
        real = {('T', 'Leaf'), ('N', 'Node'), ('E', 'Skip')}
        if (ik, tk) not in real:
            s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % goal
            continue
        if ik == 'T':
            d1 = 'Gll.Desc{index, rpath, 1n+dot, k, 1n+i}'; y1 = 'Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)'
            s += '''      +fitT = Fits.fits_tail(Spec.Leaf{a}, ts, grammar, %(it)s, %(rest)s, fitF2)
      +lts = List.length(&2, Nat, Spec.leaves(ts))
      +spT = G.leaf_rest(input, i, a, Spec.leaves(ts), spF)
      +here = Spec.at(index, %(p)s, 1n+dot, k, i, 1n+i)
      +wT = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, 1n+i)
      +inT = N1.all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, 1n+Nat.add(i, lts), Nat.add(i, 1n+lts), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Equal.sym(Nat, Nat.add(i, 1n+lts), 1n+Nat.add(i, lts), Lemma.add_succ_right(i, lts)), finF)
      U2_on_when(Gll.tokenIs(List.get(&2, Nat, input, i), tm), PS.pairWhen(%(pr)s, grammar, input, %(d)s, %(y)s), grammar, input, root,
        U2_on_when(Gll.admits(%(pr)s, grammar, input, %(d)s), [Support.FactDescriptor{%(d)s}, Support.FactStep{%(y)s}], grammar, input, root, (%(da)s, (%(st)s, {==}))))
''' % {'it': iexpr, 'rest': REST, 'p': P, 'pr': PR, 'd': d1, 'y': y1, 'da': desc('ts', 'fitT', 'spT', 'inT', 'finT'), 'st': on_step('1n+dot', '1n+i', 'onAt')}
        elif ik == 'E':
            d1 = 'Gll.Desc{index, rpath, 1n+dot, k, i}'; y1 = 'Gll.stepAt(index, rpath, 1n+dot, k, i, i)'
            s += '''      +here = Spec.at(index, %(p)s, 1n+dot, k, i, i)
      +wT = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, i)
      +inT = N1.all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      U2_on_when(Gll.admits(%(pr)s, grammar, input, %(d)s), [Support.FactDescriptor{%(d)s}, Support.FactStep{%(y)s}], grammar, input, root, (%(da)s, (%(st)s, {==})))
''' % {'p': P, 'pr': PR, 'd': d1, 'y': y1, 'da': desc('ts', 'fitF2', 'spF', 'inT', 'finF'), 'st': on_step('1n+dot', 'i', 'onAt')}
        elif ik == 'N':
            s += '''      +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +lch = Spec.leaves(ch)
      +e = Nat.add(i, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, i, lch, Spec.leaves(ts), spF)
      +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, e)
      +inCh = N1.all_in_left_n(wCh, wT, Spec.steps(root, 0n), N1.all_in_tail_n(Spec.at(index, %(p)s, 1n+dot, k, i, e), List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF))
      ((q, (ch, (lhsQ, (fitCh, (spCh, inCh))))), ((%(da)s, itEq), {==}))
''' % {'rest': REST, 'p': P, 'da': desc(texpr, 'fitF', 'spF', 'inF', 'finF')}
out.append(s)
src = ''.join(out)
src = src.replace('U2_on_when(', 'on_when(')
open('m6.bend', 'w').write(src)
