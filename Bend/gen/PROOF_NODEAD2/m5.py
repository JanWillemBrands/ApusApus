SEQ = 'Gll.seqAt(grammar, index, rpath)'
P = 'prefixOf(rpath)'
REST = 'Gll.dropFrom(1n+dot, %s)' % SEQ
PR = 'Gll.Predict{t}'
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
SEQD = '''  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +fitF: {Spec.fits(FOREST, grammar, Gll.dropFrom(dot, %s)) == True{} : Bool}
  for +spF: G.Spells(FOREST, input, i)
  for +inF: {Spec.allIn(Spec.walk(FOREST, False{}, index, %s, dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(FOREST))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
''' % (SEQ, P)
SEQA = 'index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF'
def desc(f, fit, sp, inn, fin): return '(p0, (g, (%s, (occ, (%s, (%s, (%s, %s)))))))' % (f, fit, sp, inn, fin)
def on_step(d, j, iat):
    # bsrMember(stepAt(index, rpath, d, k, i, j)) from the membership of Spec.at
    return 'Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, %s, k, i, %s), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, %s, %s, k, i, %s), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, %s, k, i, %s), Spec.at(index, %s, %s, k, i, %s), step_at_eq(index, rpath, %s, k, i, %s)), %s)' % (d, j, P, d, j, d, j, P, d, j, d, j, iat)
def fit_moved(item, f):
    return '''      +dEq = N1.nth_drop(%(seq)s, dot, %(it)s, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(%(f)s, grammar, %(it)s <> %(rest)s), Spec.fits(%(f)s, grammar, Gll.dropFrom(dot, %(seq)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(f)s, grammar, v), %(it)s <> %(rest)s, Gll.dropFrom(dot, %(seq)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(seq)s), %(it)s <> %(rest)s, dEq)), fitF)
''' % {'seq': SEQ, 'it': item, 'f': f, 'rest': REST}
def contra(ne):
    return 'Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, %s), noConf))' % ne

out = []
# ---- skipping [ ] or { } ----
SKD = 'Gll.Desc{index, rpath, 1n+dot, k, i}'
SKY = 'Gll.stepAt(index, rpath, 1n+dot, k, i, i)'
SKGOAL = 'AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{%s}, Support.FactStep{%s}]))' % (SKD, SKY)
for kind, kname in (('Spec.Optional{}', 'optional'), ('Spec.Closure{}', 'closure')):
    IT = 'Spec.Brack{%s, alts}' % kind
    s = '''
# Skipping %(kname)s at the dot: on the tree when the tree skips it, else not admitted.
law skip_%(kname)s:
  for f: +List<Spec.Tree>
  for b: Bool
''' % {'kname': kname} + TB + SEQD.replace('FOREST', 'f') + '''  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(%(seq)s, dot) == Some{%(it)s} : Maybe<&2, Spec.Item>}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == b : Bool}
  %(goal)s

def skip_%(kname)s(f, b, %(tba)s, %(seqa)s, alts, itEq, bEq):
  match f b:
''' % {'seq': SEQ, 'it': IT, 'pr': PR, 'd': SKD, 'goal': SKGOAL, 'tba': TBA, 'seqa': SEQA, 'kname': kname}
    shapes = [('Nil{}', '[]'), ('Con{Spec.Leaf{+a}, +ts}', 'Spec.Leaf{a} <> ts'), ('Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
              ('Con{Spec.Pick{+a, +ch}, +ts}', 'Spec.Pick{a, ch} <> ts'), ('Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'),
              ('Con{Spec.Loop{Nil{}}, +ts}', 'Spec.Loop{[]} <> ts'), ('Con{Spec.Loop{Con{Spec.Pick{+a, +ch}, +r}}, +ts}', 'Spec.Loop{Spec.Pick{a, ch} <> r} <> ts'),
              ('Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts}', 'Spec.Loop{Spec.Leaf{x} <> r} <> ts'), ('Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts}', 'Spec.Loop{Spec.Node{q, ch} <> r} <> ts'),
              ('Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts}', 'Spec.Loop{Spec.Skip{} <> r} <> ts'), ('Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts}', 'Spec.Loop{Spec.Loop{rs} <> r} <> ts')]
    for bpat in ('True{}', 'False{}'):
        for spat, sexpr in shapes:
            s += '    case %s %s:\n' % (spat, bpat)
            g2 = SKGOAL.replace('Support.whenTrue(b,', 'Support.whenTrue(%s,' % bpat)
            if bpat == 'False{}':
                s += '      {==}\n'
                continue
            s += fit_moved(IT, sexpr)
            taken = (kname == 'optional' and spat.startswith('Con{Spec.Pick')) or (kname == 'closure' and 'Loop{Con{Spec.Pick' in spat)
            skipped = (kname == 'optional' and spat.startswith('Con{Spec.Skip')) or (kname == 'closure' and 'Loop{Nil' in spat)
            if skipped:
                if kname == 'optional':
                    s += '''      +inT = N1.all_in_tail_n(Spec.at(index, %(p)s, 1n+dot, k, i, i), Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, i), Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, %(p)s, 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.allIn(Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, i), Spec.steps(root, 0n)), inF)
      (%(desc)s, (%(st)s, {==}))
''' % {'p': P, 'desc': desc('ts', 'fitF2', 'spF', 'inT', 'finF'), 'st': on_step('1n+dot', 'i', 'onAt')}
                else:
                    s += '''      +i0 = Lemma.add_zero_right(i)
      +wT0 = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, Nat.add(i, 0n))
      +inA = N1.all_in_tail_n(Spec.at(index, %(p)s, 1n+dot, k, i, Nat.add(i, 0n)), List.append(&2, Spec.Bsr, [], wT0), Spec.steps(root, 0n), inF)
      +inT = Equal.trans(Bool, Spec.allIn(Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, i), Spec.steps(root, 0n)), Spec.allIn(wT0, Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, v), Spec.steps(root, 0n)), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, i0)), inA)
      +onAt0 = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, %(p)s, 1n+dot, k, i, Nat.add(i, 0n)), Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, [], wT0), Spec.steps(root, 0n)), inF)
      +onAt = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, %(p)s, 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, %(p)s, 1n+dot, k, i, Nat.add(i, 0n)), Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, %(p)s, 1n+dot, k, i, v), Spec.steps(root, 0n)), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, i0)), onAt0)
      +fitT = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, []), True{}), Spec.fits(ts, grammar, %(rest)s), fitF2)
      +spT0 = G.spells_second(input, i, [], Spec.leaves(ts), spF)
      +nT = List.length(&2, Nat, Spec.leaves(ts))
      +spT = Equal.trans(+List<Nat>, Spec.leaves(ts), Lemma.slice(input, Nat.add(i, 0n), nT), Lemma.slice(input, i, nT), spT0, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, nT), Nat.add(i, 0n), i, i0))
      +finT = Equal.trans(Nat, Nat.add(i, List.length(&2, Nat, Spec.leaves(ts))), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, [], Spec.leaves(ts)))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), {==}, finF)
      (%(desc)s, (%(st)s, {==}))
''' % {'p': P, 'rest': REST, 'desc': desc('ts', 'fitT', 'spT', 'inT', 'finT'), 'st': on_step('1n+dot', 'i', 'onAt')}
            elif taken:
                if kname == 'optional':
                    s += '''      +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
      +hP = Bool.and(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, %(rest)s), fitF2)
      +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      +isA = Lemma.and_true_right_side(okR, Spec.isAlt(alts, a), h2)
      +fitCh = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      +reads = G.optional_reads(a, ch, Lemma.and_true_left(okR, Spec.isAlt(alts, a), h2))
      +spCh = G.spells_first(input, i, Spec.leaves(ch), Spec.leaves(ts), spF)
''' % {'rest': REST}
                else:
                    s += '''      +rounds = {Spec.Pick{a, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rounds), Spec.Brack{Spec.Group{}, alts})
      +okR = Spec.roundsOk(Spec.Closure{}, rounds)
      +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rounds, grammar, tm)), Spec.fits(ts, grammar, %(rest)s), fitF2)
      +fitR = Lemma.and_true_right_side(okR, Spec.fits(rounds, grammar, tm), hOk)
      +all = G.closure_reads(rounds, Lemma.and_true_left(okR, Spec.fits(rounds, grammar, tm), hOk))
      +reads = G.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), all))
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
      +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +lr = Spec.leaves(rounds)
      +spR = G.spells_first(input, i, lr, Spec.leaves(ts), spF)
      +spCh = G.spells_first(input, i, Spec.leaves(ch), Spec.leaves(r), spR)
''' % {'rest': REST}
                s += '''      +seqEq = N1_and_right({L.evenLength(%(p)s) == True{} : Bool}, {Spec.sequenceAt(grammar, index, %(p)s) == %(seq)s : +List<Spec.Item>}, seq_of(rpath, grammar, input, root, index, k, p0, g, occ))
      +next = List.get(&2, Nat, input, i)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsA = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a), i, ch, fitCh, spCh, reads)
      Empty.absurd(%(goal)s, %(contra)s)
''' % {'p': P, 'seq': SEQ, 'goal': g2, 'contra': contra('enter_conflict(%s, grammar, t, index, rpath, dot, alts, a, n, next, U.lt_ne(a, n, isA), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))' % kind)}
            elif kname == 'closure' and spat.startswith('Con{Spec.Loop{Con{'):
                rs = sexpr[len('Spec.Loop{'):].rsplit('} <> ts', 1)[0]
                s += '''      +rsT = {%(rs)s : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, %(rest)s), fitF2)
      Empty.absurd(%(goal)s, Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
''' % {'rs': rs, 'rest': REST, 'goal': g2}
            else:
                s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % g2
    out.append(s)
open('m5.bend', 'w').write(''.join(out))
