exec(open('m5.py').read().split('out = []')[0])
def tup(xs):
    return xs[0] if len(xs) == 1 else '(%s, %s)' % (xs[0], tup(xs[1:]))
D1 = 'Gll.Desc{index, rpath, 1n+dot, k, end}'
Y1 = 'Gll.stepAt(index, rpath, 1n+dot, k, i, end)'
GOALB = lambda b: 'AllOn(grammar, input, root, Support.whenTrue(%s, [Support.FactDescriptor{%s}, Support.FactStep{%s}]))' % (b, D1, Y1)
CD = '''  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +p0c: Nat
  for +gc: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0c, gc)
  for +fitF: {Spec.fits(FOREST, grammar, Gll.dropFrom(dot, %s)) == True{} : Bool}
  for +spF: G.Spells(FOREST, input, i)
  for +inF: {Spec.allIn(Spec.walk(FOREST, False{}, index, %s, dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(FOREST))) == Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))) : Nat}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(%s, dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +seqEq: {Spec.sequenceAt(grammar, index, %s) == %s : +List<Spec.Item>}
''' % (SEQ, P, SEQ, P, SEQ)
CA = 'index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, kind, alts, itEq, seqEq'
IT = 'Spec.Brack{kind, alts}'
def resumed(x, sub, extra):
    # the resumed descriptor after the bracket tree x, whose leaves are sub, at e
    return '''      +dEq = N1.nth_drop(%(seq)s, dot, %(it)s, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(%(x)s <> ts, grammar, %(it)s <> %(rest)s), Spec.fits(%(x)s <> ts, grammar, Gll.dropFrom(dot, %(seq)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(x)s <> ts, grammar, v), %(it)s <> %(rest)s, Gll.dropFrom(dot, %(seq)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(seq)s), %(it)s <> %(rest)s, dEq)), fitF)
      +fitT = Fits.fits_tail(%(x)s, ts, grammar, %(it)s, %(rest)s, fitF2)
      +lx = Spec.leaves(%(sub)s)
      +lts = Spec.leaves(ts)
      +e = Nat.add(i, List.length(&2, Nat, lx))
      +spT = G.spells_second(input, i, lx, lts, spF)
      +here = Spec.at(index, %(p)s, 1n+dot, k, i, e)
      +wX = %(wx)s
      +wT = Spec.walk(ts, False{}, index, %(p)s, 1n+dot, k, e)
      +inA = N1.all_in_tail_n(here, List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n), inF)
      +inT = N1.all_in_right_n(wX, wT, Spec.steps(root, 0n), inA)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lx, lts))), Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))), G.end_split(i, lx, lts), finF)
%(extra)s      %%eEnd : %(goalU)s
      ((p0c, (gc, (ts, (occ, (fitT, (spT, (inT, finT))))))), (%(st)s, {==}))
''' % {'seq': SEQ, 'it': IT, 'x': x, 'rest': REST, 'sub': sub, 'p': P, 'extra': extra,
       'wx': ('Spec.walk(%s, False{}, index, List.append(&2, Nat, %s, [dot, a2]), 0n, i, i)' % (sub, P)) if x.startswith('Spec.Pick') else ('Spec.walk(%s, True{}, index, List.append(&2, Nat, %s, [dot]), 0n, i, i)' % (sub, P)),
       'goalU': 'AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, _}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, _)}]))',
       'st': on_step('1n+dot', 'e', 'onAt')}
out = []
# ---- a loop round boundary ----
s = '''
# At the end of a round of a loop on the tree: the loop's end, or a resume that prediction
# does not admit (another round follows, and it reads something).
law resume_loop:
  for r2: +List<Spec.Tree>
  for b: Bool
''' + TB + '''  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
''' + CD.replace('FOREST', 'Spec.Loop{rs} <> ts') + '''  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +ready: {G.roundsReady(kind, i, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(i, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == b : Bool}
  %(goal)s

def resume_loop(r2, b, %(tba)s, rs, ts, %(ca)s, a, p0, g, endEq, fitR, spR, ready, sumEq, bEq):
  match r2 b:
''' % {'pr': PR, 'd': D1, 'goal': GOALB('b'), 'tba': TBA, 'ca': CA}
for bpat in ('False{}', 'True{}'):
    for rpat, rexpr in (('Nil{}', '[]'), ('Con{Spec.Pick{+a3, +g3}, +r3}', 'Spec.Pick{a3, g3} <> r3'), ('Con{Spec.Leaf{+x}, +r3}', 'Spec.Leaf{x} <> r3'),
                        ('Con{Spec.Node{+q, +ch}, +r3}', 'Spec.Node{q, ch} <> r3'), ('Con{Spec.Skip{}, +r3}', 'Spec.Skip{} <> r3'), ('Con{Spec.Loop{+rr}, +r3}', 'Spec.Loop{rr} <> r3')):
        s += '    case %s %s:\n' % (rpat, bpat)
        if bpat == 'False{}':
            s += '      {==}\n'
            continue
        if rpat == 'Nil{}':
            extra = '''      +lg = Spec.leaves(g)
      +eEnd = Equal.trans(Nat, e, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), end, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), e, sumEq),
        Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), Nat.add(p0, List.length(&2, Nat, lg)), end, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, lg)), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), G.end_alone(p0, lg)), endEq))
'''
            s += resumed('Spec.Loop{rs}', 'rs', extra)
            continue
        if not rpat.startswith('Con{Spec.Pick'):
            s += '''      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(%s, grammar, Spec.times(List.length(&2, Spec.Tree, %s), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(%s, Lemma.false_is_not_true(inner))
''' % (rexpr, rexpr, GOALB('True{}'))
            continue
        s += '''      resume_next(kind, %(tba)s, rs, ts, %(ca)s, a, p0, g, a3, g3, r3, endEq, fitR, spR, ready, bEq)
''' % {'tba': TBA, 'ca': CA.replace('kind, ', '')}
out.append(s)
# the conflict when another round follows
s = '''
law resume_next:
  for kind0: Spec.Bracket
''' + TB + '''  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
''' + CD.replace('FOREST', 'Spec.Loop{rs} <> ts').replace('  for +kind: Spec.Bracket\n', '').replace('{kind, alts}', '{kind0, alts}') + '''  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +a3: Nat
  for +g3: +List<Spec.Tree>
  for +r3: +List<Spec.Tree>
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3), grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3)), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3), input, p0)
  for +ready: {G.roundsReady(kind0, i, p0, Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3)) == True{} : Bool}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == True{} : Bool}
  %(goal)s

def resume_next(kind0, %(tba)s, rs, ts, %(ca)s, a, p0, g, a3, g3, r3, endEq, fitR, spR, ready, bEq):
''' % {'pr': PR, 'd': D1, 'goal': GOALB('True{}'), 'tba': TBA, 'ca': CA.replace('kind, ', '')}
common = '''      +next = List.get(&2, Nat, input, end)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +sp3 = G.spells_first(input, Nat.add(p0, List.length(&2, Nat, lg)), Spec.leaves(g3), Spec.leaves(r3), sp2)
      +n3 = List.length(&2, Nat, Spec.leaves(g3))
      +spG3 = Equal.trans(+List<Nat>, Spec.leaves(g3), Lemma.slice(input, Nat.add(p0, List.length(&2, Nat, lg)), n3), Lemma.slice(input, end, n3), sp3, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, n3), Nat.add(p0, List.length(&2, Nat, lg)), end, endEq))
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
'''
def contra3(ne):
    return 'Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, %s), noConf))' % ne
s += '  match kind0:\n'
s += '    case Spec.Closure{}:\n      +allR = Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, g}), Spec.allConsume(rest2), ready)\n'.replace('rest2', 'Spec.Pick{a3, g3} <> r3') + common
s += '      Empty.absurd(%s, %s)\n' % (GOALB('True{}'), contra3('enter_conflict(Spec.Closure{}, grammar, t, index, rpath, dot, alts, a3, n, next, U.lt_ne(a3, n, isA3), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a3, next, isA3, hsA3), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))'))
s += '    case Spec.Positive{}:\n      +allR = G.positive_next(i, p0, end, a, g, Spec.Pick{a3, g3} <> r3, ready)\n' + common
s += '      Empty.absurd(%s, %s)\n' % (GOALB('True{}'), contra3('after_conflict(grammar, t, index, rpath, dot, alts, a3, n, next, U.lt_ne(a3, n, isA3), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a3, next, isA3, hsA3), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))'))
for kd in ('Spec.Group{}', 'Spec.Optional{}'):
    s += '''    case %(kd)s:
      +dEq = N1.nth_drop(%(seq)s, dot, Spec.Brack{%(kd)s, alts}, itEq)
      Empty.absurd(%(goal)s, Lemma.false_is_not_true(Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{%(kd)s, alts} <> %(rest)s), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, %(seq)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{%(kd)s, alts} <> %(rest)s, Gll.dropFrom(dot, %(seq)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(seq)s), Spec.Brack{%(kd)s, alts} <> %(rest)s, dEq)), fitF)))
''' % {'kd': kd, 'seq': SEQ, 'goal': GOALB('True{}'), 'rest': REST}
out.insert(0, s)
# ---- the caller's forest, by the round's place in it ----
s = '''
law resume_br_f:
  for ff: +List<Spec.Tree>
  for b: Bool
''' + TB + CD.replace('FOREST', 'ff') + '''  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +ri: RoundIn(ff, grammar, input, root, index, rpath, dot, a, i, p0, g, kind, alts)
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == b : Bool}
  %(goal)s

def resume_br_f(ff, b, %(tba)s, %(ca)s, a, p0, g, ri, endEq, bEq):
  match ff b:
''' % {'pr': PR, 'd': D1, 'goal': GOALB('b'), 'tba': TBA, 'ca': CA}
SH = [('Nil{}', '[]'), ('Con{Spec.Leaf{+x}, +ts}', 'Spec.Leaf{x} <> ts'), ('Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
      ('Con{Spec.Pick{+a2, +ch}, +ts}', 'Spec.Pick{a2, ch} <> ts'), ('Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'), ('Con{Spec.Loop{+rs}, +ts}', 'Spec.Loop{rs} <> ts')]
for bpat in ('False{}', 'True{}'):
    for spat, sexpr in SH:
        s += '    case %s %s:\n' % (spat, bpat)
        if bpat == 'False{}':
            s += '      {==}\n'
            continue
        if spat.startswith('Con{Spec.Pick'):
            extra = '''      +eEnd = Equal.trans(Nat, e, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), end,
        Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g, ce),
          Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves(g))), i, p0, Equal.sym(Nat, p0, i, pe))), endEq)
'''
            body = resumed('Spec.Pick{a2, ch}', 'ch', extra)
            s += '      match ri:\n        case (ae, (ce, pe)):\n' + '\n'.join('    ' + l if l.strip() else l for l in body.rstrip('\n').split('\n')) + '\n'
        elif spat.startswith('Con{Spec.Loop'):
            s += '''      match ri:
        case (r2, (fitR, (spR, (inR, (ready, sumEq))))):
          resume_loop(r2, True{}, %(tba)s, rs, ts, %(ca)s, a, p0, g, endEq, fitR, spR, ready, sumEq, bEq)
''' % {'tba': TBA, 'ca': CA}
        else:
            s += '      Empty.absurd(%s, Lemma.false_is_not_true(ri))\n' % GOALB('True{}')
out.append(s)
open('m9c.bend', 'w').write(''.join(out))
