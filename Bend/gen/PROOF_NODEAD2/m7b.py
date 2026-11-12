exec(open('m5.py').read().split('out = []')[0])
def tup(xs):
    return xs[0] if len(xs) == 1 else '(%s, %s)' % (xs[0], tup(xs[1:]))
SEQO = 'Gll.seqAt(grammar, index, outer)'
RESTO = 'Gll.dropFrom(1n+m, %s)' % SEQO
N = 'Gll.nthItem(%s, m)' % SEQO
D = 'Gll.Desc{index, a <> (m <> outer), 0n, k, k}'
GOALT = 'AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{%s}]))' % D
CALLD = '''  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(FOREST, grammar, Gll.dropFrom(m, %s)) == True{} : Bool}
  for +spF: G.Spells(FOREST, input, k)
  for +inF: {Spec.allIn(Spec.walk(FOREST, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(FOREST))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
''' % SEQO
CALLA = 'index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts'
def contra2(ne):
    return 'Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, %s), noConf))' % ne
KINDS = {'group': ('Spec.Group{}', 'True{}', 'False{}', 'predict'), 'optional': ('Spec.Optional{}', 'False{}', 'True{}', 'first'),
         'closure': ('Spec.Closure{}', 'False{}', 'True{}', 'first'), 'positive': ('Spec.Positive{}', 'True{}', 'False{}', 'predict')}
out = []
for kn, (K, mbe, leave, how) in KINDS.items():
    B = 'Some{Spec.Brack{%s, alts}}' % K
    IT = 'Spec.Brack{%s, alts}' % K
    hsA = '''      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(%(B)s, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(%(N)s, k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), %(B)s, %(N)s, Equal.sym(Maybe<&2, Spec.Item>, %(N)s, %(B)s, itEqB)), bEq)
''' % {'B': B, 'N': N}
    if kn == 'group':
        hsA += '      +hsA = h1\n'
    elif kn == 'positive':
        hsA += '''      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(False{}, grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Bool.not(Nat.is_eq(k, k)), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Bool, Bool, v => Gll.lsHas(next, Gll.roundPick(Bool.not(v), grammar, t, index, a <> (m <> outer))), True{}, Nat.is_eq(k, k), Equal.sym(Bool, Nat.is_eq(k, k), True{}, Lemma.nat_eq_refl(k))), h1)
'''
    else:
        hsA += '''      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(%(N)s, a), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a), t))), %(B)s, %(N)s, Equal.sym(Maybe<&2, Spec.Item>, %(N)s, %(B)s, itEqB)), h1)
''' % {'B': B, 'N': N}
    head = '''      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == %(seqo)s : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == %(seqo)s : +List<Spec.Item>}, sq)
''' % {'seqo': SEQO} + hsA
    # the same choice: rewrite a to the tree's
    for shape in (['pick'] if kn in ('group', 'optional') else ['loop']):
        if shape == 'pick':
            F = 'Spec.Pick{a2, ch} <> ts'
            builder = 'seed_pick_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, %s, alts, itEqB, a2, ch, ts, fitF, spF, inF, finF, fitCh)' % K
            extraD = '  for +ch: +List<Spec.Tree>\n  for +ts: +List<Spec.Tree>\n  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a2)) == True{} : Bool}\n'
            extraA = 'ch, ts, fitCh'
            trees = 'ch, ts'
            extraF = 'fitCh'
        else:
            F = 'Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts'
            builder = 'seed_loop_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, %s, alts, itEqB, a2, ch, r, ts, fitF, spF, inF, finF, fitR, ready)' % K
            extraD = '  for +ch: +List<Spec.Tree>\n  for +r: +List<Spec.Tree>\n  for +ts: +List<Spec.Tree>\n  for +fitR: {Spec.fits(Spec.Pick{a2, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}\n  for +ready: {G.roundsReady(%s, k, k, Spec.Pick{a2, ch} <> r) == True{} : Bool}\n' % K
            extraA = 'ch, r, ts, fitR, ready'
            trees = 'ch, r, ts'
            extraF = 'fitR, ready'
        s = '''
law same_%(kn)s:
''' % {'kn': kn} + TB + '''  for +a: Nat
  for +a2: Nat
  for +ae: {a == a2 : Nat}
''' + extraD.split('  for +fit')[0] + CALLD.replace('FOREST', F) + '''  for +itEqB: {%(N)s == %(B)s : Maybe<&2, Spec.Item>}
%(extraD)s  AllOn(grammar, input, root, [Support.FactDescriptor{%(D)s}])

def same_%(kn)s(%(tba)s, a, a2, ae, %(trees)s, %(calla)s, itEqB, %(extraF)s):
  +ea = Equal.sym(Nat, a, a2, ae)
  %%ea : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, k}}])
  %(builder)s
''' % {'kn': kn, 'N': N, 'B': B, 'extraD': '  for +fit' + '  for +fit'.join(extraD.split('  for +fit')[1:]), 'D': D, 'tba': TBA, 'calla': CALLA, 'trees': trees, 'extraF': extraF, 'builder': builder}
        out.append(s)
    # the seeding lemma, by the tree's shape
    shapes = [('Nil{}', '[]'), ('Con{Spec.Leaf{+x}, +ts}', 'Spec.Leaf{x} <> ts'), ('Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
              ('Con{Spec.Pick{+a2, +ch}, +ts}', 'Spec.Pick{a2, ch} <> ts'), ('Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'),
              ('Con{Spec.Loop{Nil{}}, +ts}', 'Spec.Loop{[]} <> ts'), ('Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts}', 'Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts'),
              ('Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts}', 'Spec.Loop{Spec.Leaf{x} <> r} <> ts'), ('Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts}', 'Spec.Loop{Spec.Node{q, ch} <> r} <> ts'),
              ('Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts}', 'Spec.Loop{Spec.Skip{} <> r} <> ts'), ('Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts}', 'Spec.Loop{Spec.Loop{rs} <> r} <> ts')]
    s = '''
# A seed of the %(kn)s bracket on the tree: the tree's own alternate, else not admitted.
law seed_%(kn)s:
  for ff: +List<Spec.Tree>
  for b: Bool
''' % {'kn': kn} + TB + CALLD.replace('FOREST', 'ff') + '''  for +itEqB: {%(N)s == %(B)s : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(D)s) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{%(D)s}]))

def seed_%(kn)s(ff, b, %(tba)s, %(calla)s, itEqB, a, isA, bEq):
  match ff b:
''' % {'kn': kn, 'N': N, 'B': B, 'pr': PR, 'D': D, 'tba': TBA, 'calla': CALLA}
    for bpat in ('False{}', 'True{}'):
        for spat, sexpr in shapes:
            s += '    case %s %s:\n' % (spat, bpat)
            if bpat == 'False{}':
                s += '      {==}\n'
                continue
            s += '''      +dEq = N1.nth_drop(%(seqo)s, m, %(it)s, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(%(f)s, grammar, %(it)s <> %(resto)s), Spec.fits(%(f)s, grammar, Gll.dropFrom(m, %(seqo)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(f)s, grammar, v), %(it)s <> %(resto)s, Gll.dropFrom(m, %(seqo)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, %(seqo)s), %(it)s <> %(resto)s, dEq)), fitF)
''' % {'seqo': SEQO, 'it': IT, 'f': sexpr, 'resto': RESTO}
            pick = spat.startswith('Con{Spec.Pick')
            loopPick = 'Loop{Con{Spec.Pick' in spat
            loopNil = 'Loop{Nil' in spat
            skip = spat.startswith('Con{Spec.Skip')
            loopOther = spat.startswith('Con{Spec.Loop{Con{') and not loopPick
            real = (kn in ('group', 'optional') and pick) or (kn in ('closure', 'positive') and loopPick) or (kn == 'optional' and skip) or (kn == 'closure' and loopNil)
            if not real:
                if loopOther and kn in ('closure', 'positive'):
                    rs = sexpr[len('Spec.Loop{'):].rsplit('} <> ts', 1)[0]
                    s += '''      +rsT = {%(rs)s : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(%(K)s, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, %(resto)s), fitF2)
      Empty.absurd(%(goal)s, Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(%(K)s, rsT), Spec.fits(rsT, grammar, tm), inner)))
''' % {'rs': rs, 'K': K, 'resto': RESTO, 'goal': GOALT}
                else:
                    s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % GOALT
                continue
            s += head
            if skip or loopNil:
                x = 'Spec.Skip{}' if skip else 'Spec.Loop{[]}'
                s += '''      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsL = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, k, %(x)s, ts, seqEqO, fitF, fitF2, spF, inF, {==})
      Empty.absurd(%(goal)s, %(c)s)
''' % {'x': x, 'goal': GOALT, 'c': contra2('enter_conflict(%s, grammar, t, index, outer, m, alts, a, n, next, U.lt_ne(a, n, isA), seqEqO, itEqB, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL))' % K)}
                continue
            # the tree takes a2
            if pick:
                if kn == 'group':
                    s += '''      +hP = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, %(resto)s), fitF2)
      +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
''' % {'resto': RESTO}
                else:
                    s += '''      +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a2, ch}])
      +hP = Bool.and(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, %(resto)s), fitF2)
      +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +isA2 = Lemma.and_true_right_side(okR, Spec.isAlt(alts, a2), h2)
      +fitCh = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +reads = G.optional_reads(a2, ch, Lemma.and_true_left(okR, Spec.isAlt(alts, a2), h2))
''' % {'resto': RESTO}
                s += '''      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(ts), spF)
      +inCh = pick_child_walk(root, index, outer, m, kc, k, a2, ch, ts, inF)
'''
                same = 'same_%s(%s, a, a2, ae, ch, ts, %s, itEqB, fitCh)' % (kn, TBA, CALLA)
            else:
                s += '''      +rounds = {Spec.Pick{a2, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rounds), Spec.Brack{Spec.Group{}, alts})
      +okR = Spec.roundsOk(%(K)s, rounds)
      +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rounds, grammar, tm)), Spec.fits(ts, grammar, %(resto)s), fitF2)
      +fitR = Lemma.and_true_right_side(okR, Spec.fits(rounds, grammar, tm), hOk)
      +okRT = Lemma.and_true_left(okR, Spec.fits(rounds, grammar, tm), hOk)
      +ready = G.ready_entry(%(K)s, k, rounds, {==}, okRT)
      +h = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
      +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +spR = G.spells_first(input, k, Spec.leaves(rounds), Spec.leaves(ts), spF)
      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(r), spR)
      +inCh = round_child_walk(root, index, outer, m, k, k, a2, ch, r, loop_rounds_walk(root, index, outer, m, kc, k, rounds, ts, inF))
''' % {'K': K, 'resto': RESTO}
                if kn == 'closure':
                    s += '      +reads = G.consumes_child(a2, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch}), Spec.allConsume(r), G.closure_reads(rounds, okRT)))\n'
                same = 'same_%s(%s, a, a2, ae, ch, r, ts, %s, itEqB, fitR, ready)' % (kn, TBA, CALLA)
            if how == 'predict':
                hs2 = 'round_predict_set(grammar, start, t, po, input, root, rootFit, rootSp, index, a2 <> (m <> outer), k, k, ch, (alt_fits(grammar, index, outer, m, a2, %s, alts, ch, itEqB, fitCh), (spCh, inCh)), round_seq_eq(grammar, index, outer, m, a2, evenO, seqEqO))' % K
            else:
                hs2 = 'round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a2), k, ch, fitCh, spCh, reads)'
            conflict = 'enter_conflict(%s, grammar, t, index, outer, m, alts, a, a2, next, neq, seqEqO, itEqB, alt_has(%s, %s, grammar, t, index, outer, m, alts, a, next, isA, hsA), alt_has(%s, %s, grammar, t, index, outer, m, alts, a2, next, isA2, %s))' % (K, mbe, leave, mbe, leave, hs2)
            s += '''      L.either_case({a == a2 : Nat}, {Nat.is_eq(a, a2) == False{} : Bool}, %(goal)s, U.decide(Nat.is_eq(a, a2), a, a2, {==}),
        +ae => %(same)s,
        neq => Empty.absurd(%(goal)s, %(c)s))
''' % {'goal': GOALT, 'same': same, 'c': contra2(conflict)}
    out.append(s)
open('m7b.bend', 'w').write(''.join(out))
