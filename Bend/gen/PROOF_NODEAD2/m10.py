exec(open('m5.py').read().split('out = []')[0])
def tup(xs):
    return xs[0] if len(xs) == 1 else '(%s, %s)' % (xs[0], tup(xs[1:]))
SEQO = 'Gll.seqAt(grammar, index, outer)'
RESTO = 'Gll.dropFrom(1n+m, %s)' % SEQO
N = 'Gll.nthItem(%s, m)' % SEQO
PO = 'prefixOf(outer)'
PM = 'List.append(&2, Nat, %s, [m])' % PO
DE = 'Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}'
GOAL = lambda b: 'AllOn(grammar, input, root, Support.whenTrue(%s, [Support.FactDescriptor{%s}]))' % (b, DE)
def contra(ne):
    return 'Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, %s), noConf))' % ne
LD = '''  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, %(seqo)s)) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, %(po)s, m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {%(n)s == Some{Spec.Brack{KIND, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> R2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> R2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> R2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> R2, True{}, index, %(pm)s, 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(KIND, k, p0, Spec.Pick{a, g} <> R2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> R2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
''' % {'seqo': SEQO, 'po': PO, 'n': N, 'pm': PM}
LA = 'index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq'
out = []
for K, kn in (('Spec.Closure{}', 'closure'), ('Spec.Positive{}', 'positive')):
    B = 'Some{Spec.Brack{%s, alts}}' % K
    hsA = '''      +next = List.get(&2, Nat, input, end)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(%(B)s, k, end), grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(%(N)s, k, end), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, end), grammar, t, index, a1 <> (m <> outer))), %(B)s, %(N)s, Equal.sym(Maybe<&2, Spec.Item>, %(N)s, %(B)s, itEqP)), bEq)
''' % {'B': B, 'N': N}
    if kn == 'positive':
        hsA += '''      +h1b = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(True{}, grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Bool.not(Nat.is_eq(k, end)), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Bool, Bool, v => Gll.lsHas(next, Gll.roundPick(Bool.not(v), grammar, t, index, a1 <> (m <> outer))), False{}, Nat.is_eq(k, end), Equal.sym(Bool, Nat.is_eq(k, end), False{}, b2Eq)), h1)
'''
    else:
        hsA += '      +h1b = h1\n'
    hsA += '''      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a1), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(%(N)s, a1), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a1), t))), %(B)s, %(N)s, Equal.sym(Maybe<&2, Spec.Item>, %(N)s, %(B)s, itEqP)), h1b)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(%(po)s) == True{} : Bool}, {Spec.sequenceAt(grammar, index, %(po)s) == %(seqo)s : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(%(po)s) == True{} : Bool}, {Spec.sequenceAt(grammar, index, %(po)s) == %(seqo)s : +List<Spec.Item>}, sq)
      +n = List.length(&2, +List<Spec.Item>, alts)
''' % {'B': B, 'N': N, 'po': PO, 'seqo': SEQO}
    if kn == 'closure':
        conf = lambda c2, h2: 'enter_conflict(Spec.Closure{}, grammar, t, index, outer, m, alts, a1, %s, next, NEQ, seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), %s)' % (c2, h2)
        allR = 'Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, g}), Spec.allConsume(R2), ready)'
    else:
        conf = lambda c2, h2: 'after_conflict(grammar, t, index, outer, m, alts, a1, %s, next, NEQ, seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), %s)' % (c2, h2)
        allR = 'G.positive_next(k, p0, end, a, g, R2, ready)'
    # the next round, or none
    s = '''
# Another round of the %(kn)s loop, at a round's end that is not the loop's start.
law again_next_%(kn)s:
  for r2: +List<Spec.Tree>
''' % {'kn': kn} + TB + LD.replace('KIND', K).replace('R2', 'r2') + '''  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == False{} : Bool}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == True{} : Bool}
  %(goal)s

def again_next_%(kn)s(r2, %(tba)s, %(la)s, a1, isA1, b2Eq, bEq):
  match r2:
''' % {'pr': PR, 'd': DE, 'goal': GOAL('True{}'), 'tba': TBA, 'la': LA, 'kn': kn}
    # no more rounds: leave
    s += '''    case Nil{}:
''' + hsA + '''      +dEq = N1.nth_drop(%(seqo)s, m, Spec.Brack{%(K)s, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{%(K)s, alts} <> %(resto)s), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, %(seqo)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{%(K)s, alts} <> %(resto)s, Gll.dropFrom(m, %(seqo)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, %(seqo)s), Spec.Brack{%(K)s, alts} <> %(resto)s, dEq)), fitF)
      +tmR = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +fitT = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(%(K)s, rs), Spec.fits(rs, grammar, tmR)), Spec.fits(ts, grammar, %(resto)s), fitF2)
      +lrs = Spec.leaves(rs)
      +lts = Spec.leaves(ts)
      +eL = Nat.add(k, List.length(&2, Nat, lrs))
      +spT = G.spells_second(input, k, lrs, lts, spF)
      +hsL0 = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, eL, Spec.Loop{rs}, ts, seqEqO, fitF, fitT, spT, inF, Equal.sym(Nat, Nat.add(eL, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), G.end_split(k, lrs, lts)))
      +lg = Spec.leaves(g)
      +endL = Equal.trans(Nat, end, Nat.add(p0, List.length(&2, Nat, lg)), eL, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, lg)), end, endEq),
        Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, lg)), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), eL, G.end_alone(p0, lg), sumEq))
      +hsL = Equal.trans(Bool, Gll.lsHas(next, Gll.predictAt(grammar, t, index, outer, 1n+m)), Gll.lsHas(List.get(&2, Nat, input, eL), Gll.predictAt(grammar, t, index, outer, 1n+m)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.predictAt(grammar, t, index, outer, 1n+m)), end, eL, endL), hsL0)
      Empty.absurd(%(goal)s, %(c)s)
''' % {'seqo': SEQO, 'K': K, 'resto': RESTO, 'goal': GOAL('True{}'), 'c': contra(conf('n', 'leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL)').replace('NEQ', 'U.lt_ne(a1, n, isA1)'))}
    # a next round a3
    s += '''    case Con{Spec.Pick{+a3, +g3}, +r3}:
''' + hsA.replace('R2', 'r2') + '''      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +allR = %(allR)s
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +eg = Nat.add(p0, List.length(&2, Nat, lg))
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +nR = List.length(&2, Nat, Spec.leaves(rest2))
      +spRest = Equal.trans(+List<Nat>, Spec.leaves(rest2), Lemma.slice(input, eg, nR), Lemma.slice(input, end, nR), sp2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, nR), eg, end, endEq))
      +spG3 = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
      +wG = Spec.walk(g, False{}, index, List.append(&2, Nat, %(pm)s, [a]), 0n, k, p0)
      +wRest = Spec.walk(rest2, True{}, index, %(pm)s, 0n, k, eg)
      +inRest0 = N1.all_in_right_n(wG, wRest, Spec.steps(root, 0n), inR)
      +inRest = Equal.trans(Bool, Spec.allIn(Spec.walk(rest2, True{}, index, %(pm)s, 0n, k, end), Spec.steps(root, 0n)), Spec.allIn(wRest, Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(rest2, True{}, index, %(pm)s, 0n, k, v), Spec.steps(root, 0n)), end, eg, Equal.sym(Nat, eg, end, endEq)), inRest0)
      +ready3 = G.round_next(%(K)s, k, p0, end, a, g, rest2, {==}, ready)
      +sum3 = Equal.trans(Nat, Nat.add(end, nR), Nat.add(eg, nR), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), Equal.cong(Nat, Nat, v => Nat.add(v, nR), end, eg, Equal.sym(Nat, eg, end, endEq)),
        Equal.trans(Nat, Nat.add(eg, nR), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, Spec.leaves(rest2)))), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), G.end_split(p0, lg, Spec.leaves(rest2)), sumEq))
      L.either_case({a1 == a3 : Nat}, {Nat.is_eq(a1, a3) == False{} : Bool}, %(goal)s, U.decide(Nat.is_eq(a1, a3), a1, a3, {==}),
        +ae => again_same_%(kn)s(%(tba)s, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3),
        neq => Empty.absurd(%(goal)s, %(c)s))
''' % {'allR': allR.replace('R2', 'rest2'), 'pm': PM, 'K': K, 'goal': GOAL('True{}'), 'tba': TBA, 'kn': kn, 'c': contra(conf('a3', 'alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a3, next, isA3, hsA3)').replace('NEQ', 'neq'))}
    for rpat, rexpr in (('Con{Spec.Leaf{+x}, +r3}', 'Spec.Leaf{x} <> r3'), ('Con{Spec.Node{+q, +ch}, +r3}', 'Spec.Node{q, ch} <> r3'), ('Con{Spec.Skip{}, +r3}', 'Spec.Skip{} <> r3'), ('Con{Spec.Loop{+rr}, +r3}', 'Spec.Loop{rr} <> r3')):
        s += '''    case %s:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(%s, grammar, Spec.times(List.length(&2, Spec.Tree, %s), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(%s, Lemma.false_is_not_true(inner))
''' % (rpat, rexpr, rexpr, GOAL('True{}'))
    # the tree's next round, as the descriptor
    same = '''
law again_same_%(kn)s:
''' % {'kn': kn} + TB + '''  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, %(seqo)s)) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, %(po)s, m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {%(n)s == %(b)s : Maybe<&2, Spec.Item>}
  for +a1: Nat
  for +a3: Nat
  for +ae: {a1 == a3 : Nat}
  for +g3: +List<Spec.Tree>
  for +r3: +List<Spec.Tree>
  for +end: Nat
  for +fitRest: {Spec.fits(Spec.Pick{a3, g3} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a3, g3} <> r3), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spRest: G.Spells(Spec.Pick{a3, g3} <> r3, input, end)
  for +inRest: {Spec.allIn(Spec.walk(Spec.Pick{a3, g3} <> r3, True{}, index, %(pm)s, 0n, k, end), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready3: {G.roundsReady(%(K)s, k, end, Spec.Pick{a3, g3} <> r3) == True{} : Bool}
  for +sum3: {Nat.add(end, List.length(&2, Nat, Spec.leaves(Spec.Pick{a3, g3} <> r3))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +fitG3: {Spec.fits(g3, grammar, Spec.altOf(alts, a3)) == True{} : Bool}
  %(goal)s

def again_same_%(kn)s(%(tba)s, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3):
  +ea = Equal.sym(Nat, a1, a3, ae)
  %%ea : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, end}}]))
  +fitC = alt_fits(grammar, index, outer, m, a3, %(K)s, alts, g3, itEqP, fitG3)
  +spC = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
  +inC = round_child_walk(root, index, outer, m, k, end, a3, g3, r3, inRest)
  +ff = {Spec.Loop{rs} <> ts : +List<Spec.Tree>}
  %(build)s
''' % {'kn': kn, 'seqo': SEQO, 'po': PO, 'n': N, 'b': B, 'pm': PM, 'K': K, 'goal': GOAL('True{}').replace('a1 <> (m', 'a1 <> (m'), 'tba': TBA,
       'build': tup([tup(['end', 'g3', 'g3', tup([tup(['kc', 'p1', 'g1', 'ff', K, 'alts', 'occO', tup(['fitF', 'spF', 'inF', 'finF']), 'itEqP', tup(['fitC', 'spC', 'inC']), tup(['r3', 'fitRest', 'spRest', 'inRest', 'ready3', 'sum3'])]), tup(['fitC', 'spC', 'inC', '{==}'])])]), '{==}'])}
    out.append(same)
    out.append(s)
    # one alternative of another round: at the loop's start (the same as a first-round seed), or later
    s = '''
law again_one_%(kn)s:
  for b: Bool
  for b2: Bool
''' % {'kn': kn} + TB + '  for +r2: +List<Spec.Tree>\n' + LD.replace('KIND', K).replace('R2', 'r2') + '''  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == b2 : Bool}
  for +bEq: {Gll.admits(%(pr)s, grammar, input, %(d)s) == b : Bool}
  %(goal)s

def again_one_%(kn)s(b, b2, %(tba)s, r2, %(la)s, a1, isA1, b2Eq, bEq):
  match b b2:
    case False{} _:
      {==}
    case True{} True{}:
      +ke = Lemma.nat_eq_sound(k, end, b2Eq)
      %%ke : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, _}}]))
      +bK = Equal.trans(Bool, Gll.admits(%(pr)s, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, k}), Gll.admits(%(pr)s, grammar, input, %(d)s), True{},
        Equal.cong(Nat, Bool, v => Gll.admits(%(pr)s, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, v}), k, end, ke), bEq)
      seed_%(kn)s(Spec.Loop{rs} <> ts, True{}, %(tba)s, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a1, isA1, bK)
    case True{} False{}:
      again_next_%(kn)s(r2, %(tba)s, %(la)s, a1, isA1, b2Eq, bEq)
''' % {'kn': kn, 'pr': PR, 'd': DE, 'goal': GOAL('b'), 'tba': TBA, 'la': LA}
    out.append(s)
src = ''.join(out)
open('m10.bend', 'w').write(src)
