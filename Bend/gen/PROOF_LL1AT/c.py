exec(open('common.py').read())
out = []
CTXR = CTX.replace('  for +kind: Spec.Bracket\n', '').replace('  for +later: Bool\n', '')
CTXRA = 'index, prefix, dot, i, k, alts, restO, E'
def rbind(F, K, LT):
    return '''        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(%(K)s, %(LT)s, %(F)s) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(%(seq)s, dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, %(seq)s) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits(%(F)s, grammar, Spec.times(List.length(&2, Spec.Tree, %(F)s), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells(%(F)s, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(%(F)s, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves(%(F)s))) == E : Nat}}
''' % {'seq': SEQ, 'F': F, 'K': K, 'LT': LT}
KINDS = [('Spec.Group{}', 'group'), ('Spec.Optional{}', 'optional'), ('Spec.Closure{}', 'closure'), ('Spec.Positive{}', 'positive')]
LATERS = ['True{}', 'False{}']
def rready(F, kind, later):
    return 'Ready(True{}, grammar, start, input, root, %s, [], index, prefix, dot, i, k, %s, alts, restO, %s, E)' % (F, kind, later)

# ---- no more rounds: leaving the loop ----
F = '[]'
s = '''
law rounds_nil_ok:
  for kind: Spec.Bracket
  for later: Bool
''' + TB + CTXR + '''  for ready: %(ready)s
  %(goal)s

def rounds_nil_ok(kind, later, %(tba)s, %(ctxa)s, ready):
  match kind later:
''' % {'ready': rready(F, 'kind', 'later'), 'goal': allok(made(F, rounds='True{}')), 'tba': TBA, 'ctxa': CTXRA}
for K, kn in KINDS:
    for LT in LATERS:
        goal = allok(made(F, rounds='True{}', later=LT))
        s += '    case %s %s:\n      match ready:\n' % (K, LT)
        if kn in ('group', 'optional') or (kn == 'positive' and LT == 'False{}'):
            why = 'isL' if kn in ('group', 'optional') else 'fine'
            s += '''        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(%s, Lemma.false_is_not_true(%s))
''' % (goal, why)
            continue
        cp = 'U.after_cp' if (kn == 'positive') else 'U.bracket_cp'
        point = 'Spec.AfterRoundAt{index, prefix, dot}' if kn == 'positive' else 'Spec.BracketAt{index, prefix, dot}'
        s += rbind(F, K, LT).replace('kind, alts}}', K + ', alts}}') + '''          +n = List.length(&2, +List<Spec.Item>, alts)
          +next = List.get(&2, Nat, input, E)
          +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), fin)
          +ek = Equal.sym(Nat, k, E, nk)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%(seq)s, dot), Some{Spec.Brack{%(K)s, alts}}, itAt)
          cpL = %(cp)s(grammar, start, index, prefix, dot, n, %(K)s, alts, restO, next, itAt, restAt,
            U.leave_cp(Spec.isAlt(alts, n), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(n), {==}, LP))
          %%itS : AllOk(grammar, start, input, [Spec.Made{Spec.roundPoint(%(LT)s, _, index, prefix, dot), k, Spec.alternateCount(_)}])
          %%ek : AllOk(grammar, start, input, [Spec.Made{%(point)s, _, n}])
          (cpL, {==})
''' % {'seq': SEQ, 'K': K, 'cp': cp, 'LT': LT, 'point': point}
out.append(s)

# ---- another round ----
F = 'Spec.Pick{a, ch} <> r'
PC1 = 'List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])'
PCN = 'List.append(&2, Nat, prefix, [dot, a])'
s = '''
law rounds_pick_ok:
  for kind: Spec.Bracket
  for later: Bool
''' + TB + CTXR + '''  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for ready: %(ready)s
  for ihCh: %(ihc)s
  for ihR: %(ihr)s
  %(goal)s

def rounds_pick_ok(kind, later, %(tba)s, %(ctxa)s, a, ch, r, ready, ihCh, ihR):
  match kind later:
''' % {'ready': rready(F, 'kind', 'later'), 'ihc': ih('ch'), 'ihr': ih('r'), 'goal': allok(made(F, rounds='True{}')), 'tba': TBA, 'ctxa': CTXRA}
for K, kn in KINDS:
    for LT in LATERS:
        goal = allok(made(F, rounds='True{}', later=LT))
        s += '    case %s %s:\n      match ready:\n' % (K, LT)
        if kn in ('group', 'optional'):
            s += '''        case (itAt0, (restAt0, (isL, rest))):
          Empty.absurd(%s, Lemma.false_is_not_true(isL))
''' % goal
            continue
        reads = 'U.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine))'
        firstPw = 'U.first_from(lc, next, grammar, input, ch, Spec.altOf(alts, a), k, fC, {==}, spC, {==}, %s)' % reads
        if kn == 'closure':
            point, cpf, flags, pw = 'Spec.BracketAt{index, prefix, dot}', 'U.bracket_cp', 'False{}, True{}', firstPw
            fineR = 'Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine)'
        elif LT == 'False{}':
            point, cpf, flags = 'Spec.BracketAt{index, prefix, dot}', 'U.bracket_cp', 'True{}, False{}'
            pw = '''U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.altOf(alts, a), index, %(pcn)s, %(pc1)s, k, i, e, wC, fC, spC, {==}, {==}, asc,
                U.end_walk(ch, Spec.altOf(alts, a), 0n, grammar, index, %(pc1)s, i, k, e, fC, cEq1, {==}, {==}), inC)''' % {'pcn': PCN, 'pc1': PC1}
            fineR = 'U.positive_rest(Spec.Pick{a, ch}, r, fine)'
        else:
            point, cpf, flags, pw = 'Spec.AfterRoundAt{index, prefix, dot}', 'U.after_cp', 'False{}, True{}', firstPw
            fineR = 'Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine)'
        mC = made('ch', later='False{}', prefix=PCN, dot='0n')
        mR = made('r', rounds='True{}', later='True{}', k='e')
        s += rbind(F, K, LT).replace('kind, alts}}', K + ', alts}}') + '''          +tmR = Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(r, grammar, tmR), fR)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fRest = Lemma.and_true_right_side(h, Spec.fits(r, grammar, tmR), fR)
          +lc = Spec.leaves(ch)
          +lr = Spec.leaves(r)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lr, sp)
          +spR = G.spells_second(input, k, lc, lr, sp)
          +asc = G.nat_append_assoc(prefix, [dot], [a])
          +wC = Spec.walk(ch, False{}, index, %(pc1)s, 0n, i, k)
          +wR = Spec.walk(r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, e)
          +inC = U.all_in_left(wC, wR, %(steps)s, inW)
          +inRr = U.all_in_right(wC, wR, %(steps)s, inW)
          +inCN = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, %(pcn)s, 0n, i, k), %(steps)s), Spec.allIn(wC, %(steps)s), True{},
            Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, i, k), %(steps)s), %(pcn)s, %(pc1)s, Equal.sym(+List<Nat>, %(pc1)s, %(pcn)s, asc)), inC)
          +cEqN = U.seq_child(grammar, index, prefix, dot, a, %(K)s, alts, even, itAt)
          +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, %(pc1)s), Spec.sequenceAt(grammar, index, %(pcn)s), Spec.altOf(alts, a),
            Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), %(pc1)s, %(pcn)s, asc), cEqN)
          +evenC = Equal.trans(Bool, L.evenLength(%(pcn)s), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +finRr = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lr)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc, lr))), E, G.end_split(k, lc, lr), fin)
          +next = List.get(&2, Nat, input, k)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%(seq)s, dot), Some{Spec.Brack{%(K)s, alts}}, itAt)
          cp = %(cpf)s(grammar, start, index, prefix, dot, a, %(K)s, alts, restO, next, itAt, restAt,
            U.alt_cp(Spec.isAlt(alts, a), grammar, start, alts, a, index, prefix, dot, %(flags)s, restO, next, isA,
              %(pw)s))
          okC = ihCh(False{}, False{}, Spec.altOf(alts, a), index, %(pcn)s, 0n, i, k, %(K)s, alts, restO, E, %(rdC)s)
          okR = ihR(True{}, True{}, [], index, prefix, dot, i, e, %(K)s, alts, restO, E, %(rdR)s)
          %%itS : AllOk(grammar, start, input, Spec.Made{Spec.roundPoint(%(LT)s, _, index, prefix, dot), k, a} <> List.append(&2, Spec.Made, %(mC)s, %(mR)s))
          (cp, ok_append(%(mC)s, %(mR)s, grammar, start, input, okC, okR))
''' % {'pc1': PC1, 'pcn': PCN, 'steps': STEPS, 'K': K, 'seq': SEQ, 'cpf': cpf, 'flags': flags, 'pw': pw, 'LT': LT, 'mC': mC, 'mR': mR,
       'rdC': tup(['fC', 'spC', 'inCN', 'cEqN', 'evenC']), 'rdR': tup(['itAt', 'restAt', 'isL', 'even', 'fRest', fineR, 'spR', 'inRr', 'finRr', 'LP'])}
out.append(s)
open('c.bend', 'w').write(''.join(out))
