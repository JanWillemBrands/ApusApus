exec(open('a.py').read().split("\nout = []")[0])
exec(open('a.py').read().split("ITEM_CASES = ")[1].split("# ---- a leaf ----")[0].join(["ITEM_CASES = ", ""]))
out = []
# ---- a pick: ( ) or [ ] ----
F = 'Spec.Pick{a, ch} <> ts'
G0 = allok(made(F))
PCN = 'List.append(&2, Nat, prefix, [dot, a])'
def pick_case(K, kn):
    B = 'Spec.Brack{%s, balts}' % K
    if kn == 'group':
        h = '''          +h = Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +isA = Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
'''
    else:
        h = '''          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +h = Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +reads = U.optional_consume(a, ch, Lemma.and_true_left(okR, Spec.isAlt(balts, a), h2))
          +isA = Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), h2)
          +fC = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
'''
    if kn == 'group':
        pw = '''U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.altOf(balts, a), index, %(pcn)s, %(pcn)s, k, k, e, wC, fC, spC, {==}, {==}, {==},
                U.end_walk(ch, Spec.altOf(balts, a), 0n, grammar, index, %(pcn)s, k, k, e, fC, cEq, {==}, {==}), inC)''' % {'pcn': PCN}
        flags = 'True{}, False{}'
    else:
        pw = 'U.first_from(lc, next, grammar, input, ch, Spec.altOf(balts, a), k, fC, {==}, spC, {==}, reads)'
        flags = 'False{}, True{}'
    return '''    case Con{%(B0)s, +restI}:
      match ready:
%(bind)s          +it = {%(B)s : Spec.Item}
%(h)s          +lc = Spec.leaves(ch)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lt, sp)
          +spT = G.spells_second(input, k, lc, lt, sp)
          +wC = Spec.walk(ch, False{}, index, %(pcn)s, 0n, k, k)
          +wT = %(wT)s
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wC, wT), %(steps)s, inW)
          +inC = U.all_in_left(wC, wT, %(steps)s, inA)
          +inT = U.all_in_right(wC, wT, %(steps)s, inA)
          +itAt = U.items_from_head(dot, %(seq)s, it, restI, itemsEq)
          +itT = U.items_from_tail(dot, %(seq)s, it, restI, itemsEq)
          +cEq = U.seq_child(grammar, index, prefix, dot, a, %(K)s, balts, even, itAt)
          +evenC = Equal.trans(Bool, L.evenLength(%(pcn)s), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +next = List.get(&2, Nat, input, k)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, %(K)s, balts, restI, next, itAt, itT,
            U.alt_cp(Spec.isAlt(balts, a), grammar, start, balts, a, index, prefix, dot, %(flags)s, restI, next, isA,
              %(pw)s))
          okC = ihCh(False{}, False{}, Spec.altOf(balts, a), index, %(pcn)s, 0n, k, k, kind, alts, restO, E, %(rdC)s)
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, %(rdT)s)
          (cp, ok_append(%(mC)s, %(mT)s, grammar, start, input, okC, okT))
''' % {'B0': B.replace('balts', '+balts'), 'B': B, 'bind': seq_bind(F, B + ' <> restI'), 'h': h, 'pcn': PCN, 'wT': walkS('ts', '1n+dot', 'e'), 'steps': STEPS, 'seq': SEQ, 'K': K,
       'flags': flags, 'pw': pw, 'rdC': tup(['fC', 'spC', 'inC', 'cEq', 'evenC']), 'rdT': tup(['fT', 'spT', 'inT', 'itT', 'even']),
       'mC': made('ch', later='False{}', prefix=PCN, dot='0n'), 'mT': made('ts', later='False{}', dot='1n+dot', k='e')}
s = '''
law pick_ok:
  for items: +List<Spec.Item>
''' + TB + CTX + '''  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: %(ready)s
  for ihCh: %(ihc)s
  for ihTs: %(iht)s
  %(goal)s

def pick_ok(items, %(tba)s, %(ctxa)s, a, ch, ts, ready, ihCh, ihTs):
  match items:
''' % {'ready': ready('False{}', F), 'ihc': ih('ch'), 'iht': ih('ts'), 'goal': G0, 'tba': TBA, 'ctxa': CTXA}
s += pick_case('Spec.Group{}', 'group') + pick_case('Spec.Optional{}', 'optional')
s += absurd_cases(['Con{Spec.Brack{Spec.Group', 'Con{Spec.Brack{Spec.Optional'], F, G0)
out.append(s)

# ---- a loop: { } or < > ----
F = 'Spec.Loop{rs} <> ts'
G0 = allok(made(F))
def loop_case(K, kn):
    B = 'Spec.Brack{%s, balts}' % K
    fine = 'U.closure_consume(rs, Lemma.and_true_left(okR, Spec.fits(rs, grammar, tm), hOk))' if kn == 'closure' else 'Lemma.and_true_left(okR, Spec.fits(rs, grammar, tm), hOk)'
    return '''    case Con{%(B0)s, +restI}:
      match ready:
%(bind)s          +it = {%(B)s : Spec.Item}
          +okR = Spec.roundsOk(%(K)s, rs)
          +tm = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})
          +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fR = Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, tm), hOk)
          +fT = Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fine = %(fine)s
          +lr = Spec.leaves(rs)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lr))
          +spR = G.spells_first(input, k, lr, lt, sp)
          +spT = G.spells_second(input, k, lr, lt, sp)
          +wR = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
          +wT = %(wT)s
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wR, wT), %(steps)s, inW)
          +inR = U.all_in_left(wR, wT, %(steps)s, inA)
          +inT = U.all_in_right(wR, wT, %(steps)s, inA)
          +itAt = U.items_from_head(dot, %(seq)s, it, restI, itemsEq)
          +itT = U.items_from_tail(dot, %(seq)s, it, restI, itemsEq)
          LP = U.predicts_in(List.get(&2, Nat, input, e), grammar, start, input, root, rootFit, rootSp, ts, restI, index, prefix, prefix, e, i, Nat.add(e, List.length(&2, Nat, lt)), %(wF)s, fT, spT, {==}, {==}, {==},
            U.end_walk(%(F)s, it <> restI, dot, grammar, index, prefix, i, k, Nat.add(e, List.length(&2, Nat, lt)), fit, itemsEq,
              Equal.sym(Nat, Nat.add(e, List.length(&2, Nat, lt)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr, lt))), G.end_split(k, lr, lt)),
              Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, %(F)s)), {==})), inW)
          okRs = ihRs(True{}, False{}, [], index, prefix, dot, k, k, %(K)s, balts, restI, e, %(rdR)s)
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, %(rdT)s)
          ok_append(%(mR)s, %(mT)s, grammar, start, input, okRs, okT)
''' % {'B0': B.replace('balts', '+balts'), 'B': B, 'K': K, 'bind': seq_bind(F, B + ' <> restI'), 'fine': fine, 'wT': walkS('ts', '1n+dot', 'e'), 'steps': STEPS, 'seq': SEQ, 'F': F, 'wF': walkS(F),
       'rdR': tup(['itAt', 'itT', '{==}', 'even', 'fR', 'fine', 'spR', 'inR', '{==}', 'LP']), 'rdT': tup(['fT', 'spT', 'inT', 'itT', 'even']),
       'mR': made('rs', rounds='True{}', later='False{}'), 'mT': made('ts', later='False{}', dot='1n+dot', k='e')}
s = '''
law loop_ok:
  for items: +List<Spec.Item>
''' + TB + CTX + '''  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: %(ready)s
  for ihRs: %(ihr)s
  for ihTs: %(iht)s
  %(goal)s

def loop_ok(items, %(tba)s, %(ctxa)s, rs, ts, ready, ihRs, ihTs):
  match items:
''' % {'ready': ready('False{}', F), 'ihr': ih('rs'), 'iht': ih('ts'), 'goal': G0, 'tba': TBA, 'ctxa': CTXA}
s += loop_case('Spec.Closure{}', 'closure') + loop_case('Spec.Positive{}', 'positive')
s += absurd_cases(['Con{Spec.Brack{Spec.Closure', 'Con{Spec.Brack{Spec.Positive'], F, G0)
out.append(s)
open('b.bend', 'w').write(''.join(out))
