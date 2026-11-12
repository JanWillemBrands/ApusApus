trees = {'Leaf': 'Spec.Leaf{+kind}', 'Node': 'Spec.Node{+q, +ch}', 'Pick': 'Spec.Pick{+a, +ch}', 'Skip': 'Spec.Skip{}', 'Loop': 'Spec.Loop{+rs}'}
items = {'T': 'Spec.Sym{Spec.Terminal{+k}}', 'N': 'Spec.Sym{Spec.Nonterminal{+x}}', 'G': 'Spec.Brack{Spec.Group{}, +alts}',
 'O': 'Spec.Brack{Spec.Optional{}, +alts}', 'C': 'Spec.Brack{Spec.Closure{}, +alts}', 'P': 'Spec.Brack{Spec.Positive{}, +alts}', 'E': 'Spec.Eps{}'}
TOK = 'Some{k0}'
def G(item): return '{Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, %s <> rest, [], t))) == True{} : Bool}' % item.replace('+','')
REST = 'Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t)'
def ihts(fitTs, lvTs): return 'first_sound(ts, 1n+f, rest, grammar, t, pc, %s, k0, w, %s)' % (fitTs, lvTs)
out = ['''law first_sound:
  for forest: +List<Spec.Tree>
  for +fuel: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +k0: Nat
  for +w: +List<Nat>
  for +lv: {Spec.leaves(forest) == k0 <> w : +List<Nat>}
  {Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(fuel, Gll.MItems{}, items, [], t))) == True{} : Bool}

def first_sound(forest, fuel, items, grammar, t, pc, fit, k0, w, lv):
  match forest fuel items:
    case Nil{} 0n _:
      {==}
    case Con{t0, ts} 0n _:
      {==}
    case Nil{} 1n+(+f) Nil{}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t))) == True{} : Bool}, Lemma.nil_is_not_cons(k0, w, lv))
    case Nil{} 1n+(+f) Con{it, rest}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, it <> rest, [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{t0, ts} 1n+(+f) Nil{}:
      Empty.absurd({Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t))) == True{} : Bool}, Lemma.false_is_not_true(fit))''']
for tn, tp in trees.items():
    for iname, ip in items.items():
        head = '    case Con{%s, +ts} 1n+(+f) Con{%s, +rest}:' % (tp, ip)
        g = G(ip)
        body = '      Empty.absurd(%s, Lemma.false_is_not_true(fit))' % g
        if tn == 'Leaf' and iname == 'T':
            body = '''      isK = Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), fit)
      +ek = cons_head_eq(kind, Spec.leaves(ts), k0, w, lv)
      eq = Equal.trans(Bool, Nat.is_eq(k0, k), Nat.is_eq(kind, k), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(v, k), k0, kind, Equal.sym(Nat, kind, k0, ek)), isK)
      Lemma.or_true_left_intro(Nat.is_eq(k0, k), False{}, eq)'''
        elif tn == 'Node' and iname == 'N':
            body = '''      +inner = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), fit)
      +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), fit)
      +h = {Gll.Info{Gll.boolAt(Gll.nulTab(t), x), Gll.lsAt(Gll.fstTab(t), x)} : Gll.Info}
      first_split(Spec.leaves(ch), Spec.leaves(ts), k0, w, %s, lv,
        eqCh => cons_first_left(h, %s, Some{k0}, prod_first(grammar, q, x, t, pc, lhsOk, Some{k0}, first_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, k0, tailOf(Spec.leaves(ch)), eqCh))),
        eqNil => eqTs => cons_first_right(h, %s, Some{k0}, prod_nul(grammar, q, x, t, pc, lhsOk, nul_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, eqNil)), %s))''' % (g, REST, REST, ihts('fitTs', 'eqTs'))
        elif tn == 'Pick' and iname in 'GO':
            kind = 'Spec.Group{}' if iname == 'G' else 'Spec.Optional{}'
            if iname == 'G':
                parts = '''      +inner = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), fit)
      +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), fit)'''
                nullh = 'Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Group{}, x)), Gll.nulOf(x), True{}, nul_group(x), alts_nul_of(f, alts, a, t, isA, g => nul_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, eqNil)))'
            else:
                parts = '''      +optP = Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +inner = Lemma.and_true_left(optP, Spec.fits(ts, grammar, rest), fit)
      +inner2 = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +isA = Lemma.and_true_right_side(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), inner2)
      +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      +fitTs = Lemma.and_true_right_side(optP, Spec.fits(ts, grammar, rest), fit)'''
                nullh = 'nul_skippable(Spec.Optional{}, x, {==})'
            body = parts + '''
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(%s, x)
      first_split(Spec.leaves(ch), Spec.leaves(ts), k0, w, %s, lv,
        eqCh => cons_first_left(h, %s, Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(%s, x)), alts_first_of(f, alts, a, t, Some{k0}, isA, g => first_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, k0, tailOf(Spec.leaves(ch)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, %s, Some{k0}, %s, %s))''' % (kind, g, REST, kind, REST, nullh, ihts('fitTs', 'eqTs'))
        elif tn == 'Skip' and iname == 'E':
            body = '      ' + ihts('fit', 'lv')
        elif tn == 'Skip' and iname == 'O':
            body = '''      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_first_right(Gll.infoBracket(Spec.Optional{}, x), %s, Some{k0}, nul_skippable(Spec.Optional{}, x, {==}), %s)''' % (REST, ihts('fit', 'lv'))
        elif tn == 'Loop' and iname in 'CP':
            kind = 'Spec.Closure{}' if iname == 'C' else 'Spec.Positive{}'
            if iname == 'C':
                nullh = 'nul_skippable(Spec.Closure{}, x, {==})'
            else:
                nullh = 'Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Positive{}, x)), Gll.nulOf(x), True{}, nul_positive(x), positive_nul(rs, f, alts, t, roundsP, nul_sound(rs, 1n+f, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), grammar, t, pc, fitRs, eqNil)))'
            body = '''      +tms = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(%s, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +roundsP = Lemma.and_true_left(Spec.roundsOk(%s, rs), Spec.fits(rs, grammar, tms), inner)
      +fitRs = Lemma.and_true_right_side(Spec.roundsOk(%s, rs), Spec.fits(rs, grammar, tms), inner)
      +fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(%s, rs), Spec.fits(rs, grammar, tms)), Spec.fits(ts, grammar, rest), fit)
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      +h = Gll.infoBracket(%s, x)
      first_split(Spec.leaves(rs), Spec.leaves(ts), k0, w, %s, lv,
        eqCh => cons_first_left(h, %s, Some{k0}, Equal.trans(Bool, Gll.lsHas(Some{k0}, Gll.firstOf(h)), Gll.lsHas(Some{k0}, Gll.firstOf(x)), True{}, Equal.cong(Gll.LSet, Bool, v => Gll.lsHas(Some{k0}, v), Gll.firstOf(h), Gll.firstOf(x), first_bracket(%s, x)), times_first(List.length(&2, Spec.Tree, rs), f, alts, t, Some{k0}, first_sound(rs, 1n+f, tms, grammar, t, pc, fitRs, k0, tailOf(Spec.leaves(rs)), eqCh)))),
        eqNil => eqTs => cons_first_right(h, %s, Some{k0}, %s, %s))''' % (kind, kind, kind, kind, kind, g, REST, kind, REST, nullh, ihts('fitTs', 'eqTs'))
        out.append(head + '\n' + body)
open('first.bend', 'w').write('\n'.join(out).replace('(eqNil, eqTs) =>', 'eqNil => eqTs =>') + '\n')
