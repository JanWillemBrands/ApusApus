# Generate nul_sound for PROOF_TABLES.bend.
trees = {
 'Leaf': 'Spec.Leaf{kind}',
 'Node': 'Spec.Node{+q, +ch}',
 'Pick': 'Spec.Pick{+a, +ch}',
 'Skip': 'Spec.Skip{}',
 'Loop': 'Spec.Loop{+rs}',
}
items = {
 'T': 'Spec.Sym{Spec.Terminal{+k}}',
 'N': 'Spec.Sym{Spec.Nonterminal{+x}}',
 'G': 'Spec.Brack{Spec.Group{}, +alts}',
 'O': 'Spec.Brack{Spec.Optional{}, +alts}',
 'C': 'Spec.Brack{Spec.Closure{}, +alts}',
 'P': 'Spec.Brack{Spec.Positive{}, +alts}',
 'E': 'Spec.Eps{}',
}
G = 'Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, %s <> rest, [], t)) == True{} : Bool'
def absurd(item):
    return '      Empty.absurd({%s}, Lemma.false_is_not_true(fit))' % (G % item.replace('+',''))
IH_TS = 'nul_sound(ts, 1n+f, rest, grammar, t, pc, %s, %s)'
out = []
out.append('''law nul_sound:
  for forest: +List<Spec.Tree>
  for +fuel: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for empty: {Spec.leaves(forest) == [] : +List<Nat>}
  {Gll.nulOf(Gll.infoOf(fuel, Gll.MItems{}, items, [], t)) == True{} : Bool}

def nul_sound(forest, fuel, items, grammar, t, pc, fit, empty):
  match forest fuel items:
    case Nil{} 0n _:
      {==}
    case Con{t0, ts} 0n _:
      {==}
    case Nil{} 1n+(+f) Nil{}:
      {==}
    case Nil{} 1n+(+f) Con{it, rest}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, it <> rest, [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{t0, ts} 1n+(+f) Nil{}:
      Empty.absurd({Gll.nulOf(Gll.infoOf(1n+f, Gll.MItems{}, [], [], t)) == True{} : Bool}, Lemma.false_is_not_true(fit))''')
for tn, tp in trees.items():
    for iname, ip in items.items():
        head = '    case Con{%s, +ts} 1n+(+f) Con{%s, +rest}:' % (tp, ip)
        item = ip
        body = None
        if tn == 'Leaf' and iname == 'T':
            body = '      Empty.absurd({%s}, Lemma.nil_is_not_cons(kind, Spec.leaves(ts), Equal.sym(+List<Nat>, kind <> Spec.leaves(ts), [], empty)))' % (G % item.replace('+',''))
        elif tn == 'Node' and iname == 'N':
            body = '''      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      nulCh = nul_sound(ch, Gll.nestFuel(), Spec.rhsOf(grammar, q), grammar, t, pc, fitCh, append_nil_left(Spec.leaves(ch), Spec.leaves(ts), e2))
      nx = prod_nul(grammar, q, x, t, pc, lhsOk, nulCh)
      cons_nul(Gll.Info{Gll.boolAt(Gll.nulTab(t), x), Gll.lsAt(Gll.fstTab(t), x)}, Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nx,
        ''' + IH_TS % ('fitTs', 'append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)') + ')'
        elif tn == 'Pick' and iname == 'G':
            body = '''      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      nulX = alts_nul_of(f, alts, a, t, isA, g => nul_sound(ch, g, Spec.altOf(alts, a), grammar, t, pc, fitCh, append_nil_left(Spec.leaves(ch), Spec.leaves(ts), e2)))
      nh = Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Group{}, x)), Gll.nulOf(x), True{}, nul_group(x), nulX)
      cons_nul(Gll.infoBracket(Spec.Group{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nh,
        ''' + IH_TS % ('fitTs', 'append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)') + ')'
        elif tn == 'Pick' and iname == 'O':
            body = '''      +both = fit
      fitTs = Lemma.and_true_right_side(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Optional{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Optional{}, x, {==}),
        ''' + IH_TS % ('fitTs', 'append_nil_right_part(Spec.leaves(ch), Spec.leaves(ts), e2)') + ')'
        elif tn == 'Skip' and iname == 'E':
            body = '      ' + IH_TS % ('fit', 'empty')
        elif tn == 'Skip' and iname == 'O':
            body = '''      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Optional{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Optional{}, x, {==}),
        ''' + IH_TS % ('fit', 'empty') + ')'
        elif tn == 'Loop' and iname == 'C':
            body = '''      +both = fit
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      cons_nul(Gll.infoBracket(Spec.Closure{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nul_skippable(Spec.Closure{}, x, {==}),
        ''' + IH_TS % ('fitTs', 'append_nil_right_part(Spec.leaves(rs), Spec.leaves(ts), e2)') + ')'
        elif tn == 'Loop' and iname == 'P':
            body = '''      +both = fit
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      roundsP = Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), inner)
      fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), inner)
      fitTs = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      +e2 = empty
      +x = Gll.infoOf(f, Gll.MAlts{}, [], alts, t)
      nulRs = nul_sound(rs, 1n+f, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), grammar, t, pc, fitRs, append_nil_left(Spec.leaves(rs), Spec.leaves(ts), e2))
      nulX = positive_nul(rs, f, alts, t, roundsP, nulRs)
      nh = Equal.trans(Bool, Gll.nulOf(Gll.infoBracket(Spec.Positive{}, x)), Gll.nulOf(x), True{}, nul_positive(x), nulX)
      cons_nul(Gll.infoBracket(Spec.Positive{}, x), Gll.infoOf(1n+f, Gll.MItems{}, rest, [], t), nh,
        ''' + IH_TS % ('fitTs', 'append_nil_right_part(Spec.leaves(rs), Spec.leaves(ts), e2)') + ')'
        else:
            body = absurd(item)
        out.append(head + '\n' + body)
open('nul.bend', 'w').write('\n'.join(out) + '\n')
