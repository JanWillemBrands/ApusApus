S = 'Spec.sequenceAt(grammar, index, prefix)'
LEN = 'List.length(&2, Spec.Item, %s)' % S
def tgt(K, fin): return 'Spec.at(index, prefix, %s, i, %s, %s)' % (LEN, K, fin)
out = ['''
# ======== THE END STEP OF A SEQUENCE ========

# The walk of a sequence has the step of its last slot, ending where the forest ends.
def EndAt(+grammar: +List<Spec.Production>, +index: Nat, +prefix: +List<Nat>, +i: Nat, +fin: Nat, +ws: +List<Spec.Bsr>) -> Type:
  &K: Nat -> {Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, K, fin), ws) == True{} : Bool}

law fits_nil_items:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for e: {Spec.fits([], grammar, items) == True{} : Bool}
  {items == [] : +List<Spec.Item>}

def fits_nil_items(items, grammar, e):
  match items:
    case Nil{}:
      {==}
    case Con{it, rest}:
      Empty.absurd({it <> rest == [] : +List<Spec.Item>}, Lemma.false_is_not_true(e))

# The head step is the end step: the sequence has dot + 1 items and the forest ends at e.
law end_here:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +fin: Nat
  for +ws: +List<Spec.Bsr>
  for +lenEq: {%s == 1n+dot : Nat}
  for +finE: {fin == e : Nat}
  EndAt(grammar, index, prefix, i, fin, Spec.at(index, prefix, 1n+dot, i, k, e) <> ws)

def end_here(grammar, index, prefix, dot, i, k, e, fin, ws, lenEq, finE):
  +here = Spec.at(index, prefix, 1n+dot, i, k, e)
  (k, Equal.trans(Bool, Spec.bsrMember(%s, here <> ws), Spec.bsrMember(here, here <> ws), True{},
    Equal.trans(Bool, Spec.bsrMember(%s, here <> ws), Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, fin), here <> ws), Spec.bsrMember(here, here <> ws),
      Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, k, fin), here <> ws), %s, 1n+dot, lenEq),
      Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, v), here <> ws), fin, e, finE)),
    R.bsr_member_head(here, ws)))

# The end step is later: it is in the tail's walk.
law end_later:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +fin: Nat
  for +h: Spec.Bsr
  for +pre: +List<Spec.Bsr>
  for +ws: +List<Spec.Bsr>
  for got: EndAt(grammar, index, prefix, i, fin, ws)
  EndAt(grammar, index, prefix, i, fin, h <> List.append(&2, Spec.Bsr, pre, ws))

def end_later(grammar, index, prefix, i, fin, h, pre, ws, got):
  match got:
    case (K0, m):
      +K = {K0 : Nat}
      (K, R.bsr_member_cons(%s, h, List.append(&2, Spec.Bsr, pre, ws), Sub.member_app_right(pre, ws, %s, m)))
''' % (LEN, tgt('k', 'fin'), tgt('k', 'fin'), LEN, tgt('K', 'fin'), tgt('K', 'fin'))]

law = '''law end_walk:
  for forest: +List<Spec.Tree>
  for items: +List<Spec.Item>
  for +dot: Nat
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +fin: Nat
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, %s) == items : +List<Spec.Item>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ok: {Bool.or(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, forest))) == True{} : Bool}
  EndAt(grammar, index, prefix, i, fin, Spec.walk(forest, False{}, index, prefix, dot, i, k))

def end_walk(forest, items, dot, grammar, index, prefix, i, k, fin, fit, itemsEq, finEq, ok):
  match forest items dot:
    case Nil{} _ 0n:
      +none = fits_nil_items(items, grammar, fit)
      +lenEq = items_from_none(%s, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(0n, %s), items, [], itemsEq, none))
      +here = Spec.at(index, prefix, 0n, i, k, k)
      +finK = Equal.trans(Nat, fin, Nat.add(k, 0n), k, Equal.sym(Nat, Nat.add(k, 0n), fin, finEq), Lemma.add_zero_right(k))
      (k, Equal.trans(Bool, Spec.bsrMember(%s, [here]), Spec.bsrMember(here, [here]), True{},
        Equal.trans(Bool, Spec.bsrMember(%s, [here]), Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, fin), [here]), Spec.bsrMember(here, [here]),
          Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, k, fin), [here]), %s, 0n, lenEq),
          Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, v), [here]), fin, k, finK)),
        R.bsr_member_head(here, [])))
    case Nil{} _ 1n+d:
      Empty.absurd(EndAt(grammar, index, prefix, i, fin, []), Lemma.false_is_not_true(ok))
    case Con{t, ts} Nil{} _:
      Empty.absurd(EndAt(grammar, index, prefix, i, fin, Spec.walk(t <> ts, False{}, index, prefix, dot, i, k)), Fits.fits_cons_nil(t, ts, grammar, fit))
''' % (S, S, S, tgt('k', 'fin'), tgt('k', 'fin'), LEN)
# shapes: (pattern, tree expr, head end e, tail walk prefix list or None, leaves-of-head expr)
SH = [
 ('Spec.Leaf{+kind}', 'Spec.Leaf{kind}', '1n+k', None, None),
 ('Spec.Node{+q, +ch}', 'Spec.Node{q, ch}', 'Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))', 'Spec.walk(ch, False{}, q, [], 0n, k, k)', 'ch'),
 ('Spec.Pick{+a, +ch}', 'Spec.Pick{a, ch}', 'Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))', 'Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)', 'ch'),
 ('Spec.Skip{}', 'Spec.Skip{}', 'k', None, None),
 ('Spec.Loop{+rs}', 'Spec.Loop{rs}', 'Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))', 'Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)', 'rs'),
]
cases = []
for pat, tr, e, pre, sub in SH:
    common = '''      +ftail = Fits.fits_tail(%s, TS, grammar, it, rest, fit)
      +restEq = items_from_tail(dot, %s, it, rest, itemsEq)
''' % (tr, S)
    # ts = Nil
    if pat.startswith('Spec.Leaf'):
        finE = 'Equal.trans(Nat, fin, Nat.add(k, 1n), 1n+k, Equal.sym(Nat, Nat.add(k, 1n), fin, finEq), Lemma.add_one_right(k))'
    elif pat.startswith('Spec.Skip'):
        finE = 'Equal.trans(Nat, fin, Nat.add(k, 0n), k, Equal.sym(Nat, Nat.add(k, 0n), fin, finEq), Lemma.add_zero_right(k))'
    else:
        finE = 'Equal.trans(Nat, fin, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(%s), []))), %s, Equal.sym(Nat, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(%s), []))), fin, finEq), Equal.sym(Nat, %s, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(%s), []))), G.end_alone(k, Spec.leaves(%s))))' % (sub, e, sub, e, sub, sub)
    ws_nil = 'Spec.walk([], False{}, index, prefix, 1n+dot, i, %s)' % e
    if pre: ws_nil = 'List.append(&2, Spec.Bsr, %s, %s)' % (pre, ws_nil)
    c = '    case Con{%s, Nil{}} Con{+it, +rest} _:\n' % pat + common.replace('TS', '[]') + '''      +restNil = fits_nil_items(rest, grammar, ftail)
      +lenEq = items_from_last(dot, %s, it, Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, %s), it <> rest, [it], itemsEq, Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => it <> v, rest, [], restNil)))
      end_here(grammar, index, prefix, dot, i, k, %s, fin, %s, lenEq, %s)
''' % (S, S, e, ws_nil, finE)
    cases.append(c)
    # ts = Con
    ts = 't2 <> ts2'
    if pat.startswith('Spec.Leaf'):
        finT = 'Equal.trans(Nat, Nat.add(1n+k, List.length(&2, Nat, Spec.leaves(%s))), Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(%s))), fin, Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(%s))), 1n+Nat.add(k, List.length(&2, Nat, Spec.leaves(%s))), Lemma.add_succ_right(k, List.length(&2, Nat, Spec.leaves(%s)))), finEq)' % ((ts,)*5)
    elif pat.startswith('Spec.Skip'):
        finT = 'finEq'
    else:
        finT = 'Equal.trans(Nat, Nat.add(%s, List.length(&2, Nat, Spec.leaves(%s))), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(%s), Spec.leaves(%s)))), fin, G.end_split(k, Spec.leaves(%s), Spec.leaves(%s)), finEq)' % (e, ts, sub, ts, sub, ts)
    rec = 'end_walk(%s, rest, 1n+dot, grammar, index, prefix, i, %s, fin, ftail, restEq, %s, {==})' % (ts, e, finT)
    here = 'Spec.at(index, prefix, 1n+dot, i, k, %s)' % e
    tailw = 'Spec.walk(%s, False{}, index, prefix, 1n+dot, i, %s)' % (ts, e)
    c = '    case Con{%s, Con{+t2, +ts2}} Con{+it, +rest} _:\n' % pat + common.replace('TS', ts) + '      end_later(grammar, index, prefix, i, fin, %s, %s, %s, %s)\n' % (here, pre if pre else '[]', tailw, rec)
    cases.append(c)
out.append(law + ''.join(cases))
open('p2.bend', 'w').write('\n'.join(out))
