RHS = 'Spec.rhsOf(grammar, index)'
out = ['''
# ======== SEQUENCES OF A GRAMMAR WITHOUT BRACKETS ========

def itemOr(m: Maybe<&2, Spec.Item>, +d: Spec.Item) -> Spec.Item:
  match m:
    case Some{x}:
      x
    case None{}:
      d

law nth_drop:
  for seq: +List<Spec.Item>
  for n: Nat
  for +y: Spec.Item
  for +e: {Gll.nthItem(seq, n) == Some{y} : Maybe<&2, Spec.Item>}
  {Gll.dropFrom(n, seq) == y <> Gll.dropFrom(1n+n, seq) : +List<Spec.Item>}

def nth_drop(seq, n, y, e):
  match seq n:
    case Nil{} _:
      Empty.absurd({Gll.dropFrom(n, []) == y <> Gll.dropFrom(1n+n, []) : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{y}, e)))
    case Con{+x, +rest} 0n:
      Equal.cong(Spec.Item, +List<Spec.Item>, v => v <> rest, x, y, Equal.cong(Maybe<&2, Spec.Item>, Spec.Item, v => itemOr(v, x), Some{x}, Some{y}, e))
    case Con{x, +rest} 1n+(+m):
      nth_drop(rest, m, y, e)

law nth_none_drop:
  for seq: +List<Spec.Item>
  for n: Nat
  for +e: {Gll.nthItem(seq, n) == None{} : Maybe<&2, Spec.Item>}
  {Gll.dropFrom(n, seq) == [] : +List<Spec.Item>}

def nth_none_drop(seq, n, e):
  match seq n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      {==}
    case Con{+x, +rest} 0n:
      Empty.absurd({x <> rest == [] : +List<Spec.Item>}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), Some{x}, None{}, e)))
    case Con{x, +rest} 1n+(+m):
      nth_none_drop(rest, m, e)

law plain_items:
  for items: +List<Spec.Item>
  for n: Nat
  for +kd: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +plain: {PS.itemsPlain(items) == True{} : Bool}
  for +e: {Gll.nthItem(items, n) == Some{Spec.Brack{kd, alts}} : Maybe<&2, Spec.Item>}
  Empty

def plain_items(items, n, kd, alts, plain, e):
  match items n:
    case Nil{} _:
      Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Brack{k2, a2}, rest} _:
      Lemma.false_is_not_true(plain)
    case Con{Spec.Sym{+s}, +rest} 0n:
      Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackOf(v), Some{Spec.Sym{s}}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Sym{s}, +rest} 1n+(+m):
      plain_items(rest, m, kd, alts, plain, e)
    case Con{Spec.Eps{}, +rest} 0n:
      Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackOf(v), Some{Spec.Eps{}}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Eps{}, +rest} 1n+(+m):
      plain_items(rest, m, kd, alts, plain, e)

law plain_rhs:
  for grammar: +List<Spec.Production>
  for index: Nat
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  {PS.itemsPlain(Spec.rhsOf(grammar, index)) == True{} : Bool}

def plain_rhs(grammar, index, plain):
  match grammar index:
    case Nil{} _:
      {==}
    case Con{Spec.Production{lhs, +rhs}, +rest} 0n:
      Lemma.and_true_left(PS.itemsPlain(rhs), PS.withoutBrackets(rest), plain)
    case Con{Spec.Production{lhs, +rhs}, +rest} 1n+(+m):
      plain_rhs(rest, m, Lemma.and_true_right_side(PS.itemsPlain(rhs), PS.withoutBrackets(rest), plain))
''']
out[0] = out[0].replace("law plain_items:", '''def isBrackOf(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{Spec.Brack{kd, alts}}:
      True{}
    case _:
      False{}

law plain_items:''')

FIXD = '''  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
'''
FIX = 'grammar, input, root'
head = '''
# ======== WHAT A DESCRIPTOR ON THE TREE GIVES ========

law empty_on:
  for dot: Nat
''' + FIXD + '''  for +index: Nat
  for +k: Nat
  for +i: Nat
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  AllOn(grammar, input, root, Support.emptyStep(dot, index, [], k, i))

def empty_on(dot, grammar, input, root, index, k, i, inF):
  match dot:
    case 0n:
      (Lemma.and_true_left(Spec.bsrMember(Spec.at(index, [], 0n, k, i, i), Spec.steps(root, 0n)), True{}, inF), {==})
    case 1n+d:
      {==}

law item_on:
  for it: Maybe<&2, Spec.Item>
  for f: +List<Spec.Tree>
''' + FIXD + '''  for +pr: Gll.Pred
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +x: Nat
  for +g: +List<Spec.Tree>
  for +lhs: {Spec.lhsIs(grammar, index, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, index, k, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, %s)) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +itEq: {Gll.nthItem(%s, dot) == it : Maybe<&2, Spec.Item>}
  AllOn(grammar, input, root, PS.itemGives(it, pr, grammar, input, index, [], dot, k, i))

def item_on(it, f, %s, pr, plain, index, dot, k, i, x, g, lhs, node, fitF, spF, inF, finF, itEq):
  match it f:
''' % (RHS, RHS, FIX)
ITEMS = [('T', 'Some{Spec.Sym{Spec.Terminal{+tm}}}', 'Spec.Sym{Spec.Terminal{tm}}'), ('N', 'Some{Spec.Sym{Spec.Nonterminal{+y}}}', 'Spec.Sym{Spec.Nonterminal{y}}'),
         ('E', 'Some{Spec.Eps{}}', 'Spec.Eps{}'), ('B', 'Some{Spec.Brack{+kd, +alts}}', 'Spec.Brack{kd, alts}'), ('Z', 'None{}', None)]
TREES = [('Nil', 'Nil{}', '[]'), ('Leaf', 'Con{Spec.Leaf{+a}, +ts}', 'Spec.Leaf{a} <> ts'), ('Node', 'Con{Spec.Node{+q, +ch}, +ts}', 'Spec.Node{q, ch} <> ts'),
         ('Pick', 'Con{Spec.Pick{+a, +ch}, +ts}', 'Spec.Pick{a, ch} <> ts'), ('Skip', 'Con{Spec.Skip{}, +ts}', 'Spec.Skip{} <> ts'), ('Loop', 'Con{Spec.Loop{+rs}, +ts}', 'Spec.Loop{rs} <> ts')]
REAL = {('T', 'Leaf'), ('N', 'Node'), ('E', 'Skip'), ('Z', 'Nil')}
def goal(itexpr, fexpr):
    return 'AllOn(grammar, input, root, PS.itemGives(%s, pr, grammar, input, index, [], dot, k, i))' % itexpr
def fit_moved(item, fexpr):
    rest = 'Gll.dropFrom(1n+dot, %s)' % RHS
    return '''      +dEq = nth_drop(%(rhs)s, dot, %(it)s, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(%(f)s, grammar, %(it)s <> %(rest)s), Spec.fits(%(f)s, grammar, Gll.dropFrom(dot, %(rhs)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%(f)s, grammar, v), %(it)s <> %(rest)s, Gll.dropFrom(dot, %(rhs)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %(rhs)s), %(it)s <> %(rest)s, dEq)), fitF)
''' % {'rhs': RHS, 'it': item, 'f': fexpr, 'rest': rest}
REST = 'Gll.dropFrom(1n+dot, %s)' % RHS
def desc_at(d, f, fitT, spT, inT, finT):
    return '(x, (g, (%s, (lhs, (node, (%s, (%s, (%s, %s))))))))' % (f, fitT, spT, inT, finT)
s = head
for ik, ipat, iexpr in ITEMS:
    itx = 'Some{%s}' % iexpr if iexpr else 'None{}'
    for tk, tpat, texpr in TREES:
        s += '    case %s %s:\n' % (ipat, tpat)
        if ik == 'B':
            s += '      Empty.absurd(%s, plain_items(%s, dot, kd, alts, plain_rhs(grammar, index, plain), itEq))\n' % (goal(itx, texpr), RHS)
            continue
        if ik == 'Z':
            if tk == 'Nil':
                s += '''      +lhsIdx = Equal.trans(Bool, Spec.lhsIs(grammar, index, Gll.lhsOf(grammar, index)), Spec.lhsIs(grammar, index, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, index, v), Gll.lhsOf(grammar, index), x, G.lhs_of_is(grammar, index, x, lhs)), lhs)
      +endEq = Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
      ((index, (g, (lhsIdx, (node, endEq)))), empty_on(dot, grammar, input, root, index, k, i, inF))
'''
            else:
                s += '''      +dNil = nth_none_drop(%s, dot, itEq)
      Empty.absurd(%s, Fits.fits_cons_nil(%s, %s, grammar, Equal.trans(Bool, Spec.fits(%s, grammar, []), Spec.fits(%s, grammar, Gll.dropFrom(dot, %s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%s, grammar, v), [], Gll.dropFrom(dot, %s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, %s), [], dNil)), fitF)))
''' % (RHS, goal(itx, texpr), texpr.split(' <> ')[0], 'ts', texpr, texpr, RHS, texpr, RHS, RHS)
            continue
        s += fit_moved(iexpr, texpr)
        if (ik, tk) not in REAL:
            s += '      Empty.absurd(%s, Lemma.false_is_not_true(fitF2))\n' % goal(itx, texpr)
            continue
        if ik == 'T':
            d1 = 'Gll.Desc{index, [], 1n+dot, k, 1n+i}'
            y1 = 'Gll.stepAt(index, [], 1n+dot, k, i, 1n+i)'
            s += '''      +fitT = Fits.fits_tail(Spec.Leaf{a}, ts, grammar, %(it)s, %(rest)s, fitF2)
      +lts = List.length(&2, Nat, Spec.leaves(ts))
      +spT = G.leaf_rest(input, i, a, Spec.leaves(ts), spF)
      +here = Spec.at(index, [], 1n+dot, k, i, 1n+i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, 1n+i)
      +inT = all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, 1n+Nat.add(i, lts), Nat.add(i, 1n+lts), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Equal.sym(Nat, Nat.add(i, 1n+lts), 1n+Nat.add(i, lts), Lemma.add_succ_right(i, lts)), finF)
      on_when(Gll.tokenIs(List.get(&2, Nat, input, i), tm), PS.pairWhen(pr, grammar, input, %(d)s, %(y)s), %(fix)s,
        on_when(Gll.admits(pr, grammar, input, %(d)s), [Support.FactDescriptor{%(d)s}, Support.FactStep{%(y)s}], %(fix)s, (%(da)s, (onS, {==}))))
''' % {'it': iexpr, 'rest': REST, 'd': d1, 'y': y1, 'fix': FIX, 'da': desc_at(d1, 'ts', 'fitT', 'spT', 'inT', 'finT')}
        elif ik == 'E':
            d1 = 'Gll.Desc{index, [], 1n+dot, k, i}'
            y1 = 'Gll.stepAt(index, [], 1n+dot, k, i, i)'
            s += '''      +here = Spec.at(index, [], 1n+dot, k, i, i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, i)
      +inT = all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      on_when(Gll.admits(pr, grammar, input, %(d)s), [Support.FactDescriptor{%(d)s}, Support.FactStep{%(y)s}], %(fix)s, (%(da)s, (onS, {==})))
''' % {'d': d1, 'y': y1, 'fix': FIX, 'da': desc_at(d1, 'ts', 'fitF2', 'spF', 'inT', 'finF')}
        elif ik == 'N':
            s += '''      +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, %(rest)s), fitF2)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +lch = Spec.leaves(ch)
      +e = Nat.add(i, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, i, lch, Spec.leaves(ts), spF)
      +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, e)
      +inCh = all_in_left_n(wCh, wT, Spec.steps(root, 0n), all_in_tail_n(Spec.at(index, [], 1n+dot, k, i, e), List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF))
      ((q, (ch, (lhsQ, (fitCh, (spCh, inCh))))), ((%(da)s, itEq), {==}))
''' % {'rest': REST, 'da': desc_at(None, texpr, 'fitF', 'spF', 'inF', 'finF')}
out.append(s)
# all_in helpers (local names, the generic ones are in PROOF_UNAMBIGUOUS)
out.insert(1, '''
law all_in_tail_n:
  for +x: Spec.Bsr
  for +xs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(x <> xs, set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_tail_n(x, xs, set, h):
  U.all_in_tail(x, xs, set, h)

law all_in_left_n:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_left_n(xs, ys, set, h):
  U.all_in_left(xs, ys, set, h)

law all_in_right_n:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(ys, set) == True{} : Bool}

def all_in_right_n(xs, ys, set, h):
  U.all_in_right(xs, ys, set, h)
''')
open('n4.bend', 'w').write(''.join(out))
