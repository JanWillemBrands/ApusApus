# Generates the side-by-side comparison of PROOF_UNAMBIGUOUS.bend.
FIXD = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Spec.Tree
  for +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}
  for +root2: Spec.Tree
  for +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}
'''
FIX = 'grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2'
POSD = '''  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +after: Bool
  for +E1: Nat
  for +E2: Nat
'''
POS = 'index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2'
S = 'Spec.sequenceAt(grammar, index, prefix)'
def ST(j): return 'Spec.steps(root%d, 0n)' % j
def W(f, i, k, d, pre='prefix'): return 'Spec.walk(%s, False{}, index, %s, %s, %s, %s)' % (f, pre, d, i, k)
def SAME(f1, f2): return 'Same(grammar, start, %s, %s)' % (f1, f2)
DUMMY = 'Spec.Group{}, [], [], False{}, 0n, 0n'
def ready8(*a): return '(%s, (%s, (%s, (%s, (%s, (%s, (%s, %s)))))))' % a
def ready16(*a): return '(' + ', ('.join(a[:-1]) + ', ' + a[-1] + ')' * 15
SEQF = '(fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even)))))))'
SEQFD = '''  for +fit1: {Spec.fits(F1, grammar, ITEMS) == True{} : Bool}
  for +fit2: {Spec.fits(F2, grammar, ITEMS) == True{} : Bool}
  for +sp1: G.Spells(F1, input, k)
  for +sp2: G.Spells(F2, input, k)
  for +in1: {Spec.allIn(Spec.walk(F1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(F2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itemsEq: {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == ITEMS : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
'''
SEQA = 'fit1, fit2, sp1, sp2, in1, in2, itemsEq, even'
def ihd(name, f): return '  for %s: CmpIH(grammar, start, input, root1, rootFit1, rootSp1, root2, rootFit2, rootSp2, %s)\n' % (name, f)
def ih(name, rounds, f2, items, index, prefix, dot, i1, i2, k, rest, ready):
    return '%s(%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)' % (name, rounds, f2, items, index, prefix, dot, i1, i2, k, rest, ready)
def cong(T, U, lam, a, b, e): return 'Equal.cong(%s, %s, %s, %s, %s, %s)' % (T, U, lam, a, b, e)
def trans(T, a, b, c, e1, e2): return 'Equal.trans(%s, %s, %s, %s, %s, %s)' % (T, a, b, c, e1, e2)
def sym(T, a, b, e): return 'Equal.sym(%s, %s, %s, %s)' % (T, a, b, e)
LT = '+List<Spec.Tree>'

out = []
out.append('''
# ======== THE COMPARISON ========

# How the rounds of a loop must consume: all of them, except the first round of < >.
def roundsFine(kind: Spec.Bracket, after: Bool, +rounds: +List<Spec.Tree>) -> Bool:
  match kind after:
    case Spec.Positive{} False{}:
      Spec.roundsOk(Spec.Positive{}, rounds)
    case _ _:
      Spec.allConsume(rounds)

# What the comparison knows of the two forests. In a sequence: both fit the items from the
# dot, spell the input from k, and walk inside their root's steps. In the rounds of a loop
# (the bracket at the dot): both are rounds of its body from k, consume as they must, end
# at E1 and E2, and leaving the loop there predicts the token there.
def CmpReady(rounds: Bool, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root1: Spec.Tree, +root2: Spec.Tree, +f1: +List<Spec.Tree>, +f2: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i1: Nat, +i2: Nat, +k: Nat, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +restO: +List<Spec.Item>, +after: Bool, +E1: Nat, +E2: Nat) -> Type:
  match rounds:
    case False{}:
      {Spec.fits(f1, grammar, items) == True{} : Bool} & {Spec.fits(f2, grammar, items) == True{} : Bool} & G.Spells(f1, input, k) & G.Spells(f2, input, k) &
        {Spec.allIn(Spec.walk(f1, False{}, index, prefix, dot, i1, k), Spec.steps(root1, 0n)) == True{} : Bool} & {Spec.allIn(Spec.walk(f2, False{}, index, prefix, dot, i2, k), Spec.steps(root2, 0n)) == True{} : Bool} &
        {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == items : +List<Spec.Item>} & {L.evenLength(prefix) == True{} : Bool}
    case True{}:
      {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>} &
        {Gll.isLoop(kind) == True{} : Bool} & {L.evenLength(prefix) == True{} : Bool} &
        {Spec.fits(f1, grammar, Spec.times(List.length(&2, Spec.Tree, f1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.fits(f2, grammar, Spec.times(List.length(&2, Spec.Tree, f2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} &
        {roundsFine(kind, after, f1) == True{} : Bool} & {roundsFine(kind, after, f2) == True{} : Bool} &
        G.Spells(f1, input, k) & G.Spells(f2, input, k) &
        {Spec.allIn(Spec.walk(f1, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool} & {Spec.allIn(Spec.walk(f2, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool} &
        {Nat.add(k, List.length(&2, Nat, Spec.leaves(f1))) == E1 : Nat} & {Nat.add(k, List.length(&2, Nat, Spec.leaves(f2))) == E2 : Nat} &
        Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1)) & Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))

def CmpIH(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root1: Spec.Tree, +rootFit1: {Spec.fits([root1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp1: {Spec.leaves([root1]) == input : +List<Nat>}, +root2: Spec.Tree, +rootFit2: {Spec.fits([root2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp2: {Spec.leaves([root2]) == input : +List<Nat>}, +f1: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @f2: +List<Spec.Tree> -> @items: +List<Spec.Item> -> @index: Nat -> @prefix: +List<Nat> -> @dot: Nat -> @i1: Nat -> @i2: Nat -> @k: Nat -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @restO: +List<Spec.Item> -> @after: Bool -> @E1: Nat -> @E2: Nat ->
    CmpReady(rounds, grammar, start, input, root1, root2, f1, f2, items, index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2) -> Same(grammar, start, f1, f2)
''')

def seq_law(name, comment, treeD, itemD, F1, F2, ITEMS, extraD, ihs, params, body):
    s = '# %s\nlaw %s:\n' % (comment, name) + FIXD + POSD + treeD + itemD + SEQFD.replace('F1', F1).replace('F2', F2).replace('ITEMS', ITEMS) + extraD
    for n, f in ihs: s += ihd(n, f)
    extra = [l.split(':')[0].split()[-1].lstrip('+') for l in extraD.split('\n') if l.strip()]
    names = [FIX, POS] + [x.strip() for x in params.split(',') if x.strip()] + [SEQA] + extra + [n for n, f in ihs]
    s += '  %s\n\ndef %s(%s):\n' % (SAME(F1, F2), name, ', '.join(names))
    return s + body + '\n'

# ---- tokens ----
F1 = 'Spec.Leaf{a1} <> ts1'; F2 = 'Spec.Leaf{a2} <> ts2'
IT = 'Spec.Sym{Spec.Terminal{term}} <> restI'
body = '''  +tok1 = G.leaf_token(input, k, a1, Spec.leaves(ts1), sp1)
  +tok2 = G.leaf_token(input, k, a2, Spec.leaves(ts2), sp2)
  +ae = Lemma.some_injective(a1, a2, %s)
  +itT = items_from_tail(dot, %s, Spec.Sym{Spec.Terminal{term}}, restI, itemsEq)
  then_same(grammar, start, ts1, ts2, %s, %s,
    %s,
    tse => %s)
''' % (trans('Maybe<&2, Nat>', 'Some{a1}', 'List.get(&2, Nat, input, k)', 'Some{a2}', sym('Maybe<&2, Nat>', 'List.get(&2, Nat, input, k)', 'Some{a1}', 'tok1'), 'tok2'), S, F1, F2,
   ih('ihTs', 'False{}', 'ts2', 'restI', 'index', 'prefix', '1n+dot', 'i1', 'i2', '1n+k', 'kind, alts, restO, after, E1, E2',
      ready8('Fits.fits_tail(Spec.Leaf{a1}, ts1, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit1)', 'Fits.fits_tail(Spec.Leaf{a2}, ts2, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit2)',
             'G.leaf_rest(input, k, a1, Spec.leaves(ts1), sp1)', 'G.leaf_rest(input, k, a2, Spec.leaves(ts2), sp2)',
             'all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, 1n+k), %s, %s, in1)' % (W('ts1', 'i1', '1n+k', '1n+dot'), ST(1)),
             'all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, 1n+k), %s, %s, in2)' % (W('ts2', 'i2', '1n+k', '1n+dot'), ST(2)), 'itT', 'even')),
   trans(LT, F1, 'Spec.Leaf{a2} <> ts1', F2, cong('Nat', LT, 'v => Spec.Leaf{v} <> ts1', 'a1', 'a2', 'ae'), cong(LT, LT, 'v => Spec.Leaf{a2} <> v', 'ts1', 'ts2', 'tse')))
out.append(seq_law('leaf_leaf', 'Two tokens: the same token, then the rest.', '  for +a1: Nat\n  for +ts1: +List<Spec.Tree>\n  for +a2: Nat\n  for +ts2: +List<Spec.Tree>\n', '  for +term: Nat\n  for +restI: +List<Spec.Item>\n', F1, F2, IT, '', [('ihTs', 'ts1')], 'a1, ts1, a2, ts2, term, restI, ', body))

# ---- skips ----
F1 = 'Spec.Skip{} <> ts1'; F2 = 'Spec.Skip{} <> ts2'
body = '''  +itT = items_from_tail(dot, %s, it, restI, itemsEq)
  then_same(grammar, start, ts1, ts2, %s, %s,
    %s,
    tse => %s)
''' % (S, F1, F2, ih('ihTs', 'False{}', 'ts2', 'restI', 'index', 'prefix', '1n+dot', 'i1', 'i2', 'k', 'kind, alts, restO, after, E1, E2',
      ready8('fT1', 'fT2', 'sp1', 'sp2', 'all_in_tail(Spec.at(index, prefix, 1n+dot, i1, k, k), %s, %s, in1)' % (W('ts1', 'i1', 'k', '1n+dot'), ST(1)),
             'all_in_tail(Spec.at(index, prefix, 1n+dot, i2, k, k), %s, %s, in2)' % (W('ts2', 'i2', 'k', '1n+dot'), ST(2)), 'itT', 'even')),
   cong(LT, LT, 'v => Spec.Skip{} <> v', 'ts1', 'ts2', 'tse'))
out.append(seq_law('skip_skip', 'Two skips (of [ ] or of an empty item): the rest.', '  for +ts1: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n', '  for +it: Spec.Item\n  for +restI: +List<Spec.Item>\n', F1, F2, 'it <> restI', '  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}\n  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}\n', [('ihTs', 'ts1')], 'ts1, ts2, it, restI, ', body))

open('p6.bend', 'w').write('\n'.join(out))

out = []
out.append('''# ---- Shared steps ----

law make_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -F1: +List<Spec.Tree>
  for -F2: +List<Spec.Tree>
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  Same(grammar, start, F1, F2)

def make_clash(grammar, start, F1, F2, point, first, second, next, neq, cp1, cp2):
  Inr{(point, (first, (second, (next, (neq, (cp1, cp2))))))}

# After equal first trees: the rest of both sequences, from the same position.
law seq_tail:
  for +c1: +List<Spec.Tree>
  for +c2: +List<Spec.Tree>
  for +ce: {c1 == c2 : +List<Spec.Tree>}
''' + FIXD + POSD + '''  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +restI: +List<Spec.Item>
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for +spT1: G.Spells(ts1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(c1))))
  for +spT2: G.Spells(ts2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(c2))))
  for +inT1: {Spec.allIn(Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(c1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inT2: {Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(c2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itT: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
''' + ihd('ihTs', 'ts1') + '''  Same(grammar, start, ts1, ts2)

def seq_tail(c1, c2, ce, ''' + FIX + ', ' + POS + ''', ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs):
  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(c1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(c2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), c2, c1, Equal.sym(+List<Spec.Tree>, c1, c2, ce))
  +lt2 = List.length(&2, Nat, Spec.leaves(ts2))
  +spT2b = Equal.trans(+List<Nat>, Spec.leaves(ts2), Lemma.slice(input, e2, lt2), Lemma.slice(input, e1, lt2), spT2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lt2), e2, e1, eE))
  +inT2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inT2)
  ihTs(False{}, ts2, restI, index, prefix, 1n+dot, i1, i2, e1, kind, alts, restO, after, E1, E2, (fT1, (fT2, (spT1, (spT2b, (inT1, (inT2b, (itT, even))))))))

law node_eq:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +qe: {q1 == q2 : Nat}
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Node{q1, ch1} <> ts1 == Spec.Node{q2, ch2} <> ts2 : +List<Spec.Tree>}

def node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, che, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Node{q1, ch1} <> ts1, Spec.Node{q2, ch1} <> ts1, Spec.Node{q2, ch2} <> ts2, Equal.cong(Nat, +List<Spec.Tree>, v => Spec.Node{v, ch1} <> ts1, q1, q2, qe),
    Equal.trans(+List<Spec.Tree>, Spec.Node{q2, ch1} <> ts1, Spec.Node{q2, ch2} <> ts1, Spec.Node{q2, ch2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Node{q2, v} <> ts1, ch1, ch2, che),
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Node{q2, ch2} <> v, ts1, ts2, tse)))

law pick_eq:
  for +a1: Nat
  for +a2: Nat
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +ae: {a1 == a2 : Nat}
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Pick{a1, ch1} <> ts1 == Spec.Pick{a2, ch2} <> ts2 : +List<Spec.Tree>}

def pick_eq(a1, a2, ch1, ch2, ts1, ts2, ae, che, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Pick{a1, ch1} <> ts1, Spec.Pick{a2, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts2, Equal.cong(Nat, +List<Spec.Tree>, v => Spec.Pick{v, ch1} <> ts1, a1, a2, ae),
    Equal.trans(+List<Spec.Tree>, Spec.Pick{a2, ch1} <> ts1, Spec.Pick{a2, ch2} <> ts1, Spec.Pick{a2, ch2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Pick{a2, v} <> ts1, ch1, ch2, che),
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Pick{a2, ch2} <> v, ts1, ts2, tse)))

law loop_eq:
  for +rs1: +List<Spec.Tree>
  for +rs2: +List<Spec.Tree>
  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +rse: {rs1 == rs2 : +List<Spec.Tree>}
  for +tse: {ts1 == ts2 : +List<Spec.Tree>}
  {Spec.Loop{rs1} <> ts1 == Spec.Loop{rs2} <> ts2 : +List<Spec.Tree>}

def loop_eq(rs1, rs2, ts1, ts2, rse, tse):
  Equal.trans(+List<Spec.Tree>, Spec.Loop{rs1} <> ts1, Spec.Loop{rs2} <> ts1, Spec.Loop{rs2} <> ts2, Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Loop{v} <> ts1, rs1, rs2, rse),
    Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => Spec.Loop{rs2} <> v, ts1, ts2, tse))
''')

# ---- nonterminals ----
F1 = 'Spec.Node{q1, ch1} <> ts1'; F2 = 'Spec.Node{q2, ch2} <> ts2'
TAILD = '''  for +ts1: +List<Spec.Tree>
  for +ts2: +List<Spec.Tree>
  for +restI: +List<Spec.Item>
  for +fT1: {Spec.fits(ts1, grammar, restI) == True{} : Bool}
  for +fT2: {Spec.fits(ts2, grammar, restI) == True{} : Bool}
  for +spT1: G.Spells(ts1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(C1))))
  for +spT2: G.Spells(ts2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(C2))))
  for +inT1: {Spec.allIn(Spec.walk(ts1, False{}, index, prefix, 1n+dot, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(C1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inT2: {Spec.allIn(Spec.walk(ts2, False{}, index, prefix, 1n+dot, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(C2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +itT: {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restI : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
'''
TAILA = 'ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even'
out.append('''law node_same:
''' + FIXD + POSD + '''  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +fC1: {Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, q1, [], 0n, k, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.steps(root2, 0n)) == True{} : Bool}
''' + TAILD.replace('C1', 'ch1').replace('C2', 'ch2') + ihd('ihCh', 'ch1') + ihd('ihTs', 'ts1') + '  ' + SAME(F1, F2) + '''

def node_same(''' + FIX + ', ' + POS + ', q1, q2, qe, ch1, ch2, fC1, fC2, spC1, spC2, inC1, inC2, ' + TAILA + ''', ihCh, ihTs):
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, q1, [], 0n, k, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, k, k), Spec.steps(root2, 0n)), True{}, Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, v, [], 0n, k, k), Spec.steps(root2, 0n)), q1, q2, qe), inC2)
  both_same(grammar, start, ch1, ch2, ts1, ts2, ''' + F1 + ', ' + F2 + ''',
    ihCh(False{}, ch2, Spec.rhsOf(grammar, q1), q1, [], 0n, k, k, k, ''' + DUMMY + ''', (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, ({==}, {==})))))))),
    che => seq_tail(ch1, ch2, che, ''' + FIX + ', ' + POS + ', ' + TAILA + ''', ihTs),
    che => tse => node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, che, tse))
''')

def heads(j, kind):
    # facts of tree j for a head with children ch_j and tail ts_j
    return '''  +lc%(j)d = Spec.leaves(ch%(j)d)
  +lt%(j)d = Spec.leaves(ts%(j)d)
  +e%(j)d = Nat.add(k, List.length(&2, Nat, lc%(j)d))
  +spC%(j)d = G.spells_first(input, k, lc%(j)d, lt%(j)d, sp%(j)d)
  +spT%(j)d = G.spells_second(input, k, lc%(j)d, lt%(j)d, sp%(j)d)
''' % {'j': j}

def walk_split(j, head_at, wC):
    wT = W('ts%d' % j, 'i%d' % j, 'e%d' % j, '1n+dot')
    return '''  +inA%(j)d = all_in_tail(%(h)s, List.append(&2, Spec.Bsr, %(wC)s, %(wT)s), %(st)s, in%(j)d)
  +inC%(j)d = all_in_left(%(wC)s, %(wT)s, %(st)s, inA%(j)d)
  +inT%(j)d = all_in_right(%(wC)s, %(wT)s, %(st)s, inA%(j)d)
''' % {'j': j, 'h': head_at % {'j': j}, 'wC': wC, 'wT': wT, 'st': ST(j)}

body = ''
for j in (1, 2):
    body += '''  +h%(j)d = Bool.and(Spec.lhsIs(grammar, q%(j)d, x), Spec.fits(ch%(j)d, grammar, Spec.rhsOf(grammar, q%(j)d)))
  +hOk%(j)d = Lemma.and_true_left(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
  +lhs%(j)d = Lemma.and_true_left(Spec.lhsIs(grammar, q%(j)d, x), Spec.fits(ch%(j)d, grammar, Spec.rhsOf(grammar, q%(j)d)), hOk%(j)d)
  +fC%(j)d = Lemma.and_true_right_side(Spec.lhsIs(grammar, q%(j)d, x), Spec.fits(ch%(j)d, grammar, Spec.rhsOf(grammar, q%(j)d)), hOk%(j)d)
  +fT%(j)d = Lemma.and_true_right_side(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
''' % {'j': j} + heads(j, 'node') + walk_split(j, 'Spec.at(index, prefix, 1n+dot, i%(j)d, k, e%(j)d)', 'Spec.walk(ch%d, False{}, q%d, [], 0n, k, k)' % (j, j))
body += '''  +itT = items_from_tail(dot, %s, Spec.Sym{Spec.Nonterminal{x}}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
''' % S
for j in (1, 2):
    body += '''  cp%(j)d = nt_cp(Spec.lhsIs(grammar, q%(j)d, x), grammar, start, q%(j)d, next, lhs%(j)d,
    predicts_in(next, grammar, start, input, root%(j)d, rootFit%(j)d, rootSp%(j)d, ch%(j)d, Spec.rhsOf(grammar, q%(j)d), q%(j)d, [], [], k, k, e%(j)d, Spec.walk(ch%(j)d, False{}, q%(j)d, [], 0n, k, k), fC%(j)d, spC%(j)d, {==}, {==}, {==},
      end_walk(ch%(j)d, Spec.rhsOf(grammar, q%(j)d), 0n, grammar, q%(j)d, [], k, k, e%(j)d, fC%(j)d, {==}, {==}, {==}), inC%(j)d))
''' % {'j': j}
body += '''  L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, %s, decide(Nat.is_eq(q1, q2), q1, q2, {==}),
    qe => node_same(%s, %s, q1, q2, qe, ch1, ch2, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs),
    neq => make_clash(grammar, start, %s, %s, Spec.NonterminalAt{x}, q1, q2, next, neq, cp1, cp2))
''' % (SAME(F1, F2), FIX, POS, F1, F2)
out.append(seq_law('node_node', 'Two nodes: the same alternate, else a clash.', '  for +q1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n  for +q2: Nat\n  for +ch2: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n', '  for +x: Nat\n  for +restI: +List<Spec.Item>\n', F1, F2, 'Spec.Sym{Spec.Nonterminal{x}} <> restI', '', [('ihCh', 'ch1'), ('ihTs', 'ts1')], 'q1, ch1, ts1, q2, ch2, ts2, x, restI, ', body))
open('p7.bend', 'w').write('\n'.join(out))

out = []
# ---- bracket alternatives ----
F1 = 'Spec.Pick{a1, ch1} <> ts1'; F2 = 'Spec.Pick{a2, ch2} <> ts2'
def pc(j): return 'List.append(&2, Nat, prefix, [dot, a%d])' % j
out.append('''law pick_same:
''' + FIXD + POSD + '''  for +bk: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(%s, dot) == Some{Spec.Brack{bk, balts}} : Maybe<&2, Spec.Item>}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(balts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(balts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, %s, 0n, k, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, %s, 0n, k, k), Spec.steps(root2, 0n)) == True{} : Bool}
''' % (S, pc(1), pc(2)) + TAILD.replace('C1', 'ch1').replace('C2', 'ch2') + ihd('ihCh', 'ch1') + ihd('ihTs', 'ts1') + '  ' + SAME(F1, F2) + '''

def pick_same(''' + FIX + ', ' + POS + ', bk, balts, a1, a2, ae, ch1, ch2, itAt, fC1, fC2, spC1, spC2, inC1, inC2, ' + TAILA + ''', ihCh, ihTs):
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(balts, a1)), Spec.fits(ch2, grammar, Spec.altOf(balts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(balts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, %s, 0n, k, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, %s, 0n, k, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, prefix, [dot, v]), 0n, k, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +cEq = seq_child(grammar, index, prefix, dot, a1, bk, balts, even, itAt)
  +evenC = Equal.trans(Bool, L.evenLength(%s), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even)
  both_same(grammar, start, ch1, ch2, ts1, ts2, %s, %s,
    ihCh(False{}, ch2, Spec.altOf(balts, a1), index, %s, 0n, k, k, k, %s, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq, evenC)))))))),
    che => seq_tail(ch1, ch2, che, %s, %s, %s, ihTs),
    che => tse => pick_eq(a1, a2, ch1, ch2, ts1, ts2, ae, che, tse))
''' % (pc(1), pc(2), pc(1), F1, F2, pc(1), DUMMY, FIX, POS, TAILA))

def pick_common(j, opt):
    if opt:
        s = '''  +okR%(j)d = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a%(j)d, ch%(j)d}])
  +h%(j)d = Bool.and(Bool.and(okR%(j)d, Spec.isAlt(balts, a%(j)d)), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)))
  +hOk%(j)d = Lemma.and_true_left(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
  +h2%(j)d = Lemma.and_true_left(Bool.and(okR%(j)d, Spec.isAlt(balts, a%(j)d)), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)), hOk%(j)d)
  +reads%(j)d = optional_consume(a%(j)d, ch%(j)d, Lemma.and_true_left(okR%(j)d, Spec.isAlt(balts, a%(j)d), h2%(j)d))
  +isA%(j)d = Lemma.and_true_right_side(okR%(j)d, Spec.isAlt(balts, a%(j)d), h2%(j)d)
  +fC%(j)d = Lemma.and_true_right_side(Bool.and(okR%(j)d, Spec.isAlt(balts, a%(j)d)), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)), hOk%(j)d)
  +fT%(j)d = Lemma.and_true_right_side(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
'''
    else:
        s = '''  +h%(j)d = Bool.and(Spec.isAlt(balts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)))
  +hOk%(j)d = Lemma.and_true_left(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
  +isA%(j)d = Lemma.and_true_left(Spec.isAlt(balts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)), hOk%(j)d)
  +fC%(j)d = Lemma.and_true_right_side(Spec.isAlt(balts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(balts, a%(j)d)), hOk%(j)d)
  +fT%(j)d = Lemma.and_true_right_side(h%(j)d, Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
'''
    return (s % {'j': j}) + heads(j, 'pick') + walk_split(j, 'Spec.at(index, prefix, 1n+dot, i%(j)d, k, e%(j)d)', 'Spec.walk(ch%d, False{}, index, %s, 0n, k, k)' % (j, pc(j)))

def alt_pw(j, bk, opt, next='next'):
    if opt:
        return 'first_from(lc%(j)d, %(n)s, grammar, input, ch%(j)d, Spec.altOf(balts, a%(j)d), k, fC%(j)d, {==}, spC%(j)d, {==}, reads%(j)d)' % {'j': j, 'n': next}
    return '''predicts_in(%(n)s, grammar, start, input, root%(j)d, rootFit%(j)d, rootSp%(j)d, ch%(j)d, Spec.altOf(balts, a%(j)d), index, %(pc)s, %(pc)s, k, k, e%(j)d, Spec.walk(ch%(j)d, False{}, index, %(pc)s, 0n, k, k), fC%(j)d, spC%(j)d, {==}, {==}, {==},
        end_walk(ch%(j)d, Spec.altOf(balts, a%(j)d), 0n, grammar, index, %(pc)s, k, k, e%(j)d, fC%(j)d, seq_child(grammar, index, prefix, dot, a%(j)d, %(bk)s, balts, even, itAt), {==}, {==}), inC%(j)d)''' % {'j': j, 'n': next, 'pc': pc(j), 'bk': bk}

def alt_cp_at(j, bk, opt, next='next'):
    mbe, leave = ('False{}', 'True{}') if opt else ('True{}', 'False{}')
    return '''bracket_cp(grammar, start, index, prefix, dot, a%(j)d, %(bk)s, balts, restI, %(n)s, itAt, itT,
      alt_cp(Spec.isAlt(balts, a%(j)d), grammar, start, balts, a%(j)d, index, prefix, dot, %(mbe)s, %(leave)s, restI, %(n)s, isA%(j)d,
        %(pw)s))''' % {'j': j, 'bk': bk, 'n': next, 'mbe': mbe, 'leave': leave, 'pw': alt_pw(j, bk, opt, next)}

def pick_pick(name, bk, opt):
    IT = 'Spec.Brack{%s, balts} <> restI' % bk
    body = pick_common(1, opt) + pick_common(2, opt) + '''  +itAt = items_from_head(dot, %s, Spec.Brack{%s, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, %s, Spec.Brack{%s, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
''' % (S, bk, S, bk)
    body += '  cp1 = %s\n  cp2 = %s\n' % (alt_cp_at(1, bk, opt), alt_cp_at(2, bk, opt))
    body += '''  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, %s, decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => pick_same(%s, %s, %s, balts, a1, a2, ae, ch1, ch2, itAt, fC1, fC2, spC1, spC2, inC1, inC2, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihCh, ihTs),
    neq => make_clash(grammar, start, %s, %s, Spec.BracketAt{index, prefix, dot}, a1, a2, next, neq, cp1, cp2))
''' % (SAME(F1, F2), FIX, POS, bk, F1, F2)
    return seq_law(name, 'Two alternatives of %s: the same one, else a clash.' % bk, '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n  for +a2: Nat\n  for +ch2: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n', '  for +balts: +List<+List<Spec.Item>>\n  for +restI: +List<Spec.Item>\n', F1, F2, IT, '', [('ihCh', 'ch1'), ('ihTs', 'ts1')], 'a1, ch1, ts1, a2, ch2, ts2, balts, restI, ', body)
out.append(pick_pick('group_group', 'Spec.Group{}', False))
out.append(pick_pick('optional_optional', 'Spec.Optional{}', True))

# ---- [ ] taken by one tree, skipped by the other ----
def leave_at(j):
    # leaving [ ] in tree j (a skip): PREDICT of the rest, from the end of the sequence
    f = 'Spec.Skip{} <> ts%d' % j
    return '''bracket_cp(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, balts), Spec.Optional{}, balts, restI, next, itAt, itT,
      leave_cp(Spec.isAlt(balts, List.length(&2, +List<Spec.Item>, balts)), grammar, start, balts, index, prefix, dot, False{}, True{}, restI, next, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, balts)), {==},
        predicts_in(next, grammar, start, input, root%(j)d, rootFit%(j)d, rootSp%(j)d, ts%(j)d, restI, index, prefix, prefix, k, i%(j)d, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts%(j)d))), %(w)s, fit%(j)d, sp%(j)d, {==}, {==}, {==},
          end_walk(%(f)s, Spec.Brack{Spec.Optional{}, balts} <> restI, dot, grammar, index, prefix, i%(j)d, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts%(j)d))), fit%(j)d, itemsEq, {==}, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, %(f)s)), {==})), in%(j)d)))''' % {'j': j, 'f': f, 'w': W(f, 'i%d' % j, 'k', 'dot')}

for name, pickj in (('optional_skip', 1), ('skip_optional', 2)):
    skipj = 3 - pickj
    if pickj == 1:
        F1 = 'Spec.Pick{a1, ch1} <> ts1'; F2 = 'Spec.Skip{} <> ts2'; treeD = '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n'; params = 'a1, ch1, ts1, ts2, balts, restI, '
    else:
        F1 = 'Spec.Skip{} <> ts1'; F2 = 'Spec.Pick{a2, ch2} <> ts2'; treeD = '  for +ts1: +List<Spec.Tree>\n  for +a2: Nat\n  for +ch2: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n'; params = 'ts1, a2, ch2, ts2, balts, restI, '
    body = pick_common(pickj, True) + '''  +itAt = items_from_head(dot, %s, Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, %s, Spec.Brack{Spec.Optional{}, balts}, restI, itemsEq)
  +next = List.get(&2, Nat, input, k)
  +n = List.length(&2, +List<Spec.Item>, balts)
''' % (S, S)
    body += '  cpA = %s\n  cpL = %s\n' % (alt_cp_at(pickj, 'Spec.Optional{}', True), leave_at(skipj))
    if pickj == 1:
        body += '  make_clash(grammar, start, %s, %s, Spec.BracketAt{index, prefix, dot}, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)\n' % (F1, F2)
    else:
        body += '  make_clash(grammar, start, %s, %s, Spec.BracketAt{index, prefix, dot}, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)\n' % (F1, F2)
    out.append(seq_law(name, '[ ] taken by one tree and skipped by the other: a clash.', treeD, '  for +balts: +List<+List<Spec.Item>>\n  for +restI: +List<Spec.Item>\n', F1, F2, 'Spec.Brack{Spec.Optional{}, balts} <> restI', '', [], params, body))
open('p8.bend', 'w').write('\n'.join(out))

out = []
# ---- loops in a sequence ----
F1 = 'Spec.Loop{rs1} <> ts1'; F2 = 'Spec.Loop{rs2} <> ts2'
P1 = 'List.append(&2, Nat, prefix, [dot])'
def loop_loop(name, K):
    body = ''
    for j in (1, 2):
        d = {'j': j, 'K': K, 'P1': P1, 'S': S}
        body += '''  +okR%(j)d = Spec.roundsOk(%(K)s, rs%(j)d)
  +tm%(j)d = Spec.times(List.length(&2, Spec.Tree, rs%(j)d), Spec.Brack{Spec.Group{}, balts})
  +hOk%(j)d = Lemma.and_true_left(Bool.and(okR%(j)d, Spec.fits(rs%(j)d, grammar, tm%(j)d)), Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
  +fR%(j)d = Lemma.and_true_right_side(okR%(j)d, Spec.fits(rs%(j)d, grammar, tm%(j)d), hOk%(j)d)
  +fT%(j)d = Lemma.and_true_right_side(Bool.and(okR%(j)d, Spec.fits(rs%(j)d, grammar, tm%(j)d)), Spec.fits(ts%(j)d, grammar, restI), fit%(j)d)
  +lr%(j)d = Spec.leaves(rs%(j)d)
  +lt%(j)d = Spec.leaves(ts%(j)d)
  +e%(j)d = Nat.add(k, List.length(&2, Nat, lr%(j)d))
  +spR%(j)d = G.spells_first(input, k, lr%(j)d, lt%(j)d, sp%(j)d)
  +spT%(j)d = G.spells_second(input, k, lr%(j)d, lt%(j)d, sp%(j)d)
''' % d
        wR = 'Spec.walk(rs%d, True{}, index, %s, 0n, k, k)' % (j, P1)
        body += walk_split(j, 'Spec.at(index, prefix, 1n+dot, i%(j)d, k, e%(j)d)', wR).replace('+inC%d' % j, '+inR%d' % j)
        fine = 'closure_consume(rs%d, Lemma.and_true_left(okR%d, Spec.fits(rs%d, grammar, tm%d), hOk%d))' % (j, j, j, j, j) if K == 'Spec.Closure{}' else 'Lemma.and_true_left(okR%d, Spec.fits(rs%d, grammar, tm%d), hOk%d)' % (j, j, j, j)
        f = 'Spec.Loop{rs%d} <> ts%d' % (j, j)
        body += '''  +fine%(j)d = %(fine)s
  LP%(j)d = predicts_in(List.get(&2, Nat, input, e%(j)d), grammar, start, input, root%(j)d, rootFit%(j)d, rootSp%(j)d, ts%(j)d, restI, index, prefix, prefix, e%(j)d, i%(j)d, Nat.add(e%(j)d, List.length(&2, Nat, lt%(j)d)), %(w)s, fT%(j)d, spT%(j)d, {==}, {==}, {==},
    end_walk(%(f)s, Spec.Brack{%(K)s, balts} <> restI, dot, grammar, index, prefix, i%(j)d, k, Nat.add(e%(j)d, List.length(&2, Nat, lt%(j)d)), fit%(j)d, itemsEq,
      Equal.sym(Nat, Nat.add(e%(j)d, List.length(&2, Nat, lt%(j)d)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr%(j)d, lt%(j)d))), G.end_split(k, lr%(j)d, lt%(j)d)),
      Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, %(f)s)), {==})), in%(j)d)
''' % {'j': j, 'fine': fine, 'w': W(f, 'i%d' % j, 'k', 'dot'), 'f': f, 'K': K}
    body += '''  +itAt = items_from_head(dot, %s, Spec.Brack{%s, balts}, restI, itemsEq)
  +itT = items_from_tail(dot, %s, Spec.Brack{%s, balts}, restI, itemsEq)
  both_same(grammar, start, rs1, rs2, ts1, ts2, %s, %s,
    ihRs(True{}, rs2, [], index, prefix, dot, k, k, k, %s, balts, restI, False{}, e1, e2, %s),
    rse => seq_tail(rs1, rs2, rse, %s, %s, ts1, ts2, restI, fT1, fT2, spT1, spT2, inT1, inT2, itT, even, ihTs),
    rse => tse => loop_eq(rs1, rs2, ts1, ts2, rse, tse))
''' % (S, K, S, K, F1, F2, K, ready16('itAt', 'itT', '{==}', 'even', 'fR1', 'fR2', 'fine1', 'fine2', 'spR1', 'spR2', 'inR1', 'inR2', '{==}', '{==}', 'LP1', 'LP2'), FIX, POS)
    return seq_law(name, 'Two loops: the same rounds, then the rest.', '  for +rs1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n  for +rs2: +List<Spec.Tree>\n  for +ts2: +List<Spec.Tree>\n', '  for +balts: +List<+List<Spec.Item>>\n  for +restI: +List<Spec.Item>\n', F1, F2, 'Spec.Brack{%s, balts} <> restI' % K, '', [('ihRs', 'rs1'), ('ihTs', 'ts1')], 'rs1, ts1, rs2, ts2, balts, restI, ', body)
out.append(loop_loop('closure_closure', 'Spec.Closure{}'))
out.append(loop_loop('positive_positive', 'Spec.Positive{}'))

# ---- rounds ----
RD = '''  for +itAt: {Spec.itemAt(%s, dot) == Some{Spec.Brack{K, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, %s) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fR1: {Spec.fits(F1, grammar, Spec.times(List.length(&2, Spec.Tree, F1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fR2: {Spec.fits(F2, grammar, Spec.times(List.length(&2, Spec.Tree, F2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fine1: {roundsFine(K, AFTER, F1) == True{} : Bool}
  for +fine2: {roundsFine(K, AFTER, F2) == True{} : Bool}
  for +sp1: G.Spells(F1, input, k)
  for +sp2: G.Spells(F2, input, k)
  for +in1: {Spec.allIn(Spec.walk(F1, True{}, index, %s, 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(F2, True{}, index, %s, 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finR1: {Nat.add(k, List.length(&2, Nat, Spec.leaves(F1))) == E1 : Nat}
  for +finR2: {Nat.add(k, List.length(&2, Nat, Spec.leaves(F2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
''' % (S, S, P1, P1)
RA = 'itAt, restAt, even, fR1, fR2, fine1, fine2, sp1, sp2, in1, in2, finR1, finR2, LP1, LP2'
RPOSD = '''  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i1: Nat
  for +i2: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E1: Nat
  for +E2: Nat
'''
RPOS = 'index, prefix, dot, i1, i2, k, alts, restO, E1, E2'
def point_of(K, after):
    if K == 'Spec.Positive{}' and after == 'True{}':
        return 'Spec.AfterRoundAt{index, prefix, dot}', 'after_cp', 'False{}', 'True{}'
    if K == 'Spec.Positive{}':
        return 'Spec.BracketAt{index, prefix, dot}', 'bracket_cp', 'True{}', 'False{}'
    return 'Spec.BracketAt{index, prefix, dot}', 'bracket_cp', 'False{}', 'True{}'
def rlaw(name, comment, K, after, treeD, F1, F2, ihs, params, body):
    s = '# %s\nlaw %s:\n' % (comment, name) + FIXD + RPOSD + treeD + RD.replace('F1', F1).replace('F2', F2).replace('AFTER', after).replace('Spec.Brack{K', 'Spec.Brack{' + K).replace('roundsFine(K', 'roundsFine(' + K)
    for n, f in ihs: s += ihd(n, f)
    names = [FIX, RPOS] + [x.strip() for x in params.split(',') if x.strip()] + [RA] + [n for n, f in ihs]
    s += '  %s\n\ndef %s(%s):\n' % (SAME(F1, F2), name, ', '.join(names))
    return s + body + '\n'
def rtag(K, after): return ('closure' if K == 'Spec.Closure{}' else 'positive') + ('_later' if after == 'True{}' else '_first')

def round_facts(j, K, after):
    d = {'j': j, 'P1': P1, 'K': K}
    s = '''  +h%(j)d = Bool.and(Spec.isAlt(alts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(alts, a%(j)d)))
  +tmR%(j)d = Spec.times(List.length(&2, Spec.Tree, r%(j)d), Spec.Brack{Spec.Group{}, alts})
  +hOk%(j)d = Lemma.and_true_left(h%(j)d, Spec.fits(r%(j)d, grammar, tmR%(j)d), fR%(j)d)
  +isA%(j)d = Lemma.and_true_left(Spec.isAlt(alts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(alts, a%(j)d)), hOk%(j)d)
  +fC%(j)d = Lemma.and_true_right_side(Spec.isAlt(alts, a%(j)d), Spec.fits(ch%(j)d, grammar, Spec.altOf(alts, a%(j)d)), hOk%(j)d)
  +fRest%(j)d = Lemma.and_true_right_side(h%(j)d, Spec.fits(r%(j)d, grammar, tmR%(j)d), fR%(j)d)
  +lc%(j)d = Spec.leaves(ch%(j)d)
  +lrr%(j)d = Spec.leaves(r%(j)d)
  +e%(j)d = Nat.add(k, List.length(&2, Nat, lc%(j)d))
  +spC%(j)d = G.spells_first(input, k, lc%(j)d, lrr%(j)d, sp%(j)d)
  +spR%(j)d = G.spells_second(input, k, lc%(j)d, lrr%(j)d, sp%(j)d)
  +pc%(j)d = List.append(&2, Nat, %(P1)s, [a%(j)d])
  +pcN%(j)d = List.append(&2, Nat, prefix, [dot, a%(j)d])
  +asc%(j)d = G.nat_append_assoc(prefix, [dot], [a%(j)d])
  +wC%(j)d = Spec.walk(ch%(j)d, False{}, index, pc%(j)d, 0n, i%(j)d, k)
  +wR%(j)d = Spec.walk(r%(j)d, True{}, index, %(P1)s, 0n, i%(j)d, e%(j)d)
  +inC%(j)d = all_in_left(wC%(j)d, wR%(j)d, Spec.steps(root%(j)d, 0n), in%(j)d)
  +inRr%(j)d = all_in_right(wC%(j)d, wR%(j)d, Spec.steps(root%(j)d, 0n), in%(j)d)
  +cEq%(j)d = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, pc%(j)d), Spec.sequenceAt(grammar, index, pcN%(j)d), Spec.altOf(alts, a%(j)d),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), pc%(j)d, pcN%(j)d, asc%(j)d), seq_child(grammar, index, prefix, dot, a%(j)d, %(K)s, alts, even, itAt))
''' % d
    return s

def reads(j): return 'consumes_child(a%d, ch%d, Lemma.and_true_left(Spec.consumes(Spec.Pick{a%d, ch%d}), Spec.allConsume(r%d), fine%d))' % (j, j, j, j, j, j)

def round_pw(j, mbe, next):
    if mbe == 'True{}':
        return '''predicts_in(%(n)s, grammar, start, input, root%(j)d, rootFit%(j)d, rootSp%(j)d, ch%(j)d, Spec.altOf(alts, a%(j)d), index, pcN%(j)d, pc%(j)d, k, i%(j)d, e%(j)d, wC%(j)d, fC%(j)d, spC%(j)d, {==}, {==}, asc%(j)d,
          end_walk(ch%(j)d, Spec.altOf(alts, a%(j)d), 0n, grammar, index, pc%(j)d, i%(j)d, k, e%(j)d, fC%(j)d, cEq%(j)d, {==}, {==}), inC%(j)d)''' % {'j': j, 'n': next}
    return 'first_from(lc%(j)d, %(n)s, grammar, input, ch%(j)d, Spec.altOf(alts, a%(j)d), k, fC%(j)d, {==}, spC%(j)d, NEXTEQ, %(r)s)' % {'j': j, 'n': next, 'r': reads(j)}

def round_cp(j, K, after, next, nextEq='{==}'):
    point, wrap, mbe, leave = point_of(K, after)
    return '''%(w)s(grammar, start, index, prefix, dot, a%(j)d, %(K)s, alts, restO, %(n)s, itAt, restAt,
      alt_cp(Spec.isAlt(alts, a%(j)d), grammar, start, alts, a%(j)d, index, prefix, dot, %(mbe)s, %(leave)s, restO, %(n)s, isA%(j)d,
        %(pw)s))''' % {'w': wrap, 'j': j, 'K': K, 'n': next, 'mbe': mbe, 'leave': leave, 'pw': round_pw(j, mbe, next).replace('NEXTEQ', nextEq)}

def leave_round_cp(j, K, after, next):
    point, wrap, mbe, leave = point_of(K, after)
    return '''%(w)s(grammar, start, index, prefix, dot, List.length(&2, +List<Spec.Item>, alts), %(K)s, alts, restO, %(n)s, itAt, restAt,
      leave_cp(Spec.isAlt(alts, List.length(&2, +List<Spec.Item>, alts)), grammar, start, alts, index, prefix, dot, %(mbe)s, %(leave)s, restO, %(n)s, Pf.lt_irrefl(List.length(&2, +List<Spec.Item>, alts)), {==}, LP%(j)d))''' % {'w': wrap, 'j': j, 'K': K, 'n': next, 'mbe': mbe, 'leave': leave}

def fine_rest(j, K, after):
    if K == 'Spec.Positive{}' and after == 'False{}':
        return 'positive_rest(Spec.Pick{a%d, ch%d}, r%d, fine%d)' % (j, j, j, j)
    return 'Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a%d, ch%d}), Spec.allConsume(r%d), fine%d)' % (j, j, j, j)

for K in ('Spec.Closure{}', 'Spec.Positive{}'):
    for after in ('False{}', 'True{}'):
        tag = rtag(K, after)
        point, wrap, mbe, leave = point_of(K, after)
        F1 = 'Spec.Pick{a1, ch1} <> r1'; F2 = 'Spec.Pick{a2, ch2} <> r2'
        # the rest of the rounds, after equal first rounds
        tailD = '''  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +che: {ch1 == ch2 : +List<Spec.Tree>}
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(%s, dot) == Some{Spec.Brack{%s, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, %s) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fRest1: {Spec.fits(r1, grammar, Spec.times(List.length(&2, Spec.Tree, r1), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fRest2: {Spec.fits(r2, grammar, Spec.times(List.length(&2, Spec.Tree, r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +fineR1: {Spec.allConsume(r1) == True{} : Bool}
  for +fineR2: {Spec.allConsume(r2) == True{} : Bool}
  for +spR1: G.Spells(r1, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))))
  for +spR2: G.Spells(r2, input, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))))
  for +inRr1: {Spec.allIn(Spec.walk(r1, True{}, index, %s, 0n, i1, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inRr2: {Spec.allIn(Spec.walk(r2, True{}, index, %s, 0n, i2, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))), Spec.steps(root2, 0n)) == True{} : Bool}
  for +finRr1: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1))) == E1 : Nat}
  for +finRr2: {Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2))), List.length(&2, Nat, Spec.leaves(r2))) == E2 : Nat}
  for LP1: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E1))
  for LP2: Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E2))
''' % (S, K, S, P1, P1)
        s = '# The rounds after two equal rounds.\nlaw round_tail_%s:\n' % tag + FIXD + RPOSD + tailD + ihd('ihR', 'r1') + '  ' + SAME('r1', 'r2') + '\n\n'
        s += 'def round_tail_%s(%s, %s, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR):\n' % (tag, FIX, RPOS)
        s += '''  +e1 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1)))
  +e2 = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch2)))
  +eE = Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(k, List.length(&2, Nat, Spec.leaves(v))), ch2, ch1, Equal.sym(+List<Spec.Tree>, ch1, ch2, che))
  +lr2 = List.length(&2, Nat, Spec.leaves(r2))
  +spR2b = Equal.trans(+List<Nat>, Spec.leaves(r2), Lemma.slice(input, e2, lr2), Lemma.slice(input, e1, lr2), spR2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, lr2), e2, e1, eE))
  +inRr2b = Equal.trans(Bool, Spec.allIn(Spec.walk(r2, True{}, index, %(P1)s, 0n, i2, e1), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(r2, True{}, index, %(P1)s, 0n, i2, e2), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(r2, True{}, index, %(P1)s, 0n, i2, v), Spec.steps(root2, 0n)), e1, e2, Equal.sym(Nat, e2, e1, eE)), inRr2)
  +finRr2b = Equal.trans(Nat, Nat.add(e1, lr2), Nat.add(e2, lr2), E2, Equal.cong(Nat, Nat, v => Nat.add(v, lr2), e1, e2, Equal.sym(Nat, e2, e1, eE)), finRr2)
  ihR(True{}, r2, [], index, prefix, dot, i1, i2, e1, %(K)s, alts, restO, True{}, E1, E2, %(rd)s)
''' % {'P1': P1, 'K': K, 'rd': ready16('itAt', 'restAt', '{==}', 'even', 'fRest1', 'fRest2', 'fineR1', 'fineR2', 'spR1', 'spR2b', 'inRr1', 'inRr2b', 'finRr1', 'finRr2b', 'LP1', 'LP2')}
        out.append(s)
        # two rounds
        body = round_facts(1, K, after) + round_facts(2, K, after) + '  +next = List.get(&2, Nat, input, k)\n'
        body += '  cp1 = %s\n  cp2 = %s\n' % (round_cp(1, K, after, 'next'), round_cp(2, K, after, 'next'))
        same = '''round_same_%(t)s(%(FIX)s, %(RPOS)s, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, %(fr1)s, %(fr2)s, spR1, spR2, inRr1, inRr2,
      Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrr1)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc1, lrr1))), E1, G.end_split(k, lc1, lrr1), finR1),
      Equal.trans(Nat, Nat.add(e2, List.length(&2, Nat, lrr2)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc2, lrr2))), E2, G.end_split(k, lc2, lrr2), finR2), LP1, LP2, ihCh, ihR)''' % {'t': tag, 'FIX': FIX, 'RPOS': RPOS, 'fr1': fine_rest(1, K, after), 'fr2': fine_rest(2, K, after)}
        body += '''  L.either_case({a1 == a2 : Nat}, {Nat.is_eq(a1, a2) == False{} : Bool}, %s, decide(Nat.is_eq(a1, a2), a1, a2, {==}),
    ae => %s,
    neq => make_clash(grammar, start, %s, %s, %s, a1, a2, next, neq, cp1, cp2))
''' % (SAME(F1, F2), same, F1, F2, point)
        sameD = '''  for +a1: Nat
  for +a2: Nat
  for +ae: {a1 == a2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +r1: +List<Spec.Tree>
  for +r2: +List<Spec.Tree>
  for +itAt: {Spec.itemAt(%(S)s, dot) == Some{Spec.Brack{%(K)s, alts}} : Maybe<&2, Spec.Item>}
  for +restAt: {Spec.itemsFrom(1n+dot, %(S)s) == restO : +List<Spec.Item>}
  for +even: {L.evenLength(prefix) == True{} : Bool}
  for +fC1: {Spec.fits(ch1, grammar, Spec.altOf(alts, a1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  for +spC1: G.Spells(ch1, input, k)
  for +spC2: G.Spells(ch2, input, k)
  for +inC1: {Spec.allIn(Spec.walk(ch1, False{}, index, List.append(&2, Nat, %(P1)s, [a1]), 0n, i1, k), Spec.steps(root1, 0n)) == True{} : Bool}
  for +inC2: {Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, %(P1)s, [a2]), 0n, i2, k), Spec.steps(root2, 0n)) == True{} : Bool}
  for +cEq1: {Spec.sequenceAt(grammar, index, List.append(&2, Nat, %(P1)s, [a1])) == Spec.altOf(alts, a1) : +List<Spec.Item>}
''' % {'S': S, 'K': K, 'P1': P1}
        restD = tailD[tailD.index('  for +fRest1'):]
        restD = restD.replace('Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1)))', 'Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch1))), List.length(&2, Nat, Spec.leaves(r1)))')
        s = '# Two equal choices for a round: the round, then the rest of the rounds.\nlaw round_same_%s:\n' % tag + FIXD + RPOSD + sameD + restD + ihd('ihCh', 'ch1') + ihd('ihR', 'r1') + '  ' + SAME(F1, F2) + '\n\n'
        s += 'def round_same_%s(%s, %s, a1, a2, ae, ch1, ch2, r1, r2, itAt, restAt, even, fC1, fC2, spC1, spC2, inC1, inC2, cEq1, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihCh, ihR):\n' % (tag, FIX, RPOS)
        s += '''  +pc1 = List.append(&2, Nat, %(P1)s, [a1])
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.altOf(alts, a1)), Spec.fits(ch2, grammar, Spec.altOf(alts, a2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.altOf(alts, v)), a1, a2, ae), fC2)
  +inC2b = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, index, pc1, 0n, i2, k), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, %(P1)s, [a2]), 0n, i2, k), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, index, List.append(&2, Nat, %(P1)s, [v]), 0n, i2, k), Spec.steps(root2, 0n)), a1, a2, ae), inC2)
  +asc = G.nat_append_assoc(prefix, [dot], [a1])
  +evenC = Equal.trans(Bool, L.evenLength(pc1), L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), pc1, List.append(&2, Nat, prefix, [dot, a1]), asc),
    Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a1])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a1), even))
  both_same(grammar, start, ch1, ch2, r1, r2, %(F1)s, %(F2)s,
    ihCh(False{}, ch2, Spec.altOf(alts, a1), index, pc1, 0n, i1, i2, k, %(D)s, (fC1, (fC2b, (spC1, (spC2, (inC1, (inC2b, (cEq1, evenC)))))))),
    che => round_tail_%(t)s(%(FIX)s, %(RPOS)s, ch1, ch2, che, r1, r2, itAt, restAt, even, fRest1, fRest2, fineR1, fineR2, spR1, spR2, inRr1, inRr2, finRr1, finRr2, LP1, LP2, ihR),
    che => tse => pick_eq(a1, a2, ch1, ch2, r1, r2, ae, che, tse))
''' % {'P1': P1, 'F1': F1, 'F2': F2, 'D': DUMMY, 't': tag, 'FIX': FIX, 'RPOS': RPOS}
        out.append(s)
        out.append(rlaw('rounds_%s' % tag, 'Two rounds: the same choice, else a clash.', K, after, '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +r1: +List<Spec.Tree>\n  for +a2: Nat\n  for +ch2: +List<Spec.Tree>\n  for +r2: +List<Spec.Tree>\n', F1, F2, [('ihCh', 'ch1'), ('ihR', 'r1')], 'a1, ch1, r1, a2, ch2, r2', body))
        # one tree has no more rounds
        if not (K == 'Spec.Positive{}' and after == 'False{}'):
            for stop in (1, 2):
                go = 3 - stop
                Fs = '[]'
                Fg = 'Spec.Pick{a%d, ch%d} <> r%d' % (go, go, go)
                F1x, F2x = (Fs, Fg) if stop == 1 else (Fg, Fs)
                body = round_facts(go, K, after).replace('in%d)' % go, 'in%d)' % go)
                body += '''  +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E%(s)d, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finR%(s)d)
  +next = List.get(&2, Nat, input, E%(s)d)
  +n = List.length(&2, +List<Spec.Item>, alts)
''' % {'s': stop}
                body += '  cpL = %s\n  cpA = %s\n' % (leave_round_cp(stop, K, after, 'next'), round_cp(go, K, after, 'next', 'Equal.cong(Nat, Maybe<&2, Nat>, v => List.get(&2, Nat, input, v), k, E%d, nk)' % stop))
                if stop == 1:
                    body += '  make_clash(grammar, start, %s, %s, %s, n, a2, next, Equal.trans(Bool, Nat.is_eq(n, a2), Nat.is_eq(a2, n), False{}, Lemma.nat_eq_symm(n, a2), lt_ne(a2, n, isA2)), cpL, cpA)\n' % (F1x, F2x, point)
                    treeD = '  for +a2: Nat\n  for +ch2: +List<Spec.Tree>\n  for +r2: +List<Spec.Tree>\n'; params = 'a2, ch2, r2'
                else:
                    body += '  make_clash(grammar, start, %s, %s, %s, a1, n, next, lt_ne(a1, n, isA1), cpA, cpL)\n' % (F1x, F2x, point)
                    treeD = '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +r1: +List<Spec.Tree>\n'; params = 'a1, ch1, r1'
                out.append(rlaw('stop%d_%s' % (stop, tag), 'One tree leaves the loop, the other takes another round: a clash.', K, after, treeD, F1x, F2x, [], params, body))
open('p9.bend', 'w').write('\n'.join(out))

out = []
ITEMS = [('Nil', 'Nil{}', None), ('T', 'Con{Spec.Sym{Spec.Terminal{+term}}, +restI}', 'Spec.Sym{Spec.Terminal{term}} <> restI'),
         ('N', 'Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI}', 'Spec.Sym{Spec.Nonterminal{x}} <> restI'),
         ('G', 'Con{Spec.Brack{Spec.Group{}, +balts}, +restI}', 'Spec.Brack{Spec.Group{}, balts} <> restI'),
         ('O', 'Con{Spec.Brack{Spec.Optional{}, +balts}, +restI}', 'Spec.Brack{Spec.Optional{}, balts} <> restI'),
         ('C', 'Con{Spec.Brack{Spec.Closure{}, +balts}, +restI}', 'Spec.Brack{Spec.Closure{}, balts} <> restI'),
         ('P', 'Con{Spec.Brack{Spec.Positive{}, +balts}, +restI}', 'Spec.Brack{Spec.Positive{}, balts} <> restI'),
         ('E', 'Con{Spec.Eps{}, +restI}', 'Spec.Eps{} <> restI')]
TREES = [('Nil', 'Nil{}', '[]'), ('Leaf', 'Con{Spec.Leaf{+a2}, +ts2}', 'Spec.Leaf{a2} <> ts2'), ('Node', 'Con{Spec.Node{+q2, +ch2}, +ts2}', 'Spec.Node{q2, ch2} <> ts2'),
         ('Pick', 'Con{Spec.Pick{+a2, +ch2}, +ts2}', 'Spec.Pick{a2, ch2} <> ts2'), ('Skip', 'Con{Spec.Skip{}, +ts2}', 'Spec.Skip{} <> ts2'), ('Loop', 'Con{Spec.Loop{+rs2}, +ts2}', 'Spec.Loop{rs2} <> ts2')]
OK = {'T': ['Leaf'], 'N': ['Node'], 'G': ['Pick'], 'O': ['Pick', 'Skip'], 'C': ['Loop'], 'P': ['Loop'], 'E': ['Skip'], 'Nil': []}
READY8 = '(fit1, (fit2, (sp1, (sp2, (in1, (in2, (itemsEq, even)))))))'
def cmp_ready(rounds, F1, F2, items): return 'CmpReady(%s, grammar, start, input, root1, root2, %s, %s, %s, %s)' % (rounds, F1, F2, items, POS)
DISPS = {
 'Leaf': ('a1, ts1', '  for +a1: Nat\n  for +ts1: +List<Spec.Tree>\n', 'Spec.Leaf{a1} <> ts1', [('ihTs', 'ts1')],
          {('T', 'Leaf'): 'leaf_leaf(%s, %s, a1, ts1, a2, ts2, term, restI, %s, ihTs)' % (FIX, POS, SEQA)}),
 'Node': ('q1, ch1, ts1', '  for +q1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n', 'Spec.Node{q1, ch1} <> ts1', [('ihCh', 'ch1'), ('ihTs', 'ts1')],
          {('N', 'Node'): 'node_node(%s, %s, q1, ch1, ts1, q2, ch2, ts2, x, restI, %s, ihCh, ihTs)' % (FIX, POS, SEQA)}),
 'Pick': ('a1, ch1, ts1', '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n', 'Spec.Pick{a1, ch1} <> ts1', [('ihCh', 'ch1'), ('ihTs', 'ts1')],
          {('G', 'Pick'): 'group_group(%s, %s, a1, ch1, ts1, a2, ch2, ts2, balts, restI, %s, ihCh, ihTs)' % (FIX, POS, SEQA),
           ('O', 'Pick'): 'optional_optional(%s, %s, a1, ch1, ts1, a2, ch2, ts2, balts, restI, %s, ihCh, ihTs)' % (FIX, POS, SEQA),
           ('O', 'Skip'): 'optional_skip(%s, %s, a1, ch1, ts1, ts2, balts, restI, %s)' % (FIX, POS, SEQA)}),
 'Skip': ('ts1', '  for +ts1: +List<Spec.Tree>\n', 'Spec.Skip{} <> ts1', [('ihTs', 'ts1')],
          {('E', 'Skip'): '+fitA = {fit1 : {Spec.fits(Spec.Skip{} <> ts1, grammar, Spec.Eps{} <> restI) == True{} : Bool}}\n          +fitB = {fit2 : {Spec.fits(Spec.Skip{} <> ts2, grammar, Spec.Eps{} <> restI) == True{} : Bool}}\n          skip_skip(%s, %s, ts1, ts2, Spec.Eps{}, restI, fitA, fitB, sp1, sp2, in1, in2, itemsEq, even, fitA, fitB, ihTs)' % (FIX, POS),
           ('O', 'Skip'): '+fitA = {fit1 : {Spec.fits(Spec.Skip{} <> ts1, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}\n          +fitB = {fit2 : {Spec.fits(Spec.Skip{} <> ts2, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}\n          skip_skip(%s, %s, ts1, ts2, Spec.Brack{Spec.Optional{}, balts}, restI, fitA, fitB, sp1, sp2, in1, in2, itemsEq, even, fitA, fitB, ihTs)' % (FIX, POS),
           ('O', 'Pick'): 'skip_optional(%s, %s, ts1, a2, ch2, ts2, balts, restI, %s)' % (FIX, POS, SEQA)}),
 'Loop': ('rs1, ts1', '  for +rs1: +List<Spec.Tree>\n  for +ts1: +List<Spec.Tree>\n', 'Spec.Loop{rs1} <> ts1', [('ihRs', 'rs1'), ('ihTs', 'ts1')],
          {('C', 'Loop'): 'closure_closure(%s, %s, rs1, ts1, rs2, ts2, balts, restI, %s, ihRs, ihTs)' % (FIX, POS, SEQA),
           ('P', 'Loop'): 'positive_positive(%s, %s, rs1, ts1, rs2, ts2, balts, restI, %s, ihRs, ihTs)' % (FIX, POS, SEQA)}),
}
for shape, (args, treeD, F1, ihs, real) in DISPS.items():
    name = shape.lower() + '_disp'
    s = 'law %s:\n  for items: +List<Spec.Item>\n  for f2: +List<Spec.Tree>\n' % name + FIXD + POSD + treeD
    s += '  for ready: %s\n' % cmp_ready('False{}', F1, 'f2', 'items')
    for n, f in ihs: s += ihd(n, f)
    s += '  %s\n\ndef %s(items, f2, %s, %s, %s, ready%s):\n  match items f2:\n' % (SAME(F1, 'f2'), name, FIX, POS, args, ''.join(', ' + n for n, f in ihs))
    for ik, ipat, iexpr in ITEMS:
        for tk, tpat, texpr in TREES:
            s += '    case %s %s:\n      match ready:\n        case %s:\n' % (ipat, tpat, READY8)
            if (ik, tk) in real:
                s += '          %s\n' % real[(ik, tk)]
            else:
                bad = 'fit1' if shape not in OK[ik] else 'fit2'
                s += '          Empty.absurd(%s, Lemma.false_is_not_true(%s))\n' % (SAME(F1, texpr), bad)
    out.append(s)

READY16 = '(itAt, (restAt, (isL, (even, (fR1, (fR2, (fine1, (fine2, (sp1, (sp2, (in1, (in2, (finR1, (finR2, (LP1, LP2)))))))))))))))'
RPOS2 = 'index, prefix, dot, i1, i2, k, alts, restO, E1, E2'
def rdisp(name, F1, treeD, args, ihs, real):
    s = 'law %s:\n  for kind: Spec.Bracket\n  for after: Bool\n  for f2: +List<Spec.Tree>\n' % name + FIXD + RPOSD + treeD
    s += '  for ready: CmpReady(True{}, grammar, start, input, root1, root2, %s, f2, [], index, prefix, dot, i1, i2, k, kind, alts, restO, after, E1, E2)\n' % F1
    for n, f in ihs: s += ihd(n, f)
    s += '  %s\n\ndef %s(kind, after, f2, %s, %s, %s ready%s):\n  match kind after f2:\n' % (SAME(F1, 'f2'), name, FIX, RPOS2, args, ''.join(', ' + n for n, f in ihs))
    for bad in ('Spec.Group{}', 'Spec.Optional{}'):
        s += '    case %s _ _:\n      match ready:\n        case %s:\n          Empty.absurd(%s, Lemma.false_is_not_true(isL))\n' % (bad, READY16, SAME(F1, 'f2'))
    for K in ('Spec.Closure{}', 'Spec.Positive{}'):
        for after in ('False{}', 'True{}'):
            for tk, tpat, texpr in TREES:
                tpat2 = tpat.replace('ts2', 'r2')
                texpr2 = texpr.replace('ts2', 'r2')
                s += '    case %s %s %s:\n      match ready:\n        case %s:\n' % (K, after, tpat2, READY16)
                s += '          ' + real(K, after, tk, texpr2) + '\n'
    return s
def nil_real(K, after, tk, texpr):
    tag = rtag(K, after)
    if tk == 'Nil':
        return 'Inl{{==}}'
    if tk != 'Pick':
        return 'Empty.absurd(%s, Lemma.false_is_not_true(fR2))' % SAME('[]', texpr)
    if K == 'Spec.Positive{}' and after == 'False{}':
        return 'Empty.absurd(%s, Lemma.false_is_not_true(fine1))' % SAME('[]', texpr)
    return 'stop1_%s(%s, %s, a2, ch2, r2, %s)' % (tag, FIX, RPOS2, RA)
def pick_real(K, after, tk, texpr):
    tag = rtag(K, after)
    F1 = 'Spec.Pick{a1, ch1} <> r1'
    if tk == 'Nil':
        if K == 'Spec.Positive{}' and after == 'False{}':
            return 'Empty.absurd(%s, Lemma.false_is_not_true(fine2))' % SAME(F1, '[]')
        return 'stop2_%s(%s, %s, a1, ch1, r1, %s)' % (tag, FIX, RPOS2, RA)
    if tk != 'Pick':
        return 'Empty.absurd(%s, Lemma.false_is_not_true(fR2))' % SAME(F1, texpr)
    return 'rounds_%s(%s, %s, a1, ch1, r1, a2, ch2, r2, %s, ihCh, ihR)' % (tag, FIX, RPOS2, RA)
out.append(rdisp('rounds_nil_disp', '[]', '', '', [], nil_real))
out.append(rdisp('rounds_pick_disp', 'Spec.Pick{a1, ch1} <> r1', '  for +a1: Nat\n  for +ch1: +List<Spec.Tree>\n  for +r1: +List<Spec.Tree>\n', 'a1, ch1, r1,', [('ihCh', 'ch1'), ('ihR', 'r1')], pick_real))

# ---- the comparison ----
def lam(f): return '(ri => f2x => itx => ix => px => dx => i1x => i2x => kx => kdx => ax => rox => afx => e1x => e2x => rd => compare(%s, ri, f2x, itx, %s, ix, px, dx, i1x, i2x, kx, kdx, ax, rox, afx, e1x, e2x, rd))' % (f, FIX)
s = '''law seq_nil:
  for f2: +List<Spec.Tree>
  for items: +List<Spec.Item>
''' + FIXD + POSD + '''  for ready: %s
  %s

def seq_nil(f2, items, %s, %s, ready):
  match ready:
    case %s:
      +none = fits_nil_items(items, grammar, fit1)
      +fit2b = Equal.trans(Bool, Spec.fits(f2, grammar, []), Spec.fits(f2, grammar, items), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), [], items, Equal.sym(+List<Spec.Item>, items, [], none)), fit2)
      Inl{Equal.sym(+List<Spec.Tree>, f2, [], L.fits_none(f2, grammar, fit2b))}

# Two forests that fit the same items from the same position, inside parse trees of the
# same input: the same forest, or a clash.
law compare:
  for f1: +List<Spec.Tree>
  for rounds: Bool
  for +f2: +List<Spec.Tree>
  for +items: +List<Spec.Item>
''' % (cmp_ready('False{}', '[]', 'f2', 'items'), SAME('[]', 'f2'), FIX, POS, READY8)
s += FIXD + POSD + '  for ready: CmpReady(rounds, grammar, start, input, root1, root2, f1, f2, items, %s)\n  %s\n\n' % (POS, SAME('f1', 'f2'))
s += 'def compare(f1, rounds, f2, items, %s, %s, ready):\n  match f1 rounds:\n' % (FIX, POS)
s += '    case Nil{} False{}:\n      seq_nil(f2, items, %s, %s, ready)\n' % (FIX, POS)
s += '    case Nil{} True{}:\n      rounds_nil_disp(kind, after, f2, %s, %s, ready)\n' % (FIX, RPOS2)
s += '    case Con{Spec.Leaf{+a1}, +ts1} False{}:\n      leaf_disp(items, f2, %s, %s, a1, ts1, ready, %s)\n' % (FIX, POS, lam('ts1'))
s += '    case Con{Spec.Node{+q1, +ch1}, +ts1} False{}:\n      node_disp(items, f2, %s, %s, q1, ch1, ts1, ready, %s, %s)\n' % (FIX, POS, lam('ch1'), lam('ts1'))
s += '    case Con{Spec.Pick{+a1, +ch1}, +ts1} False{}:\n      pick_disp(items, f2, %s, %s, a1, ch1, ts1, ready, %s, %s)\n' % (FIX, POS, lam('ch1'), lam('ts1'))
s += '    case Con{Spec.Skip{}, +ts1} False{}:\n      skip_disp(items, f2, %s, %s, ts1, ready, %s)\n' % (FIX, POS, lam('ts1'))
s += '    case Con{Spec.Loop{+rs1}, +ts1} False{}:\n      loop_disp(items, f2, %s, %s, rs1, ts1, ready, %s, %s)\n' % (FIX, POS, lam('rs1'), lam('ts1'))
s += '    case Con{Spec.Pick{+a1, +ch1}, +r1} True{}:\n      rounds_pick_disp(kind, after, f2, %s, %s, a1, ch1, r1, ready, %s, %s)\n' % (FIX, RPOS2, lam('ch1'), lam('r1'))
for pat, expr in (('Spec.Leaf{a}', 'Spec.Leaf{a}'), ('Spec.Node{q, ch}', 'Spec.Node{q, ch}'), ('Spec.Skip{}', 'Spec.Skip{}'), ('Spec.Loop{rs}', 'Spec.Loop{rs}')):
    s += '    case Con{%s, r1} True{}:\n      match ready:\n        case %s:\n          Empty.absurd(%s, Lemma.false_is_not_true(fR1))\n' % (pat, READY16, SAME(expr + ' <> r1', 'f2'))
out.append(s)
open('p10.bend', 'w').write('\n'.join(out))
