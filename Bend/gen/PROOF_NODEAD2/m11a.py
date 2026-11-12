exec(open('m10.py').read().split('\nout = []')[0])
SEQO = 'Gll.seqAt(grammar, index, outer)'
RESTO = 'Gll.dropFrom(1n+m, %s)' % SEQO
N = 'Gll.nthItem(%s, m)' % SEQO
PO = 'prefixOf(outer)'
out = ['\n# ======== ANOTHER ROUND OF A LOOP ON THE TREE ========\n']
for K, kn in (('Spec.Closure{}', 'closure'), ('Spec.Positive{}', 'positive')):
    DEa = 'Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}'
    out.append('''
law again_alts_%(kn)s:
  for n: Nat
''' % {'kn': kn} + TB + '  for +r2: +List<Spec.Tree>\n' + LD.replace('KIND', K).replace('R2', 'r2') + '''  for +hn: {Nat.is_lt(n, 1n+List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, Gll.alternatives(n, index, m <> outer, k, end)))

def again_alts_%(kn)s(n, %(tba)s, r2, %(la)s, hn):
  match n:
    case 0n:
      {==}
    case 1n+(+a1):
      on_append(PS.descWhen(%(pr)s, grammar, input, %(de)s), PS.descsWhen(%(pr)s, grammar, input, Gll.alternatives(a1, index, m <> outer, k, end)), grammar, input, root,
        again_one_%(kn)s(Gll.admits(%(pr)s, grammar, input, %(de)s), Nat.is_eq(k, end), %(tba)s, r2, %(la)s, a1, hn, {==}, {==}),
        again_alts_%(kn)s(a1, %(tba)s, r2, %(la)s, lt_up(a1, List.length(&2, +List<Spec.Item>, alts), hn)))
''' % {'kn': kn, 'pr': PR, 'tba': TBA, 'la': LA, 'de': DEa})

GOALK = 'AllOn(grammar, input, root, PS.descsWhen(%s, grammar, input, Gll.againPick(Gll.isLoop(%%s), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end)))' % PR
s = '''
# The rounds that may follow a round of a bracket on the tree, ending at end.
law again_kind:
  for kind: Spec.Bracket
  for ff: +List<Spec.Tree>
''' + TB + '''  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, %(seqo)s)) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, %(po)s, m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {%(n)s == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +ri: RoundIn(ff, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  %(goal)s

def again_kind(kind, ff, %(tba)s, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, ri):
  match kind ff:
    case Spec.Group{} _:
      {==}
    case Spec.Optional{} _:
      {==}
''' % {'seqo': SEQO, 'po': PO, 'n': N, 'goal': GOALK % 'kind', 'tba': TBA}
for K, kn in (('Spec.Closure{}', 'closure'), ('Spec.Positive{}', 'positive')):
    G0 = GOALK % K
    s += '''    case %(K)s Con{Spec.Loop{+rs}, +ts}:
      match ri:
        case (r2, (fitR, (spR, (inR, (ready, sumEq))))):
          again_alts_%(kn)s(List.length(&2, +List<Spec.Item>, alts), %(tba)s, r2, %(la)s, L.lt_succ_self(List.length(&2, +List<Spec.Item>, alts)))
    case %(K)s Con{Spec.Pick{+a2, +ch}, +ts}:
      +dEq = N1.nth_drop(%(seqo)s, m, Spec.Brack{%(K)s, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{%(K)s, alts} <> %(resto)s), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, %(seqo)s)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{%(K)s, alts} <> %(resto)s, Gll.dropFrom(m, %(seqo)s), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, %(seqo)s), Spec.Brack{%(K)s, alts} <> %(resto)s, dEq)), fitF)
      Empty.absurd(%(g0)s, Lemma.false_is_not_true(fitF2))
''' % {'K': K, 'kn': kn, 'tba': TBA, 'la': LA, 'seqo': SEQO, 'resto': RESTO, 'g0': G0}
    for pat in ('Nil{}', 'Con{Spec.Leaf{x}, ts}', 'Con{Spec.Node{q, ch}, ts}', 'Con{Spec.Skip{}, ts}'):
        s += '''    case %s %s:
      Empty.absurd(%s, Lemma.false_is_not_true(ri))
''' % (K, pat, G0)
out.append(s)

out.append('''
# The rounds that may follow a round that ended on the tree are on it.
law again_on:
  for key: Gll.CKey
''' + TB + '''  for +end: Nat
  for +here: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, Check.againOfKey(grammar, key, end)))

def again_on(key, %(tba)s, end, here):
  match key:
    case Gll.CKey{Gll.TNt{x}, k}:
      {==}
    case Gll.CKey{Gll.TBr{index, Nil{}}, k}:
      {==}
    case Gll.CKey{Gll.TBr{+index, Con{+m, +outer}}, +k}:
      match here:
        case (a, (p0, (g, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, (gAt, ri)))))))))), endEq)))):
          +itS = Equal.sym(Maybe<&2, Spec.Item>, %(n)s, Some{Spec.Brack{kind, alts}}, itEqP)
          %%itS : AllOn(grammar, input, root, PS.descsWhen(%(pr)s, grammar, input, Gll.againOf(_, index, m <> outer, k, end)))
          again_kind(kind, ff, %(tba)s, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, ri)
''' % {'pr': PR, 'tba': TBA, 'n': N})
open('m11a.bend', 'w').write(''.join(out))
