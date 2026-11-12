exec(open('m5.py').read().split('out = []')[0])
def tup(xs):
    return xs[0] if len(xs) == 1 else '(%s, %s)' % (xs[0], tup(xs[1:]))
FIXU = 'grammar, start, input, root, rootFit, rootSp, root, rootFit, rootSp'
s = '''
# Two callers of one sequence position, at one input position, have the same forest from
# there on.
law suffix_same:
''' + TB + '''  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +kc1: Nat
  for +kc2: Nat
  for +k: Nat
  for +f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +even: {L.evenLength(prefixOf(rpath)) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == %(seq)s : +List<Spec.Item>}
  for +fit1: {Spec.fits(f1, grammar, Gll.dropFrom(dot, %(seq)s)) == True{} : Bool}
  for +fit2: {Spec.fits(f2, grammar, Gll.dropFrom(dot, %(seq)s)) == True{} : Bool}
  for +sp1: G.Spells(f1, input, k)
  for +sp2: G.Spells(f2, input, k)
  for +in1: {Spec.allIn(Spec.walk(f1, False{}, index, prefixOf(rpath), dot, kc1, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(f2, False{}, index, prefixOf(rpath), dot, kc2, k), Spec.steps(root, 0n)) == True{} : Bool}
  {f1 == f2 : +List<Spec.Tree>}

def suffix_same(%(tba)s, index, rpath, dot, kc1, kc2, k, f1, f2, even, seqEq, fit1, fit2, sp1, sp2, in1, in2):
  +p = prefixOf(rpath)
  +items = Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, p))
  +iEq = Equal.trans(+List<Spec.Item>, items, Gll.dropFrom(dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(dot, %(seq)s),
    L.items_from_eq(dot, Spec.sequenceAt(grammar, index, p)), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(dot, v), Spec.sequenceAt(grammar, index, p), %(seq)s, seqEq))
  +fitS1 = Equal.trans(Bool, Spec.fits(f1, grammar, items), Spec.fits(f1, grammar, Gll.dropFrom(dot, %(seq)s)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f1, grammar, v), items, Gll.dropFrom(dot, %(seq)s), iEq), fit1)
  +fitS2 = Equal.trans(Bool, Spec.fits(f2, grammar, items), Spec.fits(f2, grammar, Gll.dropFrom(dot, %(seq)s)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), items, Gll.dropFrom(dot, %(seq)s), iEq), fit2)
  N1.same_or_clash(grammar, start, t, po, noConf, f1, f2,
    U.compare(f1, False{}, f2, items, %(fixu)s, index, p, dot, kc1, kc2, k, Spec.Group{}, [], [], False{}, 0n, 0n,
      (fitS1, (fitS2, (sp1, (sp2, (in1, (in2, ({==}, even)))))))))

law move_round:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +fe: {f1 == f2 : +List<Spec.Tree>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +a: Nat
  for +k: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ri: RoundIn(f1, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  RoundIn(f2, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)

def move_round(grammar, input, root, f1, f2, fe, index, outer, m, a, k, p0, g, kind, alts, ri):
  %%fe : RoundIn(_, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  ri
''' % {'seq': SEQ, 'tba': TBA, 'fixu': FIXU}
open('m9b.bend', 'w').write(s)
