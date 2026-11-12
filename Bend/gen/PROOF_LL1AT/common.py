# Shared text for the ll1_at proof generator.
def tup(xs):
    return xs[0] if len(xs) == 1 else '(%s, %s)' % (xs[0], tup(xs[1:]))
TB = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
'''
TBA = 'grammar, start, input, root, rootFit, rootSp'
CTX = '''  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
'''
CTXA = 'index, prefix, dot, i, k, kind, alts, restO, later, E'
SEQ = 'Spec.sequenceAt(grammar, index, prefix)'
def made(f, rounds='False{}', later='later', index='index', prefix='prefix', dot='dot', k='k'):
    return 'Spec.madeIn(grammar, %s, %s, %s, %s, %s, %s, %s)' % (f, rounds, later, index, prefix, dot, k)
def allok(xs):
    return 'AllOk(grammar, start, input, %s)' % xs
def ready(rounds, f, items='items'):
    return 'Ready(%s, %s, %s, %s, %s)' % (rounds, TBA.replace(', rootFit, rootSp', ''), f, items, CTXA)
def ih(f):
    return 'IH(%s, %s)' % (TBA, f)
def walkS(f, dot='dot', k='k', prefix='prefix', index='index', i='i'):
    return 'Spec.walk(%s, False{}, %s, %s, %s, %s, %s)' % (f, index, prefix, dot, i, k)
STEPS = 'Spec.steps(root, 0n)'

# Bind a sequence Ready tuple as copyable values.
def seq_bind(F, ITEMS, ind='        '):
    return (ind + 'case (fit0, (sp0, (inW0, (itemsEq0, even0)))):\n' +
      ind + '  +fit = {fit0 : {Spec.fits(%s, grammar, %s) == True{} : Bool}}\n' % (F, ITEMS) +
      ind + '  +sp = {sp0 : G.Spells(%s, input, k)}\n' % F +
      ind + '  +inW = {inW0 : {Spec.allIn(%s, Spec.steps(root, 0n)) == True{} : Bool}}\n' % walkS(F) +
      ind + '  +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, %s) == %s : +List<Spec.Item>}}\n' % (SEQ, ITEMS) +
      ind + '  +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}\n')
