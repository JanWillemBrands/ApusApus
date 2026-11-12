import re
src = open('../../PROOF_NODEAD.bend').read()
tail = src[src.index('law pop_moved:'):]
# drop the stage-1 Laws binding and law; rewritten below
tail = tail[:tail.index('# NO DEAD WOOD, FOR A GRAMMAR WITHOUT BRACKETS.')]
tail = tail.replace('  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}\n', '')
tail = tail.replace(', plain,', ',')
tail = tail.replace(': NodeAt(', ': N1.NodeAt(')
# fact_on: every descriptor, bracket clusters and bracket pops
a = tail.index('def fact_on(')
b = tail.index('# ======== GROWING')
PR = 'Gll.Predict{t}'
TBA = 'grammar, start, t, po, noConf, input, root, rootFit, rootSp'
fact = '''def fact_on(fact, %(tba)s, reached, here, all):
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, +rpath, +dot, +k, +i}}:
      match here:
        case (p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))):
          item_on(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), f, %(tba)s, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, {==})
    case Support.FactCluster{Gll.CKey{Gll.TNt{+x}, +i}}:
      match here:
        case (q, (g, (lhsQ, node))):
          seeds_on(grammar, 0n, %(tba)s, x, i, q, g, lhsQ, node, {==})
    case Support.FactCluster{Gll.CKey{Gll.TBr{+index, +rpath}, +i}}:
      bracket_seeds_on(rpath, %(tba)s, index, i, here)
    case Support.FactReturn{+key, +edge}:
      edge_on(reached, %(tba)s, key, edge, here, all)
    case Support.FactPop{+key, +end}:
      on_append(PS.popGives(%(pr)s, grammar, input, reached, key, end), PS.descsWhen(%(pr)s, grammar, input, Check.againOfKey(grammar, key, end)), grammar, input, root,
        pop_on(reached, %(tba)s, key, end, here, all), again_on(key, %(tba)s, end, here))
    case Support.FactStep{+y}:
      {==}

''' % {'tba': TBA, 'pr': PR}
tail = tail[:a] + fact + tail[b:]
tail += '''# NO DEAD WOOD: an LL(1) grammar (by the checked tables) gives the checked LL(1) parser
# only steps of the input's one parse tree.
law ll1_no_dead_wood:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +t: Gll.Tables
  for +tablesEq: {First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start) == Some{t} : Maybe<&2, Gll.Tables>}
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for got: {PS.llSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def ll1_no_dead_wood(fuel, grammar, start, input, set, t, tablesEq, ll1, tree, fit, sp, got):
  +tb = First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start)
  run_exact(Gll.parseWith(fuel, Gll.Predict{t}, grammar, start, input), grammar, start, t, ll1, input, tree, fit, sp, set,
    Equal.trans(Maybe<&2, +List<Spec.Bsr>>, PS.llPick(Some{t}, fuel, grammar, start, input), PS.llPick(tb, fuel, grammar, start, input), Some{set},
      Equal.cong(Maybe<&2, Gll.Tables>, Maybe<&2, +List<Spec.Bsr>>, v => PS.llPick(v, fuel, grammar, start, input), Some{t}, tb, Equal.sym(Maybe<&2, Gll.Tables>, tb, Some{t}, tablesEq)), got))
'''
open('m11b.bend', 'w').write('\n# ======== RULES ON THE TREE, AND THE LAW ========\n\n' + tail)
