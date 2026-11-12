exec(open('m5.py').read().split('out = []')[0])
s = ('''
law pop_br_move:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +index2: Nat
  for +index: Nat
  for +rp: +List<Nat>
  for +rp2: +List<Nat>
  for +i: Nat
  for +end: Nat
  for +ie: {index2 == index : Nat}
  for +re: {rp == rp2 : +List<Nat>}
  for +pop: popOn(grammar, input, root, Gll.CKey{Gll.TBr{index2, rp}, i}, end)
  popOn(grammar, input, root, Gll.CKey{Gll.TBr{index, rp2}, i}, end)

def pop_br_move(grammar, input, root, index2, index, rp, rp2, i, end, ie, re, pop):
  %%ie : popOn(grammar, input, root, Gll.CKey{Gll.TBr{_, rp2}, i}, end)
  %%re : popOn(grammar, input, root, Gll.CKey{Gll.TBr{index2, _}, i}, end)
  pop

law resume_br:
''' + TB + '''  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +d: descOn(grammar, input, root, Gll.Desc{index, rpath, dot, k, i})
  for +pop: popOn(grammar, input, root, Gll.CKey{Gll.TBr{index, dot <> rpath}, i}, end)
  AllOn(grammar, input, root, PS.pairWhen(%(pr)s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end)))

def resume_br(%(tba)s, index, rpath, dot, k, i, end, d, pop):
  match d:
    case (p0c, (gc, (f2, (occ2, (fitF2, (spF2, (inF2, finF2))))))):
      match pop:
        case (a, (p0, (g, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, (gAt, ri)))))))))), endEq)))):
          +sq = seq_of(rpath, grammar, input, root, index, k, p0c, gc, occ2)
          +even = N1_and_left({L.evenLength(%(p)s) == True{} : Bool}, {Spec.sequenceAt(grammar, index, %(p)s) == %(seq)s : +List<Spec.Item>}, sq)
          +seqEq = N1_and_right({L.evenLength(%(p)s) == True{} : Bool}, {Spec.sequenceAt(grammar, index, %(p)s) == %(seq)s : +List<Spec.Item>}, sq)
          +fe = suffix_same(%(tba)s, index, rpath, dot, kc, k, i, ff, f2, even, seqEq, fitF, fitF2, spF, spF2, inF, inF2)
          +ri2 = move_round(grammar, input, root, ff, f2, fe, index, rpath, dot, a, i, p0, g, kind, alts, ri)
          resume_br_f(f2, Gll.admits(%(pr)s, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}), %(tba)s, index, rpath, dot, k, i, end, p0c, gc, occ2, fitF2, spF2, inF2, finF2, kind, alts, itEqP, seqEq, a, p0, g, ri2, endEq, {==})

# A return edge on the tree, resumed at a pop on the tree.
law resume_on:
  for key: Gll.CKey
  for edge: Gll.Edge
''' + TB + '''  for +end: Nat
  for +here: returnOn(grammar, input, root, key, edge)
  for +pop: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, PS.resumeGives(%(pr)s, grammar, input, key, edge, end))

def resume_on(key, edge, %(tba)s, end, here, pop):
  match key edge:
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      match here:
        case ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq):
          resume_nt(f, %(tba)s, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, y, end, itEq, pop)
    case Gll.CKey{Gll.TBr{+index2, +rp}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      match here:
        case (kindR, (altsR, (d, (ie, (re, itEqR))))):
          resume_br(%(tba)s, index, rpath, dot, k, i, end, d, pop_br_move(grammar, input, root, index2, index, rp, dot <> rpath, i, end, ie, re, pop))
''') % {'pr': PR, 'tba': TBA, 'p': P, 'seq': SEQ}
open('m9d.bend', 'w').write(s)
