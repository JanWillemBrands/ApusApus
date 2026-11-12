TB = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
'''
TBA = 'grammar, start, t, po, noConf, input, root, rootFit, rootSp'
PR = 'Gll.Predict{t}'
d = {'tba': TBA, 'pr': PR}
s = ('''
# ======== WHAT A FACT ON THE TREE GIVES ========

law pop_moved:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +key: Gll.CKey
  for +popKey: Gll.CKey
  for +end: Nat
  for +pk: {key == popKey : Gll.CKey}
  for +pop: popOn(grammar, input, root, popKey, end)
  popOn(grammar, input, root, key, end)

def pop_moved(grammar, input, root, key, popKey, end, pk, pop):
  +kp = Equal.sym(Gll.CKey, key, popKey, pk)
  %%kp : popOn(grammar, input, root, _, end)
  pop

law return_moved:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +key: Gll.CKey
  for +edgeKey: Gll.CKey
  for +edge: Gll.Edge
  for +ek: {key == edgeKey : Gll.CKey}
  for +here: returnOn(grammar, input, root, edgeKey, edge)
  returnOn(grammar, input, root, key, edge)

def return_moved(grammar, input, root, key, edgeKey, edge, ek, here):
  +ke = Equal.sym(Gll.CKey, key, edgeKey, ek)
  %%ke : returnOn(grammar, input, root, _, edge)
  here

law edge_when:
  for same: Bool
''' + TB + '''  for +key: Gll.CKey
  for +popKey: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(key, popKey) == same : Bool}
  for +here: returnOn(grammar, input, root, key, edge)
  for +pop: popOn(grammar, input, root, popKey, end)
  AllOn(grammar, input, root, Support.whenTrue(same, PS.resumeGives(%(pr)s, grammar, input, key, edge, end)))

def edge_when(same, %(tba)s, key, popKey, edge, end, sameEq, here, pop):
  match same:
    case True{}:
      +pk = G.key_eq_sound(key, popKey, sameEq)
      resume_on(key, edge, %(tba)s, end, here, pop_moved(grammar, input, root, key, popKey, end, pk, pop))
    case False{}:
      {==}

# A return edge against the pops reached.
law edge_on:
  for reached: +List<Support.Fact>
''' + TB + '''  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +here: returnOn(grammar, input, root, key, edge)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.edgeGives(%(pr)s, grammar, input, reached, key, edge))

def edge_on(reached, %(tba)s, key, edge, here, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactPop{+popKey, +end}, +rest}:
      match all:
        case (h0, t0):
          +h = {h0 : popOn(grammar, input, root, popKey, end)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(Support.whenTrue(Gll.keyEq(key, popKey), PS.resumeGives(%(pr)s, grammar, input, key, edge, end)), PS.edgeGives(%(pr)s, grammar, input, rest, key, edge), grammar, input, root,
            edge_when(Gll.keyEq(key, popKey), %(tba)s, key, popKey, edge, end, {==}, here, h),
            edge_on(rest, %(tba)s, key, edge, here, tl))
''') % d
for pat, ty in (('Support.FactDescriptor{+x}', 'descOn(grammar, input, root, x)'), ('Support.FactCluster{+x}', 'clusterOn(grammar, input, root, x)'),
                ('Support.FactReturn{+k2, +e2}', 'returnOn(grammar, input, root, k2, e2)'), ('Support.FactStep{+y}', '{Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}')):
    s += '''    case Con{%s, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          edge_on(rest, %s, key, edge, here, tl)
''' % (pat, TBA)
s += ('''
law pop_when:
  for same: Bool
''' + TB + '''  for +edgeKey: Gll.CKey
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(edgeKey, key) == same : Bool}
  for +ret: returnOn(grammar, input, root, edgeKey, edge)
  for +pop: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, Support.whenTrue(same, PS.resumeGives(%(pr)s, grammar, input, edgeKey, edge, end)))

def pop_when(same, %(tba)s, edgeKey, key, edge, end, sameEq, ret, pop):
  match same:
    case True{}:
      +ek = G.key_eq_sound(edgeKey, key, sameEq)
      resume_on(edgeKey, edge, %(tba)s, end, ret, pop_moved(grammar, input, root, edgeKey, key, end, ek, pop))
    case False{}:
      {==}

# A pop against the return edges reached.
law pop_on:
  for reached: +List<Support.Fact>
''' + TB + '''  for +key: Gll.CKey
  for +end: Nat
  for +pop: popOn(grammar, input, root, key, end)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.popGives(%(pr)s, grammar, input, reached, key, end))

def pop_on(reached, %(tba)s, key, end, pop, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactReturn{+edgeKey, +edge}, +rest}:
      match all:
        case (h0, t0):
          +h = {h0 : returnOn(grammar, input, root, edgeKey, edge)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(Support.whenTrue(Gll.keyEq(edgeKey, key), PS.resumeGives(%(pr)s, grammar, input, edgeKey, edge, end)), PS.popGives(%(pr)s, grammar, input, rest, key, end), grammar, input, root,
            pop_when(Gll.keyEq(edgeKey, key), %(tba)s, edgeKey, key, edge, end, {==}, h, pop),
            pop_on(rest, %(tba)s, key, end, pop, tl))
''') % d
for pat in ('Support.FactDescriptor{+x}', 'Support.FactCluster{+x}', 'Support.FactPop{+k2, +j2}', 'Support.FactStep{+y}'):
    s += '''    case Con{%s, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          pop_on(rest, %s, key, end, pop, tl)
''' % (pat, TBA)

s += ('''
# What a fact on the tree gives, with facts reached that are all on it, is on it.
law fact_on:
  for fact: Support.Fact
''' + TB + '''  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +reached: +List<Support.Fact>
  for +here: On(grammar, input, root, fact)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.factGives(fact, %(pr)s, grammar, input, reached))

def fact_on(fact, %(tba)s, plain, reached, here, all):
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, Nil{}, +dot, +k, +i}}:
      match here:
        case (x, (g, (f, (lhs, (node, (fitF, (spF, (inF, finF)))))))):
          item_on(Gll.nthItem(Spec.rhsOf(grammar, index), dot), f, grammar, input, root, %(pr)s, plain, index, dot, k, i, x, g, lhs, node, fitF, spF, inF, finF, {==})
    case Support.FactDescriptor{Gll.Desc{+index, Con{+a, +r}, +dot, +k, +i}}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactDescriptor{Gll.Desc{index, a <> r, dot, k, i}}, %(pr)s, grammar, input, reached)), Lemma.false_is_not_true(here))
    case Support.FactCluster{Gll.CKey{Gll.TNt{+x}, +i}}:
      match here:
        case (q, (g, (lhsQ, node))):
          seeds_on(grammar, 0n, %(tba)s, x, i, q, g, lhsQ, node, {==})
    case Support.FactCluster{Gll.CKey{Gll.TBr{+index, +rpath}, +i}}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactCluster{Gll.CKey{Gll.TBr{index, rpath}, i}}, %(pr)s, grammar, input, reached)), Lemma.false_is_not_true(here))
    case Support.FactReturn{+key, +edge}:
      edge_on(reached, %(tba)s, key, edge, here, all)
    case Support.FactPop{Gll.CKey{Gll.TNt{+x}, +k}, +end}:
      +key = {Gll.CKey{Gll.TNt{x}, k} : Gll.CKey}
      on_append(PS.popGives(%(pr)s, grammar, input, reached, key, end), [], grammar, input, root, pop_on(reached, %(tba)s, key, end, here, all), {==})
    case Support.FactPop{Gll.CKey{Gll.TBr{+index, +rpath}, +k}, +end}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactPop{Gll.CKey{Gll.TBr{index, rpath}, k}, end}, %(pr)s, grammar, input, reached)), Lemma.false_is_not_true(here))
    case Support.FactStep{+y}:
      {==}

# ======== GROWING THE FACTS REACHED KEEPS THEM ON THE TREE ========

law all_give_on:
  for facts: +List<Support.Fact>
''' + TB + '''  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +reached: +List<Support.Fact>
  for +here: AllOn(grammar, input, root, facts)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.allGive(facts, %(pr)s, grammar, input, reached))

def all_give_on(facts, %(tba)s, plain, reached, here, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      match here:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, fact)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(PS.factGives(fact, %(pr)s, grammar, input, reached), PS.allGive(rest, %(pr)s, grammar, input, reached), grammar, input, root,
            fact_on(fact, %(tba)s, plain, reached, h, all),
            all_give_on(rest, %(tba)s, plain, reached, tl, all))

law grow_on:
  for n: Nat
''' + TB + '''  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.grow(n, %(pr)s, grammar, input, s, reached))

def grow_on(n, %(tba)s, plain, s, reached, all):
  match n:
    case 0n:
      all
    case 1n+(+m):
      +next = PS.round(%(pr)s, grammar, input, s, reached)
      grow_on(m, %(tba)s, plain, s, next,
        on_add(PS.allGive(reached, %(pr)s, grammar, input, reached), s, reached, grammar, input, root, all_give_on(reached, %(tba)s, plain, reached, all, all), all))

# The roots are on the tree.
law roots_on:
  for tree: Spec.Tree
''' + TB.replace('for +root: Spec.Tree', 'for +root0: Spec.Tree').replace('[root]', '[tree]').replace('for +rootFit:', 'for +rootFitX:').replace('for +rootSp:', 'for +rootSpX:') + '''  AllOn(grammar, input, tree, PS.roots(%(pr)s, grammar, input, start))

def roots_on(tree, grammar, start, t, po, noConf, input, root0, rootFitX, rootSpX):
  match tree:
    case Spec.Node{+q, +ch}:
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, rootFitX)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +node = {(fitCh, (G.root_spells(input, q, ch, rootSpX), U.all_in_refl(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)))) : NodeAt(grammar, input, Spec.Node{q, ch}, q, 0n, ch)}
      ((q, (ch, (lhsQ, node))), seeds_on(grammar, 0n, grammar, start, t, po, noConf, input, Spec.Node{q, ch}, rootFitX, rootSpX, start, 0n, q, ch, lhsQ, node, {==}))
    case Spec.Leaf{kind}:
      Empty.absurd(AllOn(grammar, input, Spec.Leaf{kind}, PS.roots(%(pr)s, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Pick{a, ch}:
      Empty.absurd(AllOn(grammar, input, Spec.Pick{a, ch}, PS.roots(%(pr)s, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Skip{}:
      Empty.absurd(AllOn(grammar, input, Spec.Skip{}, PS.roots(%(pr)s, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Loop{rs}:
      Empty.absurd(AllOn(grammar, input, Spec.Loop{rs}, PS.roots(%(pr)s, grammar, input, start)), Lemma.false_is_not_true(rootFitX))

law reached_on:
  for facts: +List<Support.Fact>
  for +reached: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +found: {Support.allReached(facts, reached) == True{} : Bool}
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, facts)

def reached_on(facts, reached, grammar, input, root, found, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      (found_on(reached, fact, grammar, input, root, all, Lemma.and_true_left(Support.factIn(fact, reached), Support.allReached(rest, reached), found)),
        reached_on(rest, reached, grammar, input, root, Lemma.and_true_right_side(Support.factIn(fact, reached), Support.allReached(rest, reached), found), all))

# A STATE SUPPORTED WITH PREDICTION IS ON THE TREE.
law supported_on:
''' + TB + '''  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +s: Gll.GState
  for +sup: {PS.supportedWith(%(pr)s, grammar, start, input, s) == True{} : Bool}
  AllOn(grammar, input, root, Support.factsOf(s))

def supported_on(%(tba)s, plain, s, sup):
  +facts = Support.factsOf(s)
  +first = Support.addWithin(PS.roots(%(pr)s, grammar, input, start), s, [])
  +reached = PS.grow(List.length(&2, Support.Fact, facts), %(pr)s, grammar, input, s, first)
  reached_on(facts, reached, grammar, input, root, sup,
    grow_on(List.length(&2, Support.Fact, facts), %(tba)s, plain, s, first,
      on_add(PS.roots(%(pr)s, grammar, input, start), s, [], grammar, input, root, roots_on(root, %(tba)s), {==})))
''') % d
open('n7.bend', 'w').write(s)
