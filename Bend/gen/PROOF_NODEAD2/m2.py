FIXD = '''  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
'''
FIX = 'grammar, input, root'
out = ['''
# ======== LISTS OF FACTS ON THE TREE ========

law on_append:
  for xs: +List<Support.Fact>
  for +ys: +List<Support.Fact>
''' + FIXD + '''  for +hx: AllOn(grammar, input, root, xs)
  for +hy: AllOn(grammar, input, root, ys)
  AllOn(grammar, input, root, List.append(&2, Support.Fact, xs, ys))

def on_append(xs, ys, grammar, input, root, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      match hx:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, x)}
          +t = {t0 : AllOn(grammar, input, root, rest)}
          (h, on_append(rest, ys, grammar, input, root, t, hy))

law on_when:
  for c: Bool
  for +xs: +List<Support.Fact>
''' + FIXD + '''  for +h: AllOn(grammar, input, root, xs)
  AllOn(grammar, input, root, Support.whenTrue(c, xs))

def on_when(c, xs, grammar, input, root, h):
  match c:
    case True{}:
      h
    case False{}:
      {==}

law on_keep:
  for keep: Bool
  for +fact: Support.Fact
  for +facts: +List<Support.Fact>
''' + FIXD + '''  for +here: On(grammar, input, root, fact)
  for +all: AllOn(grammar, input, root, facts)
  AllOn(grammar, input, root, Support.keepPick(keep, fact, facts))

def on_keep(keep, fact, facts, grammar, input, root, here, all):
  match keep:
    case True{}:
      (here, all)
    case False{}:
      all

law on_add:
  for new: +List<Support.Fact>
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
''' + FIXD + '''  for +here: AllOn(grammar, input, root, new)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, Support.addWithin(new, s, reached))

def on_add(new, s, reached, grammar, input, root, here, all):
  match new:
    case Nil{}:
      all
    case Con{+fact, +rest}:
      match here:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, fact)}
          +t = {t0 : AllOn(grammar, input, root, rest)}
          +keep = Bool.and(Support.inState(fact, s), Bool.not(Support.factIn(fact, reached)))
          on_add(rest, s, Support.keepPick(keep, fact, reached), grammar, input, root, t, on_keep(keep, fact, reached, grammar, input, root, h, all))

law step_equal_on:
  for +x: Spec.Bsr
  for +y: Spec.Bsr
''' + FIXD + '''  for c: Either<{x == y : Spec.Bsr}, {Spec.bsrMember(x, []) == True{} : Bool}>
  for +hb: {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}
  {Spec.bsrMember(x, Spec.steps(root, 0n)) == True{} : Bool}

def step_equal_on(x, y, grammar, input, root, c, hb):
  match c:
    case Inl{same}:
      Equal.trans(Bool, Spec.bsrMember(x, Spec.steps(root, 0n)), Spec.bsrMember(y, Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), x, y, same), hb)
    case Inr{never}:
      Empty.absurd({Spec.bsrMember(x, Spec.steps(root, 0n)) == True{} : Bool}, G.ebnf_not_in_empty(x, never))

# Equal facts: one on the tree, so the other.
law equal_on:
  for a: Support.Fact
  for b: Support.Fact
''' + FIXD + '''  for +e: {Support.factEqual(a, b) == True{} : Bool}
  for +hb: On(grammar, input, root, b)
  On(grammar, input, root, a)

def equal_on(a, b, grammar, input, root, e, hb):
  match a b:
''']
K = [('Support.FactDescriptor{+x}', 'Support.FactDescriptor{x}', 'D'), ('Support.FactCluster{+x}', 'Support.FactCluster{x}', 'C'), ('Support.FactReturn{+k1, +e1}', 'Support.FactReturn{k1, e1}', 'R'), ('Support.FactPop{+k1, +j1}', 'Support.FactPop{k1, j1}', 'P'), ('Support.FactStep{+x}', 'Support.FactStep{x}', 'S')]
K2 = [('Support.FactDescriptor{+y}', 'D'), ('Support.FactCluster{+y}', 'C'), ('Support.FactReturn{+k2, +e2}', 'R'), ('Support.FactPop{+k2, +j2}', 'P'), ('Support.FactStep{+y}', 'S')]
s = ''
for pa, ea, ka in K:
    for pb, kb in K2:
        s += '    case %s %s:\n' % (pa, pb)
        if ka != kb:
            s += '      Empty.absurd(On(grammar, input, root, %s), Lemma.false_is_not_true(e))\n' % ea
        elif ka == 'D':
            s += '''      +yx = Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e))
      %yx : descOn(grammar, input, root, _)
      hb
'''
        elif ka == 'C':
            s += '''      +yx = Equal.sym(Gll.CKey, x, y, G.key_eq_sound(x, y, e))
      %yx : clusterOn(grammar, input, root, _)
      hb
'''
        elif ka == 'R':
            s += '''      +k21 = Equal.sym(Gll.CKey, k1, k2, G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e)))
      +e21 = Equal.sym(Gll.Edge, e1, e2, G.edge_eq_sound(e1, e2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e)))
      %k21 : returnOn(grammar, input, root, _, e1)
      %e21 : returnOn(grammar, input, root, k2, _)
      hb
'''
        elif ka == 'P':
            s += '''      +k21 = Equal.sym(Gll.CKey, k1, k2, G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e)))
      +j21 = Equal.sym(Nat, j1, j2, Lemma.nat_eq_sound(j1, j2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e)))
      %k21 : popOn(grammar, input, root, _, j1)
      %j21 : popOn(grammar, input, root, k2, _)
      hb
'''
        else:
            s += '      step_equal_on(x, y, grammar, input, root, G.ebnf_member_cases(x, y, [], e), hb)\n'
out.append(s)
out.append('''
law found_on_pick:
  for +fact: Support.Fact
  for +other: Support.Fact
  for -rest: +List<Support.Fact>
''' + FIXD + '''  for c: Either<{Support.factEqual(fact, other) == True{} : Bool}, {Support.factIn(fact, rest) == True{} : Bool}>
  for +here: On(grammar, input, root, other)
  for later: {Support.factIn(fact, rest) == True{} : Bool} -> On(grammar, input, root, fact)
  On(grammar, input, root, fact)

def found_on_pick(fact, other, rest, grammar, input, root, c, here, later):
  match c:
    case Inl{same}:
      equal_on(fact, other, grammar, input, root, same, here)
    case Inr{there}:
      later(there)

# A fact found among facts that are all on the tree is on it.
law found_on:
  for facts: +List<Support.Fact>
  for +fact: Support.Fact
''' + FIXD + '''  for +all: AllOn(grammar, input, root, facts)
  for +m: {Support.factIn(fact, facts) == True{} : Bool}
  On(grammar, input, root, fact)

def found_on(facts, fact, grammar, input, root, all, m):
  match facts:
    case Nil{}:
      Empty.absurd(On(grammar, input, root, fact), Lemma.false_is_not_true(m))
    case Con{+other, +rest}:
      match all:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, other)}
          +t = {t0 : AllOn(grammar, input, root, rest)}
          found_on_pick(fact, other, rest, grammar, input, root, Lemma.or_true_cases(Support.factEqual(fact, other), Support.factIn(fact, rest), m), h,
            there => found_on(rest, fact, grammar, input, root, t, there))
''')
open('m2.bend', 'w').write(''.join(out))
