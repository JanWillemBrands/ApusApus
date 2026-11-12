exec(open('common.py').read())
IHL = lambda f: '(ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(%s, ro, la, it, %s, ix, px, dx, ii, kx, kd, al, rO, ex, rd))' % (f, TBA)
CTXN = CTX.replace('  for +later: Bool\n', '')
CTXNA = 'index, prefix, dot, i, k, kind, alts, restO, E'
s = '''
# ======== EVERY CHOICE OF A FOREST PREDICTS ========

law made_ok:
  for f: +List<Spec.Tree>
  for rounds: Bool
  for later: Bool
  for +items: +List<Spec.Item>
''' + TB + CTXN + '''  for ready: Ready(rounds, grammar, start, input, root, f, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  AllOk(grammar, start, input, Spec.madeIn(grammar, f, rounds, later, index, prefix, dot, k))

def made_ok(f, rounds, later, items, %(tba)s, %(ctxa)s, ready):
  match f rounds:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      rounds_nil_ok(kind, later, %(tba)s, index, prefix, dot, i, k, alts, restO, E, ready)
    case Con{Spec.Leaf{+a}, +ts} False{}:
      leaf_ok(items, %(tba)s, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ts, ready, %(ihTs)s)
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      node_ok(items, %(tba)s, index, prefix, dot, i, k, kind, alts, restO, later, E, q, ch, ts, ready, %(ihCh)s, %(ihTs)s)
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      pick_ok(items, %(tba)s, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ch, ts, ready, %(ihCh)s, %(ihTs)s)
    case Con{Spec.Skip{}, +ts} False{}:
      skip_ok(items, %(tba)s, index, prefix, dot, i, k, kind, alts, restO, later, E, ts, ready, %(ihTs)s)
    case Con{Spec.Loop{+rs}, +ts} False{}:
      loop_ok(items, %(tba)s, index, prefix, dot, i, k, kind, alts, restO, later, E, rs, ts, ready, %(ihRs)s, %(ihTs)s)
    case Con{Spec.Pick{+a, +ch}, +r} True{}:
      rounds_pick_ok(kind, later, %(tba)s, index, prefix, dot, i, k, alts, restO, E, a, ch, r, ready, %(ihCh)s, %(ihR)s)
    case Con{Spec.Leaf{x}, r} True{}:
      {==}
    case Con{Spec.Node{q, ch}, r} True{}:
      {==}
    case Con{Spec.Skip{}, r} True{}:
      {==}
    case Con{Spec.Loop{rs}, r} True{}:
      {==}

# Every choice a parse tree makes predicts the token where it is made.
law choices_ok:
  for tree: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  AllOk(grammar, start, input, Spec.choicesMade(grammar, start, tree))

def choices_ok(tree, grammar, start, input, fit, sp):
  match tree:
    case Spec.Node{+q, +ch}:
      +root = {Spec.Node{q, ch} : Spec.Tree}
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, fit)
      +lhs = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fC = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +spC = G.root_spells(input, q, ch, sp)
      +wC = Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)
      +inC = U.all_in_refl(wC)
      +e = Nat.add(0n, List.length(&2, Nat, Spec.leaves(ch)))
      +next = List.get(&2, Nat, input, 0n)
      cp = U.nt_cp(Spec.lhsIs(grammar, q, start), grammar, start, q, next, lhs,
        U.predicts_in(next, grammar, start, input, root, fit, sp, ch, Spec.rhsOf(grammar, q), q, [], [], 0n, 0n, e, wC, fC, spC, {==}, {==}, {==},
          U.end_walk(ch, Spec.rhsOf(grammar, q), 0n, grammar, q, [], 0n, 0n, e, fC, {==}, {==}, {==}), inC))
      (cp, made_ok(ch, False{}, False{}, Spec.rhsOf(grammar, q), grammar, start, input, root, fit, sp, q, [], 0n, 0n, 0n, Spec.Group{}, [], [], 0n, (fC, (spC, (inC, ({==}, {==}))))))
    case Spec.Leaf{kind}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Pick{a, ch}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Skip{}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Loop{rs}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))

law transport_cp:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +c: Maybe<&2, Spec.Choice>
  for +n1: Maybe<&2, Nat>
  for +n2: Maybe<&2, Nat>
  for +e: {n1 == n2 : Maybe<&2, Nat>}
  for cp: Spec.ChoicePredicts(grammar, start, c, n1)
  Spec.ChoicePredicts(grammar, start, c, n2)

def transport_cp(grammar, start, c, n1, n2, e, cp):
  %%e : Spec.ChoicePredicts(grammar, start, c, _)
  cp

# ======== THE LAW ========

law ll1_at:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input1: +List<Nat>
  for +input2: +List<Nat>
  for +tree1: Spec.Tree
  for +tree2: Spec.Tree
  for +point: Spec.ChoicePoint
  for +pos: Nat
  for +choice1: Nat
  for +choice2: Nat
  for ll1: Spec.LL1At(grammar, start, point)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input1 : +List<Nat>}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([tree2]) == input2 : +List<Nat>}
  for +next: {List.get(&2, Nat, input1, pos) == List.get(&2, Nat, input2, pos) : Maybe<&2, Nat>}
  for made1: Spec.Among(Spec.Made{point, pos, choice1}, Spec.choicesMade(grammar, start, tree1))
  for made2: Spec.Among(Spec.Made{point, pos, choice2}, Spec.choicesMade(grammar, start, tree2))
  {choice1 == choice2 : Nat}

def ll1_at(grammar, start, input1, input2, tree1, tree2, point, pos, choice1, choice2, ll1, fit1, sp1, fit2, sp2, next, made1, made2):
  +n1 = List.get(&2, Nat, input1, pos)
  +n2 = List.get(&2, Nat, input2, pos)
  ok1 = among_ok(Spec.choicesMade(grammar, start, tree1), Spec.Made{point, pos, choice1}, grammar, start, input1, made1, choices_ok(tree1, grammar, start, input1, fit1, sp1))
  ok2 = among_ok(Spec.choicesMade(grammar, start, tree2), Spec.Made{point, pos, choice2}, grammar, start, input2, made2, choices_ok(tree2, grammar, start, input2, fit2, sp2))
  L.either_case({choice1 == choice2 : Nat}, {Nat.is_eq(choice1, choice2) == False{} : Bool}, {choice1 == choice2 : Nat}, U.decide(Nat.is_eq(choice1, choice2), choice1, choice2, {==}),
    same => same,
    neq => Empty.absurd({choice1 == choice2 : Nat}, ll1(choice1, choice2, n1, neq, ok1, transport_cp(grammar, start, Spec.choiceOf(grammar, point, choice2), n2, n1, Equal.sym(Maybe<&2, Nat>, n1, n2, next), ok2))))
''' % {'tba': TBA, 'ctxa': CTXNA, 'ihTs': IHL('ts'), 'ihCh': IHL('ch'), 'ihRs': IHL('rs'), 'ihR': IHL('r')}
open('d.bend', 'w').write(s.replace('%%', '%'))
