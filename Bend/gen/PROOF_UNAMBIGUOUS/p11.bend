
# ======== TWO PARSE TREES ========

law root_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -t1: Spec.Tree
  for -t2: Spec.Tree
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  Either<{t1 == t2 : Spec.Tree}, Clash(grammar, start)>

def root_clash(grammar, start, t1, t2, point, first, second, next, neq, cp1, cp2):
  Inr{(point, (first, (second, (next, (neq, (cp1, cp2))))))}

law root_then:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for r: Same(grammar, start, ch1, ch2)
  Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>

def root_then(grammar, start, q1, q2, qe, ch1, ch2, r):
  match r:
    case Inl{che}:
      Inl{Equal.trans(Spec.Tree, Spec.Node{q1, ch1}, Spec.Node{q2, ch1}, Spec.Node{q2, ch2}, Equal.cong(Nat, Spec.Tree, v => Spec.Node{v, ch1}, q1, q2, qe), Equal.cong(+List<Spec.Tree>, Spec.Tree, v => Spec.Node{q2, v}, ch1, ch2, che))}
    case Inr{c}:
      Inr{c}

law root_same:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +ch1: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +fit1: {Spec.fits([Spec.Node{q1, ch1}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([Spec.Node{q1, ch1}]) == input : +List<Nat>}
  for +fit2: {Spec.fits([Spec.Node{q2, ch2}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([Spec.Node{q2, ch2}]) == input : +List<Nat>}
  for +fC1: {Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}
  for +fC2: {Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}
  Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>

def root_same(grammar, start, input, q1, q2, qe, ch1, ch2, fit1, sp1, fit2, sp2, fC1, fC2):
  +root1 = {Spec.Node{q1, ch1} : Spec.Tree}
  +root2 = {Spec.Node{q2, ch2} : Spec.Tree}
  +fC2b = Equal.trans(Bool, Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(ch2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fC2)
  +in2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch2, False{}, q1, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), Spec.allIn(Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), True{},
    Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ch2, False{}, v, [], 0n, 0n, 0n), Spec.steps(root2, 0n)), q1, q2, qe), all_in_refl(Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n)))
  root_then(grammar, start, q1, q2, qe, ch1, ch2,
    compare(ch1, False{}, ch2, Spec.rhsOf(grammar, q1), grammar, start, input, root1, fit1, sp1, root2, fit2, sp2, q1, [], 0n, 0n, 0n, 0n, Spec.Group{}, [], [], False{}, 0n, 0n,
      (fC1, (fC2b, (G.root_spells(input, q1, ch1, sp1), (G.root_spells(input, q2, ch2, sp2), (all_in_refl(Spec.walk(ch1, False{}, q1, [], 0n, 0n, 0n)), (in2, ({==}, {==})))))))))

# Two parse trees of the same input: the same tree, or a clash.
law trees_same:
  for tree1: Spec.Tree
  for tree2: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input : +List<Nat>}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([tree2]) == input : +List<Nat>}
  Either<{tree1 == tree2 : Spec.Tree}, Clash(grammar, start)>

def trees_same(tree1, tree2, grammar, start, input, fit1, sp1, fit2, sp2):
  match tree1 tree2:
    case Spec.Node{+q1, +ch1} Spec.Node{+q2, +ch2}:
      +h1 = Bool.and(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)))
      +h2 = Bool.and(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)))
      +hOk1 = Lemma.and_true_left(h1, True{}, fit1)
      +hOk2 = Lemma.and_true_left(h2, True{}, fit2)
      +lhs1 = Lemma.and_true_left(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
      +lhs2 = Lemma.and_true_left(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
      +fC1 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q1, start), Spec.fits(ch1, grammar, Spec.rhsOf(grammar, q1)), hOk1)
      +fC2 = Lemma.and_true_right_side(Spec.lhsIs(grammar, q2, start), Spec.fits(ch2, grammar, Spec.rhsOf(grammar, q2)), hOk2)
      +next = List.get(&2, Nat, input, 0n)
      +w1 = Spec.walk(ch1, False{}, q1, [], 0n, 0n, 0n)
      +w2 = Spec.walk(ch2, False{}, q2, [], 0n, 0n, 0n)
      +n1 = List.length(&2, Nat, Spec.leaves(ch1))
      +n2 = List.length(&2, Nat, Spec.leaves(ch2))
      cp1 = nt_cp(Spec.lhsIs(grammar, q1, start), grammar, start, q1, next, lhs1,
        predicts_in(next, grammar, start, input, Spec.Node{q1, ch1}, fit1, sp1, ch1, Spec.rhsOf(grammar, q1), q1, [], [], 0n, 0n, n1, w1, fC1, G.root_spells(input, q1, ch1, sp1), {==}, {==}, {==},
          end_walk(ch1, Spec.rhsOf(grammar, q1), 0n, grammar, q1, [], 0n, 0n, n1, fC1, {==}, {==}, {==}), all_in_refl(w1)))
      cp2 = nt_cp(Spec.lhsIs(grammar, q2, start), grammar, start, q2, next, lhs2,
        predicts_in(next, grammar, start, input, Spec.Node{q2, ch2}, fit2, sp2, ch2, Spec.rhsOf(grammar, q2), q2, [], [], 0n, 0n, n2, w2, fC2, G.root_spells(input, q2, ch2, sp2), {==}, {==}, {==},
          end_walk(ch2, Spec.rhsOf(grammar, q2), 0n, grammar, q2, [], 0n, 0n, n2, fC2, {==}, {==}, {==}), all_in_refl(w2)))
      L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, Either<{Spec.Node{q1, ch1} == Spec.Node{q2, ch2} : Spec.Tree}, Clash(grammar, start)>, decide(Nat.is_eq(q1, q2), q1, q2, {==}),
        qe => root_same(grammar, start, input, q1, q2, qe, ch1, ch2, fit1, sp1, fit2, sp2, fC1, fC2),
        neq => root_clash(grammar, start, Spec.Node{q1, ch1}, Spec.Node{q2, ch2}, Spec.NonterminalAt{start}, q1, q2, next, neq, cp1, cp2))
    case Spec.Node{q1, ch1} Spec.Leaf{k}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Leaf{k} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Pick{a, ch}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Pick{a, ch} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Skip{}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Skip{} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Node{q1, ch1} Spec.Loop{rs}:
      Empty.absurd(Either<{Spec.Node{q1, ch1} == Spec.Loop{rs} : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit2))
    case Spec.Leaf{k} t2:
      Empty.absurd(Either<{Spec.Leaf{k} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Pick{a, ch} t2:
      Empty.absurd(Either<{Spec.Pick{a, ch} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Skip{} t2:
      Empty.absurd(Either<{Spec.Skip{} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))
    case Spec.Loop{rs} t2:
      Empty.absurd(Either<{Spec.Loop{rs} == t2 : Spec.Tree}, Clash(grammar, start)>, Lemma.false_is_not_true(fit1))

# LL(1) rules out the clash.
law no_clash:
  for -grammar: +List<Spec.Production>
  for -start: Nat
  for -t1: Spec.Tree
  for -t2: Spec.Tree
  for r: Either<{t1 == t2 : Spec.Tree}, Clash(grammar, start)>
  for ll1: Spec.LL1(grammar, start)
  {t1 == t2 : Spec.Tree}

def no_clash(grammar, start, t1, t2, r, ll1):
  match r:
    case Inl{e}:
      e
    case Inr{c}:
      match c:
        case (point, (first, (second, (next, (neq, (cp1, cp2)))))):
          Empty.absurd({t1 == t2 : Spec.Tree}, ll1(point, first, second, next, neq, cp1, cp2))

# AN LL(1) GRAMMAR IS UNAMBIGUOUS.
law ll1_unambiguous:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for tree1: Spec.Tree
  for tree2: Spec.Tree
  for ll1: Spec.LL1(grammar, start)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input : +List<Nat>}
  for +sp2: {Spec.leaves([tree2]) == input : +List<Nat>}
  {tree1 == tree2 : Spec.Tree}

def ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, fit1, fit2, sp1, sp2):
  no_clash(grammar, start, tree1, tree2, trees_same(tree1, tree2, grammar, start, input, fit1, sp1, fit2, sp2), ll1)
