
# ======== EXACT SETS ARE IN THE TABLES ========

law follow_at_tree:
  for tree: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for +input: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for +hit: {Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, j), Spec.steps(tree, 0n)) == True{} : Bool}
  for +nextEq: {List.get(&2, Nat, input, j) == next : Maybe<&2, Nat>}
  {Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}

def follow_at_tree(tree, grammar, start, t, po, index, prefix, rpath, rEq, next, input, i, k, j, fitting, spelled, hit, nextEq):
      match tree:
        case Spec.Leaf{kind}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Node{+q, +ch}:
          +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, True{}, fitting)
          +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +lch = Spec.leaves(ch)
          +spCh = G.root_spells(input, q, ch, spelled)
          +sameL = Equal.trans(+List<Nat>, lch, List.append(&2, Nat, lch, []), input, Equal.sym(+List<Nat>, List.append(&2, Nat, lch, []), lch, Lemma.append_nil_right(lch)), spelled)
          +finCh = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), lch, input, sameL)
          +ctxCh = Pr.root_ctx(Gll.Predict{t}, grammar, start, input, q, po, lhsOk)
          +foCh = Pr.fo_node(Gll.Predict{t}, grammar, start, q, start, po, lhsOk)
          +got = follow_walk(ch, False{}, grammar, start, t, po, input, index, prefix, i, k, j, rpath, rEq, q, [], [], [], 0n, 0n, 0n, Gll.nestFuel(), List.length(&2, Nat, input), Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, spCh, ({==}, (fitCh, (finCh, (ctxCh, (foCh, ({==}, {==})))))), hit)
          Equal.trans(Bool, Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)), Gll.lsHas(List.get(&2, Nat, input, j), Gll.contextAfter(grammar, t, index, rpath)), True{},
            Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.contextAfter(grammar, t, index, rpath)), next, List.get(&2, Nat, input, j), Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, input, j), next, nextEq)), got)
        case Spec.Pick{a, ch}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Skip{}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Loop{rs}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))

# FOLLOW from parse trees: the token is in the tables' context for the sequence.
law follow_at_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for fol: Spec.FollowAt(grammar, start, index, prefix, next)
  {Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}

def follow_at_sound(grammar, start, t, po, index, prefix, rpath, rEq, next, fol):
  match fol:
    case (input, (tree, (i, (k, (j, (fitting, (spelled, (hit, nextEq)))))))):
      follow_at_tree(tree, grammar, start, t, po, index, prefix, rpath, rEq, next, input, i, k, j, fitting, spelled, hit, nextEq)

# FIRST from derivations: the token is in the tables' FIRST of the items.
law first_of_sound:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +items: +List<Spec.Item>
  for next: Maybe<&2, Nat>
  for f: Spec.FirstOf(grammar, items, next)
  {Gll.lsHas(next, Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}

def first_of_sound(grammar, t, pc, items, next, f):
  match next:
    case None{}:
      Empty.absurd({Gll.lsHas(None{}, Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}, f)
    case Some{+token}:
      match f:
        case (rest, (forest, (fit, lv))):
          Tab.first_sound(forest, Gll.nestFuel(), items, grammar, t, pc, fit, token, rest, lv)

law predicts_by:
  for viaFirst: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for by: Spec.PredictsBy(viaFirst, grammar, start, items, index, prefix, next)
  {Gll.lsHas(next, Gll.restOr(Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath))) == True{} : Bool}

def predicts_by(viaFirst, grammar, start, t, po, items, index, prefix, rpath, rEq, next, by):
  match viaFirst:
    case True{}:
      Sets.rest_or_first(next, Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath),
        first_of_sound(grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), items, next, by))
    case False{}:
      match by:
        case ((forest, (fit, empty)), fol):
          Sets.rest_or_after(next, Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath),
            Tab.nul_sound(forest, Gll.nestFuel(), items, grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), fit, empty),
            follow_at_sound(grammar, start, t, po, index, prefix, rpath, rEq, next, fol))

# PREDICT: the token is in the tables' set for the items followed by the sequence's end.
law predicts_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for p: Spec.Predicts(grammar, start, items, index, prefix, next)
  {Gll.lsHas(next, Gll.restOr(Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath))) == True{} : Bool}

def predicts_sound(grammar, start, t, po, items, index, prefix, rpath, rEq, next, p):
  match p:
    case (viaFirst, by):
      predicts_by(viaFirst, grammar, start, t, po, items, index, prefix, rpath, rEq, next, by)

