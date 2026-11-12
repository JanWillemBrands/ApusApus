
law step_at_eq:
  for +index: Nat
  for +rpath: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Gll.stepAt(index, rpath, d, i, k, j) == Spec.at(index, prefixOf(rpath), d, i, k, j) : Spec.Bsr}

def step_at_eq(index, rpath, d, i, k, j):
  Equal.cong(+List<Nat>, Spec.Bsr, v => Spec.Bsr{Spec.Slot{index, v}, i, k, j}, Gll.reverseOnto(rpath, [d]), List.append(&2, Nat, prefixOf(rpath), [d]), G.rev_onto(rpath, [d]))

# Entering the bracket: two choices in the table's list there that admit the token.
law enter_conflict:
  for +kind: Spec.Bracket
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +alts: +List<+List<Spec.Item>>
  for +c1: Nat
  for +c2: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(c1, c2) == False{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(R)) == Gll.seqAt(grammar, index, R) : +List<Spec.Item>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for h1: L.HasAt(c1, next, LL1.enterChoices(kind, grammar, t, index, R, dot, alts))
  for h2: L.HasAt(c2, next, LL1.enterChoices(kind, grammar, t, index, R, dot, alts))
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def enter_conflict(kind, grammar, t, index, R, dot, alts, c1, c2, next, neq, seqEq, itEq, h1, h2):
  +point = {Spec.BracketAt{index, Gll.reverseOnto(R, []), dot} : Spec.ChoicePoint}
  local_conflict(grammar, t, index, R, dot, kind, alts, seqEq, itEq,
    L.nonempty_left(LL1.conflictsAmong(point, LL1.enterChoices(kind, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(kind, grammar, t, index, R, dot, alts),
      L.among_hit(point, LL1.enterChoices(kind, grammar, t, index, R, dot, alts), c1, c2, next, neq, h1, h2)))

# After a round of < >.
law after_conflict:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +alts: +List<+List<Spec.Item>>
  for +c1: Nat
  for +c2: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(c1, c2) == False{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(R)) == Gll.seqAt(grammar, index, R) : +List<Spec.Item>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for h1: L.HasAt(c1, next, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts))
  for h2: L.HasAt(c2, next, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts))
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def after_conflict(grammar, t, index, R, dot, alts, c1, c2, next, neq, seqEq, itEq, h1, h2):
  +point = {Spec.AfterRoundAt{index, Gll.reverseOnto(R, []), dot} : Spec.ChoicePoint}
  local_conflict(grammar, t, index, R, dot, Spec.Positive{}, alts, seqEq, itEq,
    L.nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Positive{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Positive{}, grammar, t, index, R, dot, alts),
      L.among_hit(point, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts), c1, c2, next, neq, h1, h2)))

# An alternate in the table's list of choices.
law alt_has:
  for +mayBeEmpty: Bool
  for +leave: Bool
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +alts: +List<+List<Spec.Item>>
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for +isA: {Nat.is_lt(c, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +hs: {Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> (dot <> R), Spec.altOf(alts, c))) == True{} : Bool}
  L.HasAt(c, next, LL1.choicesWith(mayBeEmpty, leave, grammar, t, index, R, dot, alts))

def alt_has(mayBeEmpty, leave, grammar, t, index, R, dot, alts, c, next, isA, hs):
  L.has_append_left(c, next, LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n), LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)}),
    L.alternates_in(alts, c, mayBeEmpty, grammar, t, index, dot <> R, 0n, c, next, Equal.sym(Nat, Nat.add(c, 0n), c, Lemma.add_zero_right(c)), isA, hs))

# Leaving, in the table's list of choices.
law leave_has2:
  for +mayBeEmpty: Bool
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +alts: +List<+List<Spec.Item>>
  for +next: Maybe<&2, Nat>
  for +hs: {Gll.lsHas(next, Gll.predictAt(grammar, t, index, R, 1n+dot)) == True{} : Bool}
  L.HasAt(List.length(&2, +List<Spec.Item>, alts), next, LL1.choicesWith(mayBeEmpty, True{}, grammar, t, index, R, dot, alts))

def leave_has2(mayBeEmpty, grammar, t, index, R, dot, alts, next, hs):
  +n = List.length(&2, +List<Spec.Item>, alts)
  L.has_append_right(n, next, LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n), LL1.leavePick(True{}, LL1.Predicted{n, Gll.predictAt(grammar, t, index, R, 1n+dot)}),
    L.leave_pick_has(True{}, n, n, Gll.predictAt(grammar, t, index, R, 1n+dot), next, {==}, {==}, hs))

# What follows the bracket in the tree predicts leaving it: the token after the bracket's
# tree X is in the table set for leaving.
law leave_set:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +e: Nat
  for +x: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(R)) == Gll.seqAt(grammar, index, R) : +List<Spec.Item>}
  for +fitF: {Spec.fits(x <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, R))) == True{} : Bool}
  for +fitT: {Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R))) == True{} : Bool}
  for +spT: G.Spells(ts, input, e)
  for +inF: {Spec.allIn(Spec.walk(x <> ts, False{}, index, prefixOf(R), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finX: {Nat.add(i, List.length(&2, Nat, Spec.leaves(x <> ts))) == Nat.add(e, List.length(&2, Nat, Spec.leaves(ts))) : Nat}
  {Gll.lsHas(List.get(&2, Nat, input, e), Gll.predictAt(grammar, t, index, R, 1n+dot)) == True{} : Bool}

def leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, R, dot, k, i, e, x, ts, seqEq, fitF, fitT, spT, inF, finX):
  +p = prefixOf(R)
  +seqR = Gll.seqAt(grammar, index, R)
  +rest = Gll.dropFrom(1n+dot, seqR)
  +fin = Nat.add(e, List.length(&2, Nat, Spec.leaves(ts)))
  +next = List.get(&2, Nat, input, e)
  +itemsEq = Equal.trans(+List<Spec.Item>, Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(dot, seqR),
    L.items_from_eq(dot, Spec.sequenceAt(grammar, index, p)), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(dot, v), Spec.sequenceAt(grammar, index, p), seqR, seqEq))
  +ws = Spec.walk(x <> ts, False{}, index, p, dot, k, i)
  L.predicts_sound(grammar, start, t, po, rest, index, p, R, {==}, next,
    U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ts, rest, index, p, p, e, k, fin, ws, fitT, spT, {==}, {==}, {==},
      U.end_walk(x <> ts, Gll.dropFrom(dot, seqR), dot, grammar, index, p, k, i, fin, fitF, itemsEq, finX, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, x <> ts)), {==})), inF))

# A round on the tree predicts its alternate: the token where it starts is in the table's
# full predict set of its first slot.
law round_predict_set:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rp: +List<Nat>
  for +k: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +gAt: GAt(grammar, input, root, index, rp, k, p0, g)
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rp)) == Gll.seqAt(grammar, index, rp) : +List<Spec.Item>}
  {Gll.lsHas(List.get(&2, Nat, input, p0), Gll.predictAt(grammar, t, index, rp, 0n)) == True{} : Bool}

def round_predict_set(grammar, start, t, po, input, root, rootFit, rootSp, index, rp, k, p0, g, gAt, seqEq):
  match gAt:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Gll.seqAt(grammar, index, rp)) == True{} : Bool}}
      +sp = {sp0 : G.Spells(g, input, p0)}
      +inG = {in0 : {Spec.allIn(Spec.walk(g, False{}, index, prefixOf(rp), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}}
      +p = prefixOf(rp)
      +items = Gll.seqAt(grammar, index, rp)
      +fin = Nat.add(p0, List.length(&2, Nat, Spec.leaves(g)))
      +next = List.get(&2, Nat, input, p0)
      L.predicts_sound(grammar, start, t, po, items, index, p, rp, {==}, next,
        U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, g, items, index, p, p, p0, k, fin, Spec.walk(g, False{}, index, p, 0n, k, p0), fit, sp, {==}, {==}, {==},
          U.end_walk(g, items, 0n, grammar, index, p, k, p0, fin, fit, seqEq, {==}, {==}), inG))

# A round on the tree that reads something: the token where it starts is in the table's
# FIRST of its alternate.
law round_first_set:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +fit: {Spec.fits(g, grammar, items) == True{} : Bool}
  for +sp: G.Spells(g, input, p0)
  for +reads: {Bool.not(List.is_empty(&2, Nat, Spec.leaves(g))) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, p0), Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}

def round_first_set(grammar, start, t, po, input, items, p0, g, fit, sp, reads):
  +pc = Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po)
  +next = List.get(&2, Nat, input, p0)
  L.first_of_sound(grammar, t, pc, items, next, U.first_from(Spec.leaves(g), next, grammar, input, g, items, p0, fit, {==}, sp, {==}, reads))
