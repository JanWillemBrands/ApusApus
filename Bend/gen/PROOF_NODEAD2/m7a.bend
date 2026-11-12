
# ======== THE START OF A ROUND OF A BRACKET ON THE TREE ========

law round_seq_eq:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +a: Nat
  for +evenO: {L.evenLength(prefixOf(outer)) == True{} : Bool}
  for +seqEqO: {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}
  {Spec.sequenceAt(grammar, index, prefixOf(a <> (m <> outer))) == Gll.seqAt(grammar, index, a <> (m <> outer)) : +List<Spec.Item>}

def round_seq_eq(grammar, index, outer, m, a, evenO, seqEqO):
  +pO = prefixOf(outer)
  +longer = List.append(&2, Nat, pO, [m, a])
  Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, Gll.reverseOnto(outer, [m, a])), Spec.sequenceAt(grammar, index, longer), Gll.seqAt(grammar, index, a <> (m <> outer)),
    Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), Gll.reverseOnto(outer, [m, a]), longer, G.rev_onto(outer, [m, a])),
    L.deeper_eq(grammar, index, pO, outer, m, a, evenO, seqEqO))

# The walk of a ( ) or [ ] alternative inside the walk of the sequence around it.
law pick_child_walk:
  for +root: Spec.Tree
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +inF: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  {Spec.allIn(Spec.walk(ch, False{}, index, prefixOf(a <> (m <> outer)), 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}

def pick_child_walk(root, index, outer, m, kc, k, a, ch, ts, inF):
  +pO = prefixOf(outer)
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
  +wCh = Spec.walk(ch, False{}, index, List.append(&2, Nat, pO, [m, a]), 0n, k, k)
  +wT = Spec.walk(ts, False{}, index, pO, 1n+m, kc, e)
  +inCh = N1.all_in_left_n(wCh, wT, Spec.steps(root, 0n), N1.all_in_tail_n(Spec.at(index, pO, 1n+m, kc, k, e), List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF))
  Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, Gll.reverseOnto(outer, [m, a]), 0n, k, k), Spec.steps(root, 0n)), Spec.allIn(wCh, Spec.steps(root, 0n)), True{},
    Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), Spec.steps(root, 0n)), Gll.reverseOnto(outer, [m, a]), List.append(&2, Nat, pO, [m, a]), G.rev_onto(outer, [m, a])), inCh)

# The walk of a loop's rounds inside the walk of the sequence around it.
law loop_rounds_walk:
  for +root: Spec.Tree
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  {Spec.allIn(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}

def loop_rounds_walk(root, index, outer, m, kc, k, rs, ts, inF):
  +pO = prefixOf(outer)
  +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))
  +wR = Spec.walk(rs, True{}, index, List.append(&2, Nat, pO, [m]), 0n, k, k)
  +wT = Spec.walk(ts, False{}, index, pO, 1n+m, kc, e)
  N1.all_in_left_n(wR, wT, Spec.steps(root, 0n), N1.all_in_tail_n(Spec.at(index, pO, 1n+m, kc, k, e), List.append(&2, Spec.Bsr, wR, wT), Spec.steps(root, 0n), inF))

# The walk of one round inside the walk of the rounds from it on.
law round_child_walk:
  for +root: Spec.Tree
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +k: Nat
  for +p0: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> r, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  {Spec.allIn(Spec.walk(ch, False{}, index, prefixOf(a <> (m <> outer)), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}

def round_child_walk(root, index, outer, m, k, p0, a, ch, r, inR):
  +pO = prefixOf(outer)
  +pm = List.append(&2, Nat, pO, [m])
  +e = Nat.add(p0, List.length(&2, Nat, Spec.leaves(ch)))
  +wCh = Spec.walk(ch, False{}, index, List.append(&2, Nat, pm, [a]), 0n, k, p0)
  +wR = Spec.walk(r, True{}, index, pm, 0n, k, e)
  +inCh = N1.all_in_left_n(wCh, wR, Spec.steps(root, 0n), inR)
  +toLong = Equal.trans(+List<Nat>, Gll.reverseOnto(outer, [m, a]), List.append(&2, Nat, pO, [m, a]), List.append(&2, Nat, pm, [a]), G.rev_onto(outer, [m, a]), Equal.sym(+List<Nat>, List.append(&2, Nat, pm, [a]), List.append(&2, Nat, pO, [m, a]), G.nat_append_assoc(pO, [m], [a])))
  Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, Gll.reverseOnto(outer, [m, a]), 0n, k, p0), Spec.steps(root, 0n)), Spec.allIn(wCh, Spec.steps(root, 0n)), True{},
    Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, p0), Spec.steps(root, 0n)), Gll.reverseOnto(outer, [m, a]), List.append(&2, Nat, pm, [a]), toLong), inCh)

law alt_fits:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +a: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ch: +List<Spec.Tree>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, a <> (m <> outer))) == True{} : Bool}

def alt_fits(grammar, index, outer, m, a, kind, alts, ch, itEqB, fitCh):
  Equal.trans(Bool, Spec.fits(ch, grammar, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a)), Spec.fits(ch, grammar, Gll.bracketAlt(Some{Spec.Brack{kind, alts}}, a)), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Spec.fits(ch, grammar, Gll.bracketAlt(v, a)), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itEqB), fitCh)

# The tree's alternative of a ( ) or [ ] starts on the tree.
law seed_pick_on:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def seed_pick_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, kind, alts, itEqB, a, ch, ts, fitF, spF, inF, finF, fitCh):
  +fitC = alt_fits(grammar, index, outer, m, a, kind, alts, ch, itEqB, fitCh)
  +spC = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(ts), spF)
  +inC = pick_child_walk(root, index, outer, m, kc, k, a, ch, ts, inF)
  +ff = {Spec.Pick{a, ch} <> ts : +List<Spec.Tree>}
  ((k, (ch, (ch, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqB, ((fitC, (spC, inC)), ({==}, ({==}, {==})))))))))))), (fitC, (spC, (inC, {==}))))))), {==})

# The tree's first round of a loop starts on the tree.
law seed_loop_on:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +ready: {G.roundsReady(kind, k, k, Spec.Pick{a, ch} <> r) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def seed_loop_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, kind, alts, itEqB, a, ch, r, ts, fitF, spF, inF, finF, fitR, ready):
  +rounds = {Spec.Pick{a, ch} <> r : +List<Spec.Tree>}
  +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
  +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
  +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
  +fitC = alt_fits(grammar, index, outer, m, a, kind, alts, ch, itEqB, fitCh)
  +spR = G.spells_first(input, k, Spec.leaves(rounds), Spec.leaves(ts), spF)
  +spC = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(r), spR)
  +inR = loop_rounds_walk(root, index, outer, m, kc, k, rounds, ts, inF)
  +inC = round_child_walk(root, index, outer, m, k, k, a, ch, r, inR)
  +ff = {Spec.Loop{rounds} <> ts : +List<Spec.Tree>}
  ((k, (ch, (ch, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqB, ((fitC, (spC, inC)), (r, (fitR, (spR, (inR, (ready, {==}))))))))))))))), (fitC, (spC, (inC, {==}))))))), {==})
