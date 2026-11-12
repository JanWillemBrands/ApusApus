import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./SUPPORT.bend as Support
import ./LEMMAS.bend as Lemma
import ./PROOF_GLL.bend as G

# A SUPPORTED STATE IS WITHIN A CLOSED ONE. Every fact the rules give from facts of a closed
# plain state is in that state (that is what closed means), so every fact grown from the
# roots is in it, and so is every fact of a state whose facts were all grown that way.

# ---- Lists of facts in a state ----

law within_append:
  for xs: +List<Support.Fact>
  for +ys: +List<Support.Fact>
  for +p: Gll.GState
  for hx: {Support.factsWithin(xs, p) == True{} : Bool}
  for hy: {Support.factsWithin(ys, p) == True{} : Bool}
  {Support.factsWithin(List.append(&2, Support.Fact, xs, ys), p) == True{} : Bool}

def within_append(xs, ys, p, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      +both = hx
      Lemma.and_true_intro(Support.inState(x, p), Support.factsWithin(List.append(&2, Support.Fact, rest, ys), p),
        Lemma.and_true_left(Support.inState(x, p), Support.factsWithin(rest, p), both),
        within_append(rest, ys, p, Lemma.and_true_right_side(Support.inState(x, p), Support.factsWithin(rest, p), both), hy))

# Descriptors the plain check wants are seen.
law wanted_within:
  for ds: +List<Gll.Desc>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +all: {Check.allWanted(Gll.NoPred{}, grammar, input, ds, p) == True{} : Bool}
  {Support.factsWithin(Support.descriptorFacts(ds), p) == True{} : Bool}

def wanted_within(ds, grammar, input, p, all):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +both = all
      Lemma.and_true_intro(Check.descSeen(d, p), Support.factsWithin(Support.descriptorFacts(rest), p),
        Lemma.and_true_left(Check.descSeen(d, p), Check.allWanted(Gll.NoPred{}, grammar, input, rest, p), both),
        wanted_within(rest, grammar, input, p, Lemma.and_true_right_side(Check.descSeen(d, p), Check.allWanted(Gll.NoPred{}, grammar, input, rest, p), both)))

# A descriptor and its step, both in the state.
law pair_within:
  for +d: Gll.Desc
  for +y: Spec.Bsr
  for +p: Gll.GState
  for +both: {Bool.and(Check.descSeen(d, p), Check.stepIn(y, p)) == True{} : Bool}
  {Support.factsWithin([Support.FactDescriptor{d}, Support.FactStep{y}], p) == True{} : Bool}

def pair_within(d, y, p, both):
  Lemma.and_true_intro(Check.descSeen(d, p), Bool.and(Check.stepIn(y, p), True{}),
    Lemma.and_true_left(Check.descSeen(d, p), Check.stepIn(y, p), both),
    Lemma.and_true_intro(Check.stepIn(y, p), True{}, Lemma.and_true_right_side(Check.descSeen(d, p), Check.stepIn(y, p), both), {==}))

# ---- What a seen descriptor gives is in a closed plain state ----

law token_within:
  for ok: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p: Gll.GState
  for +r: {Check.tokenOk(ok, Gll.NoPred{}, grammar, input, index, rpath, dot, k, i, p) == True{} : Bool}
  {Support.factsWithin(Support.whenTrue(ok, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, 1n+i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)}]), p) == True{} : Bool}

def token_within(ok, grammar, input, index, rpath, dot, k, i, p, r):
  match ok:
    case True{}:
      pair_within(Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), p, r)
    case False{}:
      {==}

law skip_within:
  for skip: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p: Gll.GState
  for +r: {Check.skipOk(skip, Gll.NoPred{}, grammar, input, index, rpath, dot, k, i, p) == True{} : Bool}
  {Support.factsWithin(Support.whenTrue(skip, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}]), p) == True{} : Bool}

def skip_within(skip, grammar, input, index, rpath, dot, k, i, p, r):
  match skip:
    case True{}:
      pair_within(Gll.Desc{index, rpath, 1n+dot, k, i}, Gll.stepAt(index, rpath, 1n+dot, k, i, i), p, r)
    case False{}:
      {==}

law empty_within:
  for dot: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +p: Gll.GState
  for +r: {Check.emptyOk(dot, index, rpath, k, i, p) == True{} : Bool}
  {Support.factsWithin(Support.emptyStep(dot, index, rpath, k, i), p) == True{} : Bool}

def empty_within(dot, index, rpath, k, i, p, r):
  match dot:
    case 0n:
      Lemma.and_true_intro(Check.stepIn(Gll.stepAt(index, rpath, 0n, k, i, i), p), True{}, r, {==})
    case 1n+d:
      {==}

law item_within:
  for item: Maybe<&2, Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p: Gll.GState
  for +ok: {Check.itemOk(item, Gll.NoPred{}, grammar, input, index, rpath, dot, k, i, p) == True{} : Bool}
  {Support.factsWithin(Support.itemGives(item, grammar, input, index, rpath, dot, k, i), p) == True{} : Bool}

def item_within(item, grammar, input, index, rpath, dot, k, i, p, ok):
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      token_within(Gll.tokenIs(List.get(&2, Nat, input, i), t), grammar, input, index, rpath, dot, k, i, p, ok)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      +key = {Gll.CKey{Gll.TNt{x}, i} : Gll.CKey}
      +edge = {Gll.Edge{index, rpath, dot, k} : Gll.Edge}
      +both = ok
      Lemma.and_true_intro(Check.clusterIn(key, p), Bool.and(Check.returnIn(key, edge, p), True{}),
        Lemma.and_true_left(Check.clusterIn(key, p), Check.returnIn(key, edge, p), both),
        Lemma.and_true_intro(Check.returnIn(key, edge, p), True{}, Lemma.and_true_right_side(Check.clusterIn(key, p), Check.returnIn(key, edge, p), both), {==}))
    case Some{Spec.Brack{+kind, alts}}:
      +key = {Gll.CKey{Gll.TBr{index, dot <> rpath}, i} : Gll.CKey}
      +edge = {Gll.Edge{index, rpath, dot, k} : Gll.Edge}
      +skip = Check.skipOk(Gll.isSkippable(kind), Gll.NoPred{}, grammar, input, index, rpath, dot, k, i, p)
      +both = ok
      +rest = Lemma.and_true_right_side(Check.clusterIn(key, p), Bool.and(Check.returnIn(key, edge, p), skip), both)
      +skipFacts = Support.whenTrue(Gll.isSkippable(kind), [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])
      Lemma.and_true_intro(Check.clusterIn(key, p), Bool.and(Check.returnIn(key, edge, p), Support.factsWithin(skipFacts, p)),
        Lemma.and_true_left(Check.clusterIn(key, p), Bool.and(Check.returnIn(key, edge, p), skip), both),
        Lemma.and_true_intro(Check.returnIn(key, edge, p), Support.factsWithin(skipFacts, p),
          Lemma.and_true_left(Check.returnIn(key, edge, p), skip, rest),
          skip_within(Gll.isSkippable(kind), grammar, input, index, rpath, dot, k, i, p, Lemma.and_true_right_side(Check.returnIn(key, edge, p), skip, rest))))
    case Some{Spec.Eps{}}:
      skip_within(True{}, grammar, input, index, rpath, dot, k, i, p, ok)
    case None{}:
      +key = Check.endKey(grammar, index, rpath, k)
      +both = ok
      Lemma.and_true_intro(Check.popIn(key, i, p), Support.factsWithin(Support.emptyStep(dot, index, rpath, k, i), p),
        Lemma.and_true_right_side(Check.emptyOk(dot, index, rpath, k, i, p), Check.popIn(key, i, p), both),
        empty_within(dot, index, rpath, k, i, p, Lemma.and_true_left(Check.emptyOk(dot, index, rpath, k, i, p), Check.popIn(key, i, p), both)))

# ---- Facts reached are in the state ----

law step_equal_in:
  for +x: Spec.Bsr
  for +y: Spec.Bsr
  for +p: Gll.GState
  for c: Either<{x == y : Spec.Bsr}, {Spec.bsrMember(x, []) == True{} : Bool}>
  for +hb: {Check.stepIn(y, p) == True{} : Bool}
  {Check.stepIn(x, p) == True{} : Bool}

def step_equal_in(x, y, p, c, hb):
  match c:
    case Inl{same}:
      Equal.trans(Bool, Check.stepIn(x, p), Check.stepIn(y, p), True{}, Equal.cong(Spec.Bsr, Bool, v => Check.stepIn(v, p), x, y, same), hb)
    case Inr{never}:
      Empty.absurd({Check.stepIn(x, p) == True{} : Bool}, G.ebnf_not_in_empty(x, never))


# Equal facts: one in the state, so the other.
law equal_in:
  for a: Support.Fact
  for b: Support.Fact
  for +p: Gll.GState
  for +e: {Support.factEqual(a, b) == True{} : Bool}
  for +hb: {Support.inState(b, p) == True{} : Bool}
  {Support.inState(a, p) == True{} : Bool}

def equal_in(a, b, p, e, hb):
  match a b:
    case Support.FactDescriptor{+x} Support.FactDescriptor{+y}:
      Equal.trans(Bool, Check.descSeen(x, p), Check.descSeen(y, p), True{}, Equal.cong(Gll.Desc, Bool, v => Check.descSeen(v, p), x, y, G.desc_eq_sound(x, y, e)), hb)
    case Support.FactDescriptor{+x} Support.FactCluster{+y}:
      Empty.absurd({Support.inState(Support.FactDescriptor{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd({Support.inState(Support.FactDescriptor{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd({Support.inState(Support.FactDescriptor{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactStep{+y}:
      Empty.absurd({Support.inState(Support.FactDescriptor{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactDescriptor{+y}:
      Empty.absurd({Support.inState(Support.FactCluster{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactCluster{+y}:
      Equal.trans(Bool, Check.clusterIn(x, p), Check.clusterIn(y, p), True{}, Equal.cong(Gll.CKey, Bool, v => Check.clusterIn(v, p), x, y, G.key_eq_sound(x, y, e)), hb)
    case Support.FactCluster{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd({Support.inState(Support.FactCluster{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd({Support.inState(Support.FactCluster{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactStep{+y}:
      Empty.absurd({Support.inState(Support.FactCluster{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactDescriptor{+y}:
      Empty.absurd({Support.inState(Support.FactReturn{k1, e1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactCluster{+y}:
      Empty.absurd({Support.inState(Support.FactReturn{k1, e1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactReturn{+k2, +e2}:
      +ek = G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e))
      +ee = G.edge_eq_sound(e1, e2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e))
      +h1 = Equal.trans(Bool, Check.returnIn(k1, e2, p), Check.returnIn(k2, e2, p), True{}, Equal.cong(Gll.CKey, Bool, v => Check.returnIn(v, e2, p), k1, k2, ek), hb)
      Equal.trans(Bool, Check.returnIn(k1, e1, p), Check.returnIn(k1, e2, p), True{}, Equal.cong(Gll.Edge, Bool, v => Check.returnIn(k1, v, p), e1, e2, ee), h1)
    case Support.FactReturn{+k1, +e1} Support.FactPop{+k2, +j2}:
      Empty.absurd({Support.inState(Support.FactReturn{k1, e1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactStep{+y}:
      Empty.absurd({Support.inState(Support.FactReturn{k1, e1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactDescriptor{+y}:
      Empty.absurd({Support.inState(Support.FactPop{k1, j1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactCluster{+y}:
      Empty.absurd({Support.inState(Support.FactPop{k1, j1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactReturn{+k2, +e2}:
      Empty.absurd({Support.inState(Support.FactPop{k1, j1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactPop{+k2, +j2}:
      +ek = G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e))
      +ej = Lemma.nat_eq_sound(j1, j2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e))
      +h1 = Equal.trans(Bool, Check.popIn(k1, j2, p), Check.popIn(k2, j2, p), True{}, Equal.cong(Gll.CKey, Bool, v => Check.popIn(v, j2, p), k1, k2, ek), hb)
      Equal.trans(Bool, Check.popIn(k1, j1, p), Check.popIn(k1, j2, p), True{}, Equal.cong(Nat, Bool, v => Check.popIn(k1, v, p), j1, j2, ej), h1)
    case Support.FactPop{+k1, +j1} Support.FactStep{+y}:
      Empty.absurd({Support.inState(Support.FactPop{k1, j1}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactDescriptor{+y}:
      Empty.absurd({Support.inState(Support.FactStep{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactCluster{+y}:
      Empty.absurd({Support.inState(Support.FactStep{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd({Support.inState(Support.FactStep{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd({Support.inState(Support.FactStep{x}, p) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactStep{+y}:
      step_equal_in(x, y, p, G.ebnf_member_cases(x, y, [], e), hb)

law found_in_pick:
  for +fact: Support.Fact
  for +other: Support.Fact
  for -rest: +List<Support.Fact>
  for +p: Gll.GState
  for c: Either<{Support.factEqual(fact, other) == True{} : Bool}, {Support.factIn(fact, rest) == True{} : Bool}>
  for +here: {Support.inState(other, p) == True{} : Bool}
  for later: {Support.factIn(fact, rest) == True{} : Bool} -> {Support.inState(fact, p) == True{} : Bool}
  {Support.inState(fact, p) == True{} : Bool}

def found_in_pick(fact, other, rest, p, c, here, later):
  match c:
    case Inl{same}:
      equal_in(fact, other, p, same, here)
    case Inr{there}:
      later(there)

# A fact found among facts that are all in the state is in it.
law found_in:
  for facts: +List<Support.Fact>
  for +fact: Support.Fact
  for +p: Gll.GState
  for +all: {Support.factsWithin(facts, p) == True{} : Bool}
  for +m: {Support.factIn(fact, facts) == True{} : Bool}
  {Support.inState(fact, p) == True{} : Bool}

def found_in(facts, fact, p, all, m):
  match facts:
    case Nil{}:
      Empty.absurd({Support.inState(fact, p) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+other, +rest}:
      found_in_pick(fact, other, rest, p, Lemma.or_true_cases(Support.factEqual(fact, other), Support.factIn(fact, rest), m),
        Lemma.and_true_left(Support.inState(other, p), Support.factsWithin(rest, p), all),
        there => found_in(rest, fact, p, Lemma.and_true_right_side(Support.inState(other, p), Support.factsWithin(rest, p), all), there))

# ---- What a fact gives is in a closed plain state ----

# A return edge resumes at a pop of its cluster: the resumed descriptor and step.
law resume_within:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +key: Gll.CKey
  for edge: Gll.Edge
  for +end: Nat
  for +inR: {Check.returnIn(key, edge, p) == True{} : Bool}
  for +inP: {Check.popIn(key, end, p) == True{} : Bool}
  {Support.factsWithin(Support.resumeGives(key, edge, end), p) == True{} : Bool}

def resume_within(grammar, input, p, closedOk, key, edge, end, inR, inP):
  match edge:
    case Gll.Edge{+index, +rpath, +dot, +k}:
      pair_within(Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, Check.keyStart(key), end), p,
        G.resume_ok(Gll.NoPred{}, grammar, input, p, closedOk, key, Gll.Edge{index, rpath, dot, k}, end, inR, inP))

law edge_when:
  for same: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +key: Gll.CKey
  for +popKey: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(key, popKey) == same : Bool}
  for +inR: {Check.returnIn(key, edge, p) == True{} : Bool}
  for +inP: {Check.popIn(popKey, end, p) == True{} : Bool}
  {Support.factsWithin(Support.whenTrue(same, Support.resumeGives(key, edge, end)), p) == True{} : Bool}

def edge_when(same, grammar, input, p, closedOk, key, popKey, edge, end, sameEq, inR, inP):
  match same:
    case True{}:
      +ek = G.key_eq_sound(key, popKey, sameEq)
      +inP2 = Equal.trans(Bool, Check.popIn(key, end, p), Check.popIn(popKey, end, p), True{}, Equal.cong(Gll.CKey, Bool, v => Check.popIn(v, end, p), key, popKey, ek), inP)
      resume_within(grammar, input, p, closedOk, key, edge, end, inR, inP2)
    case False{}:
      {==}

# A return edge against the pops reached.
law edge_within:
  for reached: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +inR: {Check.returnIn(key, edge, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.edgeGives(reached, key, edge), p) == True{} : Bool}

def edge_within(reached, grammar, input, p, closedOk, key, edge, inR, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactPop{+popKey, +end}, +rest}:
      +restOk = Lemma.and_true_right_side(Check.popIn(popKey, end, p), Support.factsWithin(rest, p), all)
      within_append(Support.whenTrue(Gll.keyEq(key, popKey), Support.resumeGives(key, edge, end)), Support.edgeGives(rest, key, edge), p,
        edge_when(Gll.keyEq(key, popKey), grammar, input, p, closedOk, key, popKey, edge, end, {==}, inR, Lemma.and_true_left(Check.popIn(popKey, end, p), Support.factsWithin(rest, p), all)),
        edge_within(rest, grammar, input, p, closedOk, key, edge, inR, restOk))
    case Con{Support.FactDescriptor{+x}, +rest}:
      edge_within(rest, grammar, input, p, closedOk, key, edge, inR, Lemma.and_true_right_side(Check.descSeen(x, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactCluster{+x}, +rest}:
      edge_within(rest, grammar, input, p, closedOk, key, edge, inR, Lemma.and_true_right_side(Check.clusterIn(x, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactReturn{+k2, +e2}, +rest}:
      edge_within(rest, grammar, input, p, closedOk, key, edge, inR, Lemma.and_true_right_side(Check.returnIn(k2, e2, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactStep{+y}, +rest}:
      edge_within(rest, grammar, input, p, closedOk, key, edge, inR, Lemma.and_true_right_side(Check.stepIn(y, p), Support.factsWithin(rest, p), all))

law pop_when:
  for same: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +edgeKey: Gll.CKey
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(edgeKey, key) == same : Bool}
  for +inR: {Check.returnIn(edgeKey, edge, p) == True{} : Bool}
  for +inP: {Check.popIn(key, end, p) == True{} : Bool}
  {Support.factsWithin(Support.whenTrue(same, Support.resumeGives(edgeKey, edge, end)), p) == True{} : Bool}

def pop_when(same, grammar, input, p, closedOk, edgeKey, key, edge, end, sameEq, inR, inP):
  match same:
    case True{}:
      +ek = G.key_eq_sound(edgeKey, key, sameEq)
      +inP2 = Equal.trans(Bool, Check.popIn(edgeKey, end, p), Check.popIn(key, end, p), True{}, Equal.cong(Gll.CKey, Bool, v => Check.popIn(v, end, p), edgeKey, key, ek), inP)
      resume_within(grammar, input, p, closedOk, edgeKey, edge, end, inR, inP2)
    case False{}:
      {==}

# A pop against the return edges reached.
law pop_within:
  for reached: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +key: Gll.CKey
  for +end: Nat
  for +inP: {Check.popIn(key, end, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.popGives(reached, key, end), p) == True{} : Bool}

def pop_within(reached, grammar, input, p, closedOk, key, end, inP, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactReturn{+edgeKey, +edge}, +rest}:
      +restOk = Lemma.and_true_right_side(Check.returnIn(edgeKey, edge, p), Support.factsWithin(rest, p), all)
      within_append(Support.whenTrue(Gll.keyEq(edgeKey, key), Support.resumeGives(edgeKey, edge, end)), Support.popGives(rest, key, end), p,
        pop_when(Gll.keyEq(edgeKey, key), grammar, input, p, closedOk, edgeKey, key, edge, end, {==}, Lemma.and_true_left(Check.returnIn(edgeKey, edge, p), Support.factsWithin(rest, p), all), inP),
        pop_within(rest, grammar, input, p, closedOk, key, end, inP, restOk))
    case Con{Support.FactDescriptor{+x}, +rest}:
      pop_within(rest, grammar, input, p, closedOk, key, end, inP, Lemma.and_true_right_side(Check.descSeen(x, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactCluster{+x}, +rest}:
      pop_within(rest, grammar, input, p, closedOk, key, end, inP, Lemma.and_true_right_side(Check.clusterIn(x, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactPop{+k2, +j2}, +rest}:
      pop_within(rest, grammar, input, p, closedOk, key, end, inP, Lemma.and_true_right_side(Check.popIn(k2, j2, p), Support.factsWithin(rest, p), all))
    case Con{Support.FactStep{+y}, +rest}:
      pop_within(rest, grammar, input, p, closedOk, key, end, inP, Lemma.and_true_right_side(Check.stepIn(y, p), Support.factsWithin(rest, p), all))

# What a fact of the state gives, with facts reached that are all in it, is in it.
law fact_within:
  for fact: Support.Fact
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +reached: +List<Support.Fact>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +here: {Support.inState(fact, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.factGives(fact, grammar, input, reached), p) == True{} : Bool}

def fact_within(fact, grammar, input, reached, p, closedOk, here, all):
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, +rpath, +dot, +k, +i}}:
      item_within(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), grammar, input, index, rpath, dot, k, i, p,
        G.seen_ok(Gll.NoPred{}, grammar, input, p, closedOk, Gll.Desc{index, rpath, dot, k, i}, here))
    case Support.FactCluster{+key}:
      wanted_within(Check.seedsOf(grammar, key), grammar, input, p, G.cluster_ok(Gll.NoPred{}, grammar, input, p, closedOk, key, here))
    case Support.FactReturn{+key, +edge}:
      edge_within(reached, grammar, input, p, closedOk, key, edge, here, all)
    case Support.FactPop{+key, +end}:
      within_append(Support.popGives(reached, key, end), Support.descriptorFacts(Check.againOfKey(grammar, key, end)), p,
        pop_within(reached, grammar, input, p, closedOk, key, end, here, all),
        wanted_within(Check.againOfKey(grammar, key, end), grammar, input, p, G.again_ok(Gll.NoPred{}, grammar, input, p, closedOk, key, end, here)))
    case Support.FactStep{y}:
      {==}

# ---- Growing the facts reached keeps them in the state ----

law all_give_within:
  for facts: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +reached: +List<Support.Fact>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +here: {Support.factsWithin(facts, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.allGive(facts, grammar, input, reached), p) == True{} : Bool}

def all_give_within(facts, grammar, input, reached, p, closedOk, here, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      within_append(Support.factGives(fact, grammar, input, reached), Support.allGive(rest, grammar, input, reached), p,
        fact_within(fact, grammar, input, reached, p, closedOk, Lemma.and_true_left(Support.inState(fact, p), Support.factsWithin(rest, p), here), all),
        all_give_within(rest, grammar, input, reached, p, closedOk, Lemma.and_true_right_side(Support.inState(fact, p), Support.factsWithin(rest, p), here), all))

law keep_within:
  for keep: Bool
  for +fact: Support.Fact
  for +facts: +List<Support.Fact>
  for +p: Gll.GState
  for +here: {Support.inState(fact, p) == True{} : Bool}
  for +all: {Support.factsWithin(facts, p) == True{} : Bool}
  {Support.factsWithin(Support.keepPick(keep, fact, facts), p) == True{} : Bool}

def keep_within(keep, fact, facts, p, here, all):
  match keep:
    case True{}:
      Lemma.and_true_intro(Support.inState(fact, p), Support.factsWithin(facts, p), here, all)
    case False{}:
      all

law add_within:
  for new: +List<Support.Fact>
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
  for +p: Gll.GState
  for +here: {Support.factsWithin(new, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.addWithin(new, s, reached), p) == True{} : Bool}

def add_within(new, s, reached, p, here, all):
  match new:
    case Nil{}:
      all
    case Con{+fact, +rest}:
      +keep = Bool.and(Support.inState(fact, s), Bool.not(Support.factIn(fact, reached)))
      add_within(rest, s, Support.keepPick(keep, fact, reached), p, Lemma.and_true_right_side(Support.inState(fact, p), Support.factsWithin(rest, p), here),
        keep_within(keep, fact, reached, p, Lemma.and_true_left(Support.inState(fact, p), Support.factsWithin(rest, p), here), all))

law grow_within:
  for n: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(Support.grow(n, grammar, input, s, reached), p) == True{} : Bool}

def grow_within(n, grammar, input, s, reached, p, closedOk, all):
  match n:
    case 0n:
      all
    case 1n+(+m):
      +next = Support.round(grammar, input, s, reached)
      grow_within(m, grammar, input, s, next, p, closedOk,
        add_within(Support.allGive(reached, grammar, input, reached), s, reached, p, all_give_within(reached, grammar, input, reached, p, closedOk, all, all), all))

# The roots are in a closed state that has the start symbol's cluster.
law roots_within:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +p: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +rootIn: {Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, p) == True{} : Bool}
  {Support.factsWithin(Support.roots(grammar, start), p) == True{} : Bool}

def roots_within(grammar, start, input, p, closedOk, rootIn):
  +key = {Gll.CKey{Gll.TNt{start}, 0n} : Gll.CKey}
  Lemma.and_true_intro(Check.clusterIn(key, p), Support.factsWithin(Support.descriptorFacts(Gll.productionsOf(grammar, start, 0n, 0n)), p), rootIn,
    wanted_within(Gll.productionsOf(grammar, start, 0n, 0n), grammar, input, p, G.cluster_ok(Gll.NoPred{}, grammar, input, p, closedOk, key, rootIn)))

law reached_within:
  for facts: +List<Support.Fact>
  for +reached: +List<Support.Fact>
  for +p: Gll.GState
  for +found: {Support.allReached(facts, reached) == True{} : Bool}
  for +all: {Support.factsWithin(reached, p) == True{} : Bool}
  {Support.factsWithin(facts, p) == True{} : Bool}

def reached_within(facts, reached, p, found, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      Lemma.and_true_intro(Support.inState(fact, p), Support.factsWithin(rest, p),
        found_in(reached, fact, p, all, Lemma.and_true_left(Support.factIn(fact, reached), Support.allReached(rest, reached), found)),
        reached_within(rest, reached, p, Lemma.and_true_right_side(Support.factIn(fact, reached), Support.allReached(rest, reached), found), all))

# A SUPPORTED STATE IS WITHIN A CLOSED ONE.
law supported_within:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +p: Gll.GState
  for +s: Gll.GState
  for +closedOk: {Check.closed(grammar, input, p) == True{} : Bool}
  for +rootIn: {Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, p) == True{} : Bool}
  for +sup: {Support.supported(grammar, start, input, s) == True{} : Bool}
  {Support.factsWithin(Support.factsOf(s), p) == True{} : Bool}

def supported_within(grammar, start, input, p, s, closedOk, rootIn, sup):
  +facts = Support.factsOf(s)
  +first = Support.addWithin(Support.roots(grammar, start), s, [])
  +reached = Support.grow(List.length(&2, Support.Fact, facts), grammar, input, s, first)
  reached_within(facts, reached, p, sup,
    grow_within(List.length(&2, Support.Fact, facts), grammar, input, s, first, p, closedOk,
      add_within(Support.roots(grammar, start), s, [], p, roots_within(grammar, start, input, p, closedOk, rootIn), {==})))

# ---- The states handed out ----

def stateOr(m: Maybe<&2, Gll.GState>, +d: Gll.GState) -> Gll.GState:
  match m:
    case Some{s}:
      s
    case None{}:
      d

def isNoState(m: Maybe<&2, Gll.GState>) -> Bool:
  match m:
    case Some{s}:
      False{}
    case None{}:
      True{}

law state_pick:
  for ok: Bool
  for +s: Gll.GState
  for +t: Gll.GState
  for got: {Support.statePick(ok, s) == Some{t} : Maybe<&2, Gll.GState>}
  Sigma<&2, &2, {ok == True{} : Bool}, _ => {s == t : Gll.GState}>

def state_pick(ok, s, t, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, Gll.GState>, Gll.GState, v => stateOr(v, s), Some{s}, Some{t}, got))
    case False{}:
      Empty.absurd(Sigma<&2, &2, {False{} == True{} : Bool}, _ => {s == t : Gll.GState}>, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Gll.GState>, Bool, v => isNoState(v), None{}, Some{t}, got)))

law closed_pair:
  for ok0: Bool
  for +s: Gll.GState
  for +t: Gll.GState
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +okEq: {Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)) == ok0 : Bool}
  for pair: Sigma<&2, &2, {ok0 == True{} : Bool}, _ => {s == t : Gll.GState}>
  {Bool.and(Check.closed(grammar, input, t), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, t)) == True{} : Bool}

def closed_pair(ok0, s, t, grammar, start, input, okEq, pair):
  match pair:
    case (+isOk, +same):
      +h = Equal.trans(Bool, Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), ok0, True{}, okEq, isOk)
      Equal.trans(Bool, Bool.and(Check.closed(grammar, input, t), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, t)), Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), True{},
        Equal.cong(Gll.GState, Bool, v => Bool.and(Check.closed(grammar, input, v), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, v)), t, s, Equal.sym(Gll.GState, s, t, same)), h)

law supported_pair:
  for ok0: Bool
  for +s: Gll.GState
  for +t: Gll.GState
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +okEq: {Support.supported(grammar, start, input, s) == ok0 : Bool}
  for pair: Sigma<&2, &2, {ok0 == True{} : Bool}, _ => {s == t : Gll.GState}>
  {Support.supported(grammar, start, input, t) == True{} : Bool}

def supported_pair(ok0, s, t, grammar, start, input, okEq, pair):
  match pair:
    case (+isOk, +same):
      +h = Equal.trans(Bool, Support.supported(grammar, start, input, s), ok0, True{}, okEq, isOk)
      Equal.trans(Bool, Support.supported(grammar, start, input, t), Support.supported(grammar, start, input, s), True{},
        Equal.cong(Gll.GState, Bool, v => Support.supported(grammar, start, input, v), t, s, Equal.sym(Gll.GState, s, t, same)), h)

# A closed plain state handed out: closed, with the root cluster.
law closed_of:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for got: {Support.closedPick(r, grammar, start, input) == Some{t} : Maybe<&2, Gll.GState>}
  {Bool.and(Check.closed(grammar, input, t), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, t)) == True{} : Bool}

def closed_of(r, grammar, start, input, t, got):
  match r:
    case Gll.GDone{+s}:
      +ok0 = Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s))
      closed_pair(ok0, s, t, grammar, start, input, {==}, state_pick(ok0, s, t, got))
    case Gll.OutOfFuel{s}:
      Empty.absurd({Bool.and(Check.closed(grammar, input, t), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, t)) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Gll.GState>, Bool, v => isNoState(v), None{}, Some{t}, got)))

law supported_of:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Gll.GState
  for got: {Support.supportedPick(r, grammar, start, input) == Some{t} : Maybe<&2, Gll.GState>}
  {Support.supported(grammar, start, input, t) == True{} : Bool}

def supported_of(r, grammar, start, input, t, got):
  match r:
    case Gll.GDone{+s}:
      +ok0 = Support.supported(grammar, start, input, s)
      supported_pair(ok0, s, t, grammar, start, input, {==}, state_pick(ok0, s, t, got))
    case Gll.OutOfFuel{s}:
      Empty.absurd({Support.supported(grammar, start, input, t) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Gll.GState>, Bool, v => isNoState(v), None{}, Some{t}, got)))

# The law predict_saves_work.
def Laws.predict_saves_work(fuelPlain, fuelOther, pr, grammar, start, input, plain, other, gotPlain, gotOther):
  +both = closed_of(Gll.parse(fuelPlain, grammar, start, input), grammar, start, input, plain, gotPlain)
  supported_within(grammar, start, input, plain, other,
    Lemma.and_true_left(Check.closed(grammar, input, plain), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, plain), both),
    Lemma.and_true_right_side(Check.closed(grammar, input, plain), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, plain), both),
    supported_of(Gll.parseWith(fuelOther, pr, grammar, start, input), grammar, start, input, other, gotOther))
