import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./FIRST.bend as First
import ./LL1.bend as LL1
import ./SUPPORT.bend as Support
import ./PSUPPORT.bend as PS
import ./LEMMAS.bend as Lemma
import ./FITS.bend as Fits
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_LL1.bend as L
import ./PROOF_UNAMBIGUOUS.bend as U
import ./PROOF_NODEAD.bend as N1

# NO DEAD WOOD FOR AN LL(1) GRAMMAR, WITH BRACKETS. As PROOF_NODEAD.bend, with sequences
# inside brackets: a descriptor of a round of a bracket is on the tree when the round is,
# and a round is on the tree when the bracket's caller is. Only the tree's choices get past
# prediction at a bracket (entering it, skipping it, another round, leaving it), and two
# callers of one bracket at one position have the same forest from there on.

# ======== SEQUENCES ON THE TREE ========

def prefixOf(rpath: +List<Nat>) -> +List<Nat>:
  Gll.reverseOnto(rpath, [])

# The forest g of the sequence at (index, rpath), started at p0 (its descriptors counting
# from k), is in the tree.
def GAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +rpath: +List<Nat>, +k: Nat, +p0: Nat, +g: +List<Spec.Tree>) -> Data:
  N1.And({Spec.fits(g, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}, N1.And(G.Spells(g, input, p0), {Spec.allIn(Spec.walk(g, False{}, index, prefixOf(rpath), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}))

# The rest f of the sequence after dot items, at i, ending where g ends.
def RestAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, +p0: Nat, +g: +List<Spec.Tree>, +f: +List<Spec.Tree>) -> Data:
  N1.And({Spec.fits(f, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}, N1.And(G.Spells(f, input, i),
    N1.And({Spec.allIn(Spec.walk(f, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}, {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat})))

# How a round g of alternative a sits in the bracket's tree X (the head of the caller's
# rest F): the tree of ( ) or [ ], or one of the rounds of a loop, with the rounds from it
# on (they read as they must, and end where the loop ends).
def RoundIn(f: +List<Spec.Tree>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +outer: +List<Nat>, +m: Nat, +a: Nat, +k: Nat, +p0: Nat, +g: +List<Spec.Tree>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Data:
  match f:
    case Con{Spec.Pick{+a2, +ch}, ts}:
      N1.And({a2 == a : Nat}, N1.And({ch == g : +List<Spec.Tree>}, {p0 == k : Nat}))
    case Con{Spec.Loop{+rs}, ts}:
      Sigma<&2, &2, +List<Spec.Tree>, r2 =>
        N1.And({Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool},
        N1.And(G.Spells(Spec.Pick{a, g} <> r2, input, p0),
        N1.And({Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool},
        N1.And({G.roundsReady(kind, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool},
          {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}))))>
    case Nil{}:
      N1.No()
    case Con{Spec.Leaf{x}, ts}:
      N1.No()
    case Con{Spec.Node{q, ch}, ts}:
      N1.No()
    case Con{Spec.Skip{}, ts}:
      N1.No()

# The sequence at (index, rpath) has the forest g in the tree, started at p0; its
# descriptors count from k (a production's start, or a bracket's).
def SeqOcc(rpath: +List<Nat>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +k: Nat, +p0: Nat, +g: +List<Spec.Tree>) -> Data:
  match rpath:
    case Nil{}:
      N1.And({p0 == k : Nat}, Sigma<&2, &2, Nat, x => N1.And({Spec.lhsIs(grammar, index, x) == True{} : Bool}, N1.NodeAt(grammar, input, root, index, k, g))>)
    case Con{a, Nil{}}:
      N1.No()
    case Con{+a, Con{+m, +outer}}:
      Sigma<&2, &2, Nat, kc => Sigma<&2, &2, Nat, p1 => Sigma<&2, &2, +List<Spec.Tree>, g1 => Sigma<&2, &2, +List<Spec.Tree>, ff => Sigma<&2, &2, Spec.Bracket, kind => Sigma<&2, &2, +List<+List<Spec.Item>>, alts =>
        N1.And(SeqOcc(outer, grammar, input, root, index, kc, p1, g1),
        N1.And(RestAt(grammar, input, root, index, outer, m, kc, k, p1, g1, ff),
        N1.And({Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>},
        N1.And(GAt(grammar, input, root, index, a <> (m <> outer), k, p0, g),
          RoundIn(ff, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)))))>>>>>>

# ======== FACTS ON THE TREE ========

def descOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, d: Gll.Desc) -> Data:
  match d:
    case Gll.Desc{+index, +rpath, +dot, +k, +i}:
      Sigma<&2, &2, Nat, p0 => Sigma<&2, &2, +List<Spec.Tree>, g => Sigma<&2, &2, +List<Spec.Tree>, f =>
        N1.And(SeqOcc(rpath, grammar, input, root, index, k, p0, g), RestAt(grammar, input, root, index, rpath, dot, k, i, p0, g, f))>>>

def clusterOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey) -> Data:
  match key:
    case Gll.CKey{Gll.TNt{+x}, +i}:
      N1.NtAt(grammar, input, root, x, i)
    case Gll.CKey{Gll.TBr{+index, Con{+m, +outer}}, +k}:
      Sigma<&2, &2, Nat, kc => Sigma<&2, &2, Spec.Bracket, kind => Sigma<&2, &2, +List<+List<Spec.Item>>, alts =>
        N1.And(descOn(grammar, input, root, Gll.Desc{index, outer, m, kc, k}), {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>})>>>
    case Gll.CKey{Gll.TBr{index, Nil{}}, k}:
      N1.No()

def returnOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey, edge: Gll.Edge) -> Data:
  match key edge:
    case Gll.CKey{Gll.TNt{+x}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      N1.And(descOn(grammar, input, root, Gll.Desc{index, rpath, dot, k, i}), {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>})
    case Gll.CKey{Gll.TBr{+index2, +rp}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      Sigma<&2, &2, Spec.Bracket, kind => Sigma<&2, &2, +List<+List<Spec.Item>>, alts =>
        N1.And(descOn(grammar, input, root, Gll.Desc{index, rpath, dot, k, i}), N1.And({index2 == index : Nat}, N1.And({rp == dot <> rpath : +List<Nat>},
          {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>})))>>

def popOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey, +j: Nat) -> Data:
  match key:
    case Gll.CKey{Gll.TNt{+x}, +k}:
      N1.NtEnds(grammar, input, root, x, k, j)
    case Gll.CKey{Gll.TBr{+index, Con{+m, +outer}}, +k}:
      Sigma<&2, &2, Nat, a => Sigma<&2, &2, Nat, p0 => Sigma<&2, &2, +List<Spec.Tree>, g =>
        N1.And(SeqOcc(a <> (m <> outer), grammar, input, root, index, k, p0, g), {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == j : Nat})>>>
    case Gll.CKey{Gll.TBr{index, Nil{}}, k}:
      N1.No()

def On(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, fact: Support.Fact) -> Data:
  match fact:
    case Support.FactDescriptor{+d}:
      descOn(grammar, input, root, d)
    case Support.FactCluster{+key}:
      clusterOn(grammar, input, root, key)
    case Support.FactReturn{+key, +edge}:
      returnOn(grammar, input, root, key, edge)
    case Support.FactPop{+key, +end}:
      popOn(grammar, input, root, key, end)
    case Support.FactStep{+y}:
      {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}

def AllOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, facts: +List<Support.Fact>) -> Data:
  match facts:
    case Nil{}:
      {0n == 0n : Nat}
    case Con{+fact, rest}:
      N1.And(On(grammar, input, root, fact), AllOn(grammar, input, root, rest))

law N1_and_left:
  for -A: Data
  for -B: Data
  for +p: N1.And(A, B)
  A

def N1_and_left(A, B, p):
  match p:
    case (a, b):
      a

law N1_and_right:
  for -A: Data
  for -B: Data
  for +p: N1.And(A, B)
  B

def N1_and_right(A, B, p):
  match p:
    case (a, b):
      b

# ======== THE PREFIX OF A SEQUENCE ON THE TREE ========

law seq_of:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +index: Nat
  for +k: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  N1.And({L.evenLength(prefixOf(rpath)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>})

def seq_of(rpath, grammar, input, root, index, k, p0, g, occ):
  match rpath:
    case Nil{}:
      ({==}, {==})
    case Con{a, Nil{}}:
      Empty.absurd(N1.And({L.evenLength(prefixOf([a])) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf([a])) == Gll.seqAt(grammar, index, [a]) : +List<Spec.Item>}), Lemma.false_is_not_true(occ))
    case Con{+a, Con{+m, +outer}}:
      match occ:
        case (kc, (p1, (g1, (ff, (kind, (alts, (occO, rest))))))):
          +inner = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
          +pO = prefixOf(outer)
          +ext = G.rev_onto(outer, [m, a])
          +evenO = N1_and_left({L.evenLength(pO) == True{} : Bool}, {Spec.sequenceAt(grammar, index, pO) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, inner)
          +seqO = N1_and_right({L.evenLength(pO) == True{} : Bool}, {Spec.sequenceAt(grammar, index, pO) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, inner)
          +longer = List.append(&2, Nat, pO, [m, a])
          (Equal.trans(Bool, L.evenLength(Gll.reverseOnto(outer, [m, a])), L.evenLength(longer), True{}, Equal.cong(+List<Nat>, Bool, v => L.evenLength(v), Gll.reverseOnto(outer, [m, a]), longer, ext),
             Equal.trans(Bool, L.evenLength(longer), L.evenLength(pO), True{}, L.even_snoc(pO, m, a), evenO)),
           Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, Gll.reverseOnto(outer, [m, a])), Spec.sequenceAt(grammar, index, longer), Gll.seqAt(grammar, index, a <> (m <> outer)),
             Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), Gll.reverseOnto(outer, [m, a]), longer, ext),
             L.deeper_eq(grammar, index, pO, outer, m, a, evenO, seqO)))

# ======== LISTS OF FACTS ON THE TREE ========

law on_append:
  for xs: +List<Support.Fact>
  for +ys: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +hx: AllOn(grammar, input, root, xs)
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, xs)
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +here: On(grammar, input, root, fact)
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +here: AllOn(grammar, input, root, new)
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for c: Either<{x == y : Spec.Bsr}, {Spec.bsrMember(x, []) == True{} : Bool}>
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +e: {Support.factEqual(a, b) == True{} : Bool}
  for +hb: On(grammar, input, root, b)
  On(grammar, input, root, a)

def equal_on(a, b, grammar, input, root, e, hb):
  match a b:
    case Support.FactDescriptor{+x} Support.FactDescriptor{+y}:
      +yx = Equal.sym(Gll.Desc, x, y, G.desc_eq_sound(x, y, e))
      %yx : descOn(grammar, input, root, _)
      hb
    case Support.FactDescriptor{+x} Support.FactCluster{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactDescriptor{x}), Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd(On(grammar, input, root, Support.FactDescriptor{x}), Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd(On(grammar, input, root, Support.FactDescriptor{x}), Lemma.false_is_not_true(e))
    case Support.FactDescriptor{+x} Support.FactStep{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactDescriptor{x}), Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactDescriptor{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactCluster{x}), Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactCluster{+y}:
      +yx = Equal.sym(Gll.CKey, x, y, G.key_eq_sound(x, y, e))
      %yx : clusterOn(grammar, input, root, _)
      hb
    case Support.FactCluster{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd(On(grammar, input, root, Support.FactCluster{x}), Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd(On(grammar, input, root, Support.FactCluster{x}), Lemma.false_is_not_true(e))
    case Support.FactCluster{+x} Support.FactStep{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactCluster{x}), Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactDescriptor{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactReturn{k1, e1}), Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactCluster{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactReturn{k1, e1}), Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactReturn{+k2, +e2}:
      +k21 = Equal.sym(Gll.CKey, k1, k2, G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e)))
      +e21 = Equal.sym(Gll.Edge, e1, e2, G.edge_eq_sound(e1, e2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Gll.edgeEq(e1, e2), e)))
      %k21 : returnOn(grammar, input, root, _, e1)
      %e21 : returnOn(grammar, input, root, k2, _)
      hb
    case Support.FactReturn{+k1, +e1} Support.FactPop{+k2, +j2}:
      Empty.absurd(On(grammar, input, root, Support.FactReturn{k1, e1}), Lemma.false_is_not_true(e))
    case Support.FactReturn{+k1, +e1} Support.FactStep{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactReturn{k1, e1}), Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactDescriptor{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactPop{k1, j1}), Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactCluster{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactPop{k1, j1}), Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactReturn{+k2, +e2}:
      Empty.absurd(On(grammar, input, root, Support.FactPop{k1, j1}), Lemma.false_is_not_true(e))
    case Support.FactPop{+k1, +j1} Support.FactPop{+k2, +j2}:
      +k21 = Equal.sym(Gll.CKey, k1, k2, G.key_eq_sound(k1, k2, Lemma.and_true_left(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e)))
      +j21 = Equal.sym(Nat, j1, j2, Lemma.nat_eq_sound(j1, j2, Lemma.and_true_right_side(Gll.keyEq(k1, k2), Nat.is_eq(j1, j2), e)))
      %k21 : popOn(grammar, input, root, _, j1)
      %j21 : popOn(grammar, input, root, k2, _)
      hb
    case Support.FactPop{+k1, +j1} Support.FactStep{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactPop{k1, j1}), Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactDescriptor{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactStep{x}), Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactCluster{+y}:
      Empty.absurd(On(grammar, input, root, Support.FactStep{x}), Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactReturn{+k2, +e2}:
      Empty.absurd(On(grammar, input, root, Support.FactStep{x}), Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactPop{+k2, +j2}:
      Empty.absurd(On(grammar, input, root, Support.FactStep{x}), Lemma.false_is_not_true(e))
    case Support.FactStep{+x} Support.FactStep{+y}:
      step_equal_on(x, y, grammar, input, root, G.ebnf_member_cases(x, y, [], e), hb)

law found_on_pick:
  for +fact: Support.Fact
  for +other: Support.Fact
  for -rest: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for c: Either<{Support.factEqual(fact, other) == True{} : Bool}, {Support.factIn(fact, rest) == True{} : Bool}>
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
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +all: AllOn(grammar, input, root, facts)
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

# ======== TWO CHOICES AT A BRACKET THAT ADMIT THE TOKEN: A CONFLICT ========

# The checks at the bracket at item dot of the sequence at (index, R) are among the
# grammar's checks.
law local_conflict:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R: +List<Nat>
  for +dot: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(R)) == Gll.seqAt(grammar, index, R) : +List<Spec.Item>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +ne: {List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, R, dot)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def local_conflict(grammar, t, index, R, dot, kind, alts, seqEq, itEq, ne):
  +p = prefixOf(R)
  +S = Spec.sequenceAt(grammar, index, p)
  +itS = Equal.trans(Maybe<&2, Spec.Item>, Spec.itemAt(S, dot), Gll.nthItem(S, dot), Some{Spec.Brack{kind, alts}}, L.item_at_eq(S, dot),
    Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(S, dot), Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Some{Spec.Brack{kind, alts}}, Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), S, Gll.seqAt(grammar, index, R), seqEq), itEq))
  +back = L.reverse_twice(R, [])
  +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, L.localConflicts(Spec.itemAt(S, dot), grammar, t, index, Gll.reverseOnto(p, []), dot)), List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)), False{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, L.localConflicts(v, grammar, t, index, Gll.reverseOnto(p, []), dot)), Spec.itemAt(S, dot), Some{Spec.Brack{kind, alts}}, itS),
    Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)), List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, R, dot)), False{},
      Equal.cong(+List<Nat>, Bool, v => List.is_empty(&2, LL1.Conflict, L.localConflicts(Some{Spec.Brack{kind, alts}}, grammar, t, index, v, dot)), Gll.reverseOnto(p, []), R, back), ne))
  L.nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
    L.prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), L.locate(p, Gll.nestFuel(), grammar, t, index, [], dot, ne2)))

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

# Skipping optional at the dot: on the tree when the tree skips it, else not admitted.
law skip_optional:
  for f: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}]))

def skip_optional(f, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, bEq):
  match f b:
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+a}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
      +hP = Bool.and(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      +isA = Lemma.and_true_right_side(okR, Spec.isAlt(alts, a), h2)
      +fitCh = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      +reads = G.optional_reads(a, ch, Lemma.and_true_left(okR, Spec.isAlt(alts, a), h2))
      +spCh = G.spells_first(input, i, Spec.leaves(ch), Spec.leaves(ts), spF)
      +seqEq = N1_and_right({L.evenLength(prefixOf(rpath)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}, seq_of(rpath, grammar, input, root, index, k, p0, g, occ))
      +next = List.get(&2, Nat, input, i)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsA = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a), i, ch, fitCh, spCh, reads)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Optional{}, grammar, t, index, rpath, dot, alts, a, n, next, U.lt_ne(a, n, isA), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))), noConf)))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +inT = N1.all_in_tail_n(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, i), Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.allIn(Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, i), Spec.steps(root, 0n)), inF)
      ((p0, (g, (ts, (occ, (fitF2, (spF, (inT, finF))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), step_at_eq(index, rpath, 1n+dot, k, i, i)), onAt), {==}))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Pick{+a, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+a}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}

# Skipping closure at the dot: on the tree when the tree skips it, else not admitted.
law skip_closure:
  for f: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}]))

def skip_closure(f, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, bEq):
  match f b:
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+a}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +i0 = Lemma.add_zero_right(i)
      +wT0 = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, Nat.add(i, 0n))
      +inA = N1.all_in_tail_n(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, Nat.add(i, 0n)), List.append(&2, Spec.Bsr, [], wT0), Spec.steps(root, 0n), inF)
      +inT = Equal.trans(Bool, Spec.allIn(Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, i), Spec.steps(root, 0n)), Spec.allIn(wT0, Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, v), Spec.steps(root, 0n)), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, i0)), inA)
      +onAt0 = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, Nat.add(i, 0n)), Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, [], wT0), Spec.steps(root, 0n)), inF)
      +onAt = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, Nat.add(i, 0n)), Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, v), Spec.steps(root, 0n)), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, i0)), onAt0)
      +fitT = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, []), True{}), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      +spT0 = G.spells_second(input, i, [], Spec.leaves(ts), spF)
      +nT = List.length(&2, Nat, Spec.leaves(ts))
      +spT = Equal.trans(+List<Nat>, Spec.leaves(ts), Lemma.slice(input, Nat.add(i, 0n), nT), Lemma.slice(input, i, nT), spT0, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, nT), Nat.add(i, 0n), i, i0))
      +finT = Equal.trans(Nat, Nat.add(i, List.length(&2, Nat, Spec.leaves(ts))), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, [], Spec.leaves(ts)))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), {==}, finF)
      ((p0, (g, (ts, (occ, (fitT, (spT, (inT, finT))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), step_at_eq(index, rpath, 1n+dot, k, i, i)), onAt), {==}))
    case Con{Spec.Loop{Con{Spec.Pick{+a, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +rounds = {Spec.Pick{a, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rounds), Spec.Brack{Spec.Group{}, alts})
      +okR = Spec.roundsOk(Spec.Closure{}, rounds)
      +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rounds, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      +fitR = Lemma.and_true_right_side(okR, Spec.fits(rounds, grammar, tm), hOk)
      +all = G.closure_reads(rounds, Lemma.and_true_left(okR, Spec.fits(rounds, grammar, tm), hOk))
      +reads = G.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), all))
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
      +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
      +lr = Spec.leaves(rounds)
      +spR = G.spells_first(input, i, lr, Spec.leaves(ts), spF)
      +spCh = G.spells_first(input, i, Spec.leaves(ch), Spec.leaves(r), spR)
      +seqEq = N1_and_right({L.evenLength(prefixOf(rpath)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}, seq_of(rpath, grammar, input, root, index, k, p0, g, occ))
      +next = List.get(&2, Nat, input, i)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsA = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a), i, ch, fitCh, spCh, reads)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, rpath, dot, alts, a, n, next, U.lt_ne(a, n, isA), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))), noConf)))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +rsT = {Spec.Leaf{x} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +rsT = {Spec.Node{q, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +rsT = {Spec.Skip{} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Closure{}, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +rsT = {Spec.Loop{rs} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+a}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}

law empty_on:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +k: Nat
  for +i: Nat
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  AllOn(grammar, input, root, Support.emptyStep(dot, index, rpath, k, i))

def empty_on(dot, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, k, i, inF):
  match dot:
    case 0n:
      +onAt = Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefixOf(rpath), 0n, k, i, i), Spec.steps(root, 0n)), True{}, inF)
      (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 0n, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 0n, k, i, i), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 0n, k, i, i), Spec.at(index, prefixOf(rpath), 0n, k, i, i), step_at_eq(index, rpath, 0n, k, i, i)), onAt), {==})
    case 1n+d:
      {==}

law end_on:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, 0n) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i))

def end_on(rpath, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, dot, k, i, p0, g, occ, inF, finF):
  match rpath:
    case Nil{}:
      match occ:
        case (pk, (x, (lhs, node))):
          +lhsIdx = Equal.trans(Bool, Spec.lhsIs(grammar, index, Gll.lhsOf(grammar, index)), Spec.lhsIs(grammar, index, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, index, v), Gll.lhsOf(grammar, index), x, G.lhs_of_is(grammar, index, x, lhs)), lhs)
          +endP = Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
          +endK = Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), i, Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves(g))), k, p0, Equal.sym(Nat, p0, k, pk)), endP)
          ((index, (g, (lhsIdx, (node, endK)))), empty_on(dot, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, [], k, i, inF))
    case Con{+a, Nil{}}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, [a], dot, k, i)), Lemma.false_is_not_true(occ))
    case Con{+a, Con{+m, +outer}}:
      +endP = Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
      ((a, (p0, (g, (occ, endP)))), empty_on(dot, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, a <> (m <> outer), k, i, inF))

law item_on:
  for it: Maybe<&2, Spec.Item>
  for f: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == it : Maybe<&2, Spec.Item>}
  AllOn(grammar, input, root, PS.itemGives(it, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i))

def item_on(it, f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, itEq):
  match it f:
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Nil{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +fitT = Fits.fits_tail(Spec.Leaf{a}, ts, grammar, Spec.Sym{Spec.Terminal{tm}}, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), fitF2)
      +lts = List.length(&2, Nat, Spec.leaves(ts))
      +spT = G.leaf_rest(input, i, a, Spec.leaves(ts), spF)
      +here = Spec.at(index, prefixOf(rpath), 1n+dot, k, i, 1n+i)
      +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, 1n+i)
      +inT = N1.all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, 1n+Nat.add(i, lts), Nat.add(i, 1n+lts), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Equal.sym(Nat, Nat.add(i, 1n+lts), 1n+Nat.add(i, lts), Lemma.add_succ_right(i, lts)), finF)
      on_when(Gll.tokenIs(List.get(&2, Nat, input, i), tm), PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, 1n+i}, Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)), grammar, input, root,
        on_when(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, 1n+i}), [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, 1n+i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i)}], grammar, input, root, ((p0, (g, (ts, (occ, (fitT, (spT, (inT, finT))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, 1n+i), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, 1n+i), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, 1n+i), step_at_eq(index, rpath, 1n+dot, k, i, 1n+i)), onAt), {==}))))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Skip{}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Nil{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +lch = Spec.leaves(ch)
      +e = Nat.add(i, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, i, lch, Spec.leaves(ts), spF)
      +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, e)
      +inCh = N1.all_in_left_n(wCh, wT, Spec.steps(root, 0n), N1.all_in_tail_n(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF))
      ((q, (ch, (lhsQ, (fitCh, (spCh, inCh))))), (((p0, (g, (Spec.Node{q, ch} <> ts, (occ, (fitF, (spF, (inF, finF))))))), itEq), {==}))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Skip{}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Nil{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Skip{}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +here = Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i)
      +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, i)
      +inT = N1.all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      on_when(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, i)}], grammar, input, root, ((p0, (g, (ts, (occ, (fitF2, (spF, (inT, finF))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, i), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, i), step_at_eq(index, rpath, 1n+dot, k, i, i)), onAt), {==})))
    case Some{Spec.Eps{}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Nil{}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Con{Spec.Leaf{+a}, +ts}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Con{Spec.Node{+q, +ch}, +ts}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Con{Spec.Pick{+a, +ch}, +ts}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Con{Spec.Skip{}, +ts}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Group{}, +alts}} Con{Spec.Loop{+rs}, +ts}:
      ((k, (Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Group{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Nil{}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Con{Spec.Leaf{+a}, +ts}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Con{Spec.Node{+q, +ch}, +ts}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Con{Spec.Pick{+a, +ch}, +ts}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Con{Spec.Skip{}, +ts}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Optional{}, +alts}} Con{Spec.Loop{+rs}, +ts}:
      ((k, (Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Optional{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_optional(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Nil{}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Con{Spec.Leaf{+a}, +ts}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Con{Spec.Node{+q, +ch}, +ts}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Con{Spec.Pick{+a, +ch}, +ts}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Con{Spec.Skip{}, +ts}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Closure{}, +alts}} Con{Spec.Loop{+rs}, +ts}:
      ((k, (Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Closure{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), skip_closure(f, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, i}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, alts, itEq, {==})))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Nil{}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Con{Spec.Leaf{+a}, +ts}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Con{Spec.Node{+q, +ch}, +ts}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Con{Spec.Pick{+a, +ch}, +ts}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Con{Spec.Skip{}, +ts}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case Some{Spec.Brack{Spec.Positive{}, +alts}} Con{Spec.Loop{+rs}, +ts}:
      ((k, (Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq)))), ((Spec.Positive{}, (alts, ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), ({==}, ({==}, itEq))))), {==}))
    case None{} Nil{}:
      end_on(rpath, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, dot, k, i, p0, g, occ, inF, finF)
    case None{} Con{Spec.Leaf{+a}, +ts}:
      +dNil = N1.nth_none_drop(Gll.seqAt(grammar, index, rpath), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Fits.fits_cons_nil(Spec.Leaf{a}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, []), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), [], Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), [], dNil)), fitF)))
    case None{} Con{Spec.Node{+q, +ch}, +ts}:
      +dNil = N1.nth_none_drop(Gll.seqAt(grammar, index, rpath), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Fits.fits_cons_nil(Spec.Node{q, ch}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, []), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), [], Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), [], dNil)), fitF)))
    case None{} Con{Spec.Pick{+a, +ch}, +ts}:
      +dNil = N1.nth_none_drop(Gll.seqAt(grammar, index, rpath), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Fits.fits_cons_nil(Spec.Pick{a, ch}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, []), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), [], Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), [], dNil)), fitF)))
    case None{} Con{Spec.Skip{}, +ts}:
      +dNil = N1.nth_none_drop(Gll.seqAt(grammar, index, rpath), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Fits.fits_cons_nil(Spec.Skip{}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, []), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), [], Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), [], dNil)), fitF)))
    case None{} Con{Spec.Loop{+rs}, +ts}:
      +dNil = N1.nth_none_drop(Gll.seqAt(grammar, index, rpath), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, Gll.Predict{t}, grammar, input, index, rpath, dot, k, i)), Fits.fits_cons_nil(Spec.Loop{rs}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, []), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), [], Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), [], dNil)), fitF)))

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

law same_group:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +a: Nat
  for +a2: Nat
  for +ae: {a == a2 : Nat}
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Pick{a2, ch} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def same_group(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitCh):
  +ea = Equal.sym(Nat, a, a2, ae)
  %ea : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, k}}])
  seed_pick_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, Spec.Group{}, alts, itEqB, a2, ch, ts, fitF, spF, inF, finF, fitCh)

# A seed of the group bracket on the tree: the tree's own alternate, else not admitted.
law seed_group:
  for ff: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}]))

def seed_group(ff, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, bEq):
  match ff b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a2, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits([], grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+x}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{x} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Leaf{x} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{x} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a2, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Group{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Group{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Group{}, alts}}, itEqB)), bEq)
      +hsA = h1
      +hP = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(ts), spF)
      +inCh = pick_child_walk(root, index, outer, m, kc, k, a2, ch, ts, inF)
      L.either_case({a == a2 : Nat}, {Nat.is_eq(a, a2) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), U.decide(Nat.is_eq(a, a2), a, a2, {==}),
        +ae => same_group(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitCh),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Group{}, grammar, t, index, outer, m, alts, a, a2, next, neq, seqEqO, itEqB, alt_has(True{}, False{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), alt_has(True{}, False{}, grammar, t, index, outer, m, alts, a2, next, isA2, round_predict_set(grammar, start, t, po, input, root, rootFit, rootSp, index, a2 <> (m <> outer), k, k, ch, (alt_fits(grammar, index, outer, m, a2, Spec.Group{}, alts, ch, itEqB, fitCh), (spCh, inCh)), round_seq_eq(grammar, index, outer, m, a2, evenO, seqEqO))))), noConf))))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Group{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))

law same_optional:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +a: Nat
  for +a2: Nat
  for +ae: {a == a2 : Nat}
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Pick{a2, ch} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Pick{a2, ch} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a2, ch} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a2)) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def same_optional(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitCh):
  +ea = Equal.sym(Nat, a, a2, ae)
  %ea : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, k}}])
  seed_pick_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, Spec.Optional{}, alts, itEqB, a2, ch, ts, fitF, spF, inF, finF, fitCh)

# A seed of the optional bracket on the tree: the tree's own alternate, else not admitted.
law seed_optional:
  for ff: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}]))

def seed_optional(ff, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, bEq):
  match ff b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a2, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits([], grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+x}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{x} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Leaf{x} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{x} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a2, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Optional{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Optional{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Optional{}, alts}}, itEqB)), bEq)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a), t))), Some{Spec.Brack{Spec.Optional{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Optional{}, alts}}, itEqB)), h1)
      +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a2, ch}])
      +hP = Bool.and(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +isA2 = Lemma.and_true_right_side(okR, Spec.isAlt(alts, a2), h2)
      +fitCh = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(alts, a2)), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hOk)
      +reads = G.optional_reads(a2, ch, Lemma.and_true_left(okR, Spec.isAlt(alts, a2), h2))
      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(ts), spF)
      +inCh = pick_child_walk(root, index, outer, m, kc, k, a2, ch, ts, inF)
      L.either_case({a == a2 : Nat}, {Nat.is_eq(a, a2) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), U.decide(Nat.is_eq(a, a2), a, a2, {==}),
        +ae => same_optional(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitCh),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Optional{}, grammar, t, index, outer, m, alts, a, a2, next, neq, seqEqO, itEqB, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a2, next, isA2, round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a2), k, ch, fitCh, spCh, reads)))), noConf))))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Optional{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Optional{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Optional{}, alts}}, itEqB)), bEq)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a), t))), Some{Spec.Brack{Spec.Optional{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Optional{}, alts}}, itEqB)), h1)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsL = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, k, Spec.Skip{}, ts, seqEqO, fitF, fitF2, spF, inF, {==})
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Optional{}, grammar, t, index, outer, m, alts, a, n, next, U.lt_ne(a, n, isA), seqEqO, itEqB, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL))), noConf)))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Optional{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))

law same_closure:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +a: Nat
  for +a2: Nat
  for +ae: {a == a2 : Nat}
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +fitR: {Spec.fits(Spec.Pick{a2, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Closure{}, k, k, Spec.Pick{a2, ch} <> r) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def same_closure(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, r, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitR, ready):
  +ea = Equal.sym(Nat, a, a2, ae)
  %ea : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, k}}])
  seed_loop_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, Spec.Closure{}, alts, itEqB, a2, ch, r, ts, fitF, spF, inF, finF, fitR, ready)

# A seed of the closure bracket on the tree: the tree's own alternate, else not admitted.
law seed_closure:
  for ff: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}]))

def seed_closure(ff, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, bEq):
  match ff b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a2, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits([], grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+x}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{x} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Leaf{x} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{x} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a2, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Closure{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqB)), bEq)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a), t))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqB)), h1)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +hsL = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, k, Spec.Loop{[]}, ts, seqEqO, fitF, fitF2, spF, inF, {==})
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, outer, m, alts, a, n, next, U.lt_ne(a, n, isA), seqEqO, itEqB, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL))), noConf)))
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Closure{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqB)), bEq)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a), t))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqB)), h1)
      +rounds = {Spec.Pick{a2, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rounds), Spec.Brack{Spec.Group{}, alts})
      +okR = Spec.roundsOk(Spec.Closure{}, rounds)
      +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rounds, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +fitR = Lemma.and_true_right_side(okR, Spec.fits(rounds, grammar, tm), hOk)
      +okRT = Lemma.and_true_left(okR, Spec.fits(rounds, grammar, tm), hOk)
      +ready = G.ready_entry(Spec.Closure{}, k, rounds, {==}, okRT)
      +h = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
      +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +spR = G.spells_first(input, k, Spec.leaves(rounds), Spec.leaves(ts), spF)
      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(r), spR)
      +inCh = round_child_walk(root, index, outer, m, k, k, a2, ch, r, loop_rounds_walk(root, index, outer, m, kc, k, rounds, ts, inF))
      +reads = G.consumes_child(a2, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a2, ch}), Spec.allConsume(r), G.closure_reads(rounds, okRT)))
      L.either_case({a == a2 : Nat}, {Nat.is_eq(a, a2) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), U.decide(Nat.is_eq(a, a2), a, a2, {==}),
        +ae => same_closure(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, r, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitR, ready),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, outer, m, alts, a, a2, next, neq, seqEqO, itEqB, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a2, next, isA2, round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a2), k, ch, fitCh, spCh, reads)))), noConf))))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Leaf{x} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Node{q, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Skip{} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Loop{rs} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rsT), Spec.fits(rsT, grammar, tm), inner)))

law same_positive:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +a: Nat
  for +a2: Nat
  for +ae: {a == a2 : Nat}
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +fitR: {Spec.fits(Spec.Pick{a2, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a2, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Positive{}, k, k, Spec.Pick{a2, ch} <> r) == True{} : Bool}
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])

def same_positive(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, r, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitR, ready):
  +ea = Equal.sym(Nat, a, a2, ae)
  %ea : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, k}}])
  seed_loop_on(grammar, input, root, index, outer, m, kc, k, p1, g1, occO, Spec.Positive{}, alts, itEqB, a2, ch, r, ts, fitF, spF, inF, finF, fitR, ready)

# A seed of the positive bracket on the tree: the tree's own alternate, else not admitted.
law seed_positive:
  for ff: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}]))

def seed_positive(ff, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, bEq):
  match ff b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a2, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} False{}:
      {==}
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} False{}:
      {==}
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits([], grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+x}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{x} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Leaf{x} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{x} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Pick{+a2, +ch}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Skip{}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Nil{}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{[]} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{[]} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{Con{Spec.Pick{+a2, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Pick{a2, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +next = List.get(&2, Nat, input, k)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Positive{}, alts}}, k, k), grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, k), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, k), grammar, t, index, a <> (m <> outer))), Some{Spec.Brack{Spec.Positive{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Positive{}, alts}}, itEqB)), bEq)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(False{}, grammar, t, index, a <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Bool.not(Nat.is_eq(k, k)), grammar, t, index, a <> (m <> outer))), True{},
        Equal.cong(Bool, Bool, v => Gll.lsHas(next, Gll.roundPick(Bool.not(v), grammar, t, index, a <> (m <> outer))), True{}, Nat.is_eq(k, k), Equal.sym(Bool, Nat.is_eq(k, k), True{}, Lemma.nat_eq_refl(k))), h1)
      +rounds = {Spec.Pick{a2, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rounds), Spec.Brack{Spec.Group{}, alts})
      +okR = Spec.roundsOk(Spec.Positive{}, rounds)
      +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rounds, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +fitR = Lemma.and_true_right_side(okR, Spec.fits(rounds, grammar, tm), hOk)
      +okRT = Lemma.and_true_left(okR, Spec.fits(rounds, grammar, tm), hOk)
      +ready = G.ready_entry(Spec.Positive{}, k, rounds, {==}, okRT)
      +h = Bool.and(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)))
      +hh = Lemma.and_true_left(h, Spec.fits(r, grammar, Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})), fitR)
      +isA2 = Lemma.and_true_left(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a2), Spec.fits(ch, grammar, Spec.altOf(alts, a2)), hh)
      +spR = G.spells_first(input, k, Spec.leaves(rounds), Spec.leaves(ts), spF)
      +spCh = G.spells_first(input, k, Spec.leaves(ch), Spec.leaves(r), spR)
      +inCh = round_child_walk(root, index, outer, m, k, k, a2, ch, r, loop_rounds_walk(root, index, outer, m, kc, k, rounds, ts, inF))
      L.either_case({a == a2 : Nat}, {Nat.is_eq(a, a2) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), U.decide(Nat.is_eq(a, a2), a, a2, {==}),
        +ae => same_positive(grammar, start, t, po, noConf, input, root, rootFit, rootSp, a, a2, ae, ch, r, ts, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, fitR, ready),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Positive{}, grammar, t, index, outer, m, alts, a, a2, next, neq, seqEqO, itEqB, alt_has(True{}, False{}, grammar, t, index, outer, m, alts, a, next, isA, hsA), alt_has(True{}, False{}, grammar, t, index, outer, m, alts, a2, next, isA2, round_predict_set(grammar, start, t, po, input, root, rootFit, rootSp, index, a2 <> (m <> outer), k, k, ch, (alt_fits(grammar, index, outer, m, a2, Spec.Positive{}, alts, ch, itEqB, fitCh), (spCh, inCh)), round_seq_eq(grammar, index, outer, m, a2, evenO, seqEqO))))), noConf))))
    case Con{Spec.Loop{Con{Spec.Leaf{+x}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Leaf{x} <> r} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Leaf{x} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Node{+q, +ch}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Node{q, ch} <> r} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Node{q, ch} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Skip{}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Skip{} <> r} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Skip{} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm), inner)))
    case Con{Spec.Loop{Con{Spec.Loop{+rs}, +r}}, +ts} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqB)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{Spec.Loop{rs} <> r} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +rsT = {Spec.Loop{rs} <> r : +List<Spec.Tree>}
      +tm = Spec.times(List.length(&2, Spec.Tree, rsT), Spec.Brack{Spec.Group{}, alts})
      +inner = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a <> (m <> outer), 0n, k, k}}])), Lemma.false_is_not_true(Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rsT), Spec.fits(rsT, grammar, tm), inner)))

# ======== A CLUSTER OF A NONTERMINAL ON THE TREE ========

law seed_node:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{q, [], 0n, i, i}}])

def seed_node(grammar, input, root, x, i, q, g, lhsQ, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +sp = {sp0 : G.Spells(g, input, i)}
      +inG = {in0 : {Spec.allIn(Spec.walk(g, False{}, q, [], 0n, i, i), Spec.steps(root, 0n)) == True{} : Bool}}
      ((i, (g, (g, (({==}, (x, (lhsQ, (fit, (sp, inG))))), (fit, (sp, (inG, {==}))))))), {==})

# The tree's own production, started at its node.
law seed_tree:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +q: Nat
  for +nq: {n == q : Nat}
  for +g: +List<Spec.Tree>
  for +lhsN: {Spec.lhsIs(grammar, n, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}])

def seed_tree(grammar, input, root, x, i, n, q, nq, g, lhsN, node):
  +qn = Equal.sym(Nat, n, q, nq)
  %qn : AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{_, [], 0n, i, i}}])
  seed_node(grammar, input, root, x, i, q, g, Equal.trans(Bool, Spec.lhsIs(grammar, q, x), Spec.lhsIs(grammar, n, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, v, x), q, n, qn), lhsN), node)

law seed_admitted:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +lhsN: {Spec.lhsIs(grammar, n, x) == True{} : Bool}
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{n, [], 0n, i, i}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]))

def seed_admitted(b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhsN, q, g, lhsQ, node, bEq):
  match b:
    case False{}:
      {==}
    case True{}:
      +next = List.get(&2, Nat, input, i)
      L.either_case({n == q : Nat}, {Nat.is_eq(n, q) == False{} : Bool}, AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]), U.decide(Nat.is_eq(n, q), n, q, {==}),
        +nq => seed_tree(grammar, input, root, x, i, n, q, nq, g, lhsN, node),
        neq => Empty.absurd(AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{n, [], 0n, i, i}}]),
          Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{},
            Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{},
              L.nonterminal_hits(grammar, t, x, n, q, next, neq, (lhsN, bEq),
                (lhsQ, L.predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, N1.node_predicts(grammar, start, input, root, rootFit, rootSp, i, q, g, node))))), noConf))))

law keep_seed:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +n: Nat
  for +lhs: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +ds: +List<Gll.Desc>
  for +bEq: {Nat.is_eq(lhs, x) == b : Bool}
  for +lhsEq: {Spec.lhsIs(grammar, n, x) == Nat.is_eq(lhs, x) : Bool}
  for +rec: AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, ds))
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.keepDesc(b, Gll.Desc{n, [], 0n, i, i}, ds)))

def keep_seed(b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhs, q, g, lhsQ, node, ds, bEq, lhsEq, rec):
  match b:
    case True{}:
      +d = {Gll.Desc{n, [], 0n, i, i} : Gll.Desc}
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, d), PS.descsWhen(Gll.Predict{t}, grammar, input, ds), grammar, input, root,
        seed_admitted(Gll.admits(Gll.Predict{t}, grammar, input, d), grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, Equal.trans(Bool, Spec.lhsIs(grammar, n, x), Nat.is_eq(lhs, x), True{}, lhsEq, bEq), q, g, lhsQ, node, {==}), rec)
    case False{}:
      rec

# The seeds of a cluster on the tree are on it (counting productions from n).
law seeds_on:
  for prods: +List<Spec.Production>
  for +n: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: N1.NodeAt(grammar, input, root, q, i, g)
  for +sub: {N1.dropProds(n, grammar) == prods : +List<Spec.Production>}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.productionsOf(prods, x, n, i)))

def seeds_on(prods, n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, sub):
  match prods:
    case Nil{}:
      {==}
    case Con{Spec.Production{+lhs, +rhs}, +rest}:
      +rec = seeds_on(rest, 1n+n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, N1.drop_next(grammar, n, Spec.Production{lhs, rhs}, rest, sub))
      keep_seed(Nat.is_eq(lhs, x), grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhs, q, g, lhsQ, node, Gll.productionsOf(rest, x, 1n+n, i), {==}, N1.drop_lhs(grammar, n, lhs, rhs, rest, x, sub), rec)


# ======== A CLUSTER OF A BRACKET ON THE TREE ========

law lt_up:
  for a: Nat
  for n: Nat
  for +h: {Nat.is_lt(a, n) == True{} : Bool}
  {Nat.is_lt(a, 1n+n) == True{} : Bool}

def lt_up(a, n, h):
  match a n:
    case 0n _:
      {==}
    case 1n+b 0n:
      Empty.absurd({Nat.is_lt(1n+b, 1n) == True{} : Bool}, Lemma.lt_zero_false(1n+b, h))
    case 1n+(+b) 1n+(+c):
      lt_up(b, c, h)

law seed_any:
  for kind: Spec.Bracket
  for ff: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +isA: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}))

def seed_any(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA):
  match kind:
    case Spec.Group{}:
      seed_group(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Optional{}:
      seed_optional(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Closure{}:
      seed_closure(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})
    case Spec.Positive{}:
      seed_positive(ff, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, isA, {==})

law alts_seed_on:
  for n: Nat
  for +kind: Spec.Bracket
  for +ff: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqB: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +hn: {Nat.is_lt(n, 1n+List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(n, index, m <> outer, k, k)))

def alts_seed_on(n, kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, hn):
  match n:
    case 0n:
      {==}
    case 1n+(+a):
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a <> (m <> outer), 0n, k, k}), PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(a, index, m <> outer, k, k)), grammar, input, root,
        seed_any(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, a, hn),
        alts_seed_on(a, kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, lt_up(a, List.length(&2, +List<Spec.Item>, alts), hn)))

# The seeds of a bracket's cluster on the tree are on it.
law bracket_seeds_on:
  for rp: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +k: Nat
  for +here: clusterOn(grammar, input, root, Gll.CKey{Gll.TBr{index, rp}, k})
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Check.seedsOf(grammar, Gll.CKey{Gll.TBr{index, rp}, k})))

def bracket_seeds_on(rp, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, k, here):
  match rp:
    case Nil{}:
      Empty.absurd(AllOn(grammar, input, root, []), Lemma.false_is_not_true(here))
    case Con{+m, +outer}:
      match here:
        case (kc, (kind, (alts, ((p1, (g1, (ff, (occO, (fitF, (spF, (inF, finF))))))), itEqB)))):
          +itBS = Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itEqB)
          %itBS : AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(Check.altCount(_), index, m <> outer, k, k)))
          alts_seed_on(List.length(&2, +List<Spec.Item>, alts), kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqB, L.lt_succ_self(List.length(&2, +List<Spec.Item>, alts)))

# ======== RESUMING A CALLER ON THE TREE ========

# At a pop of a nonterminal's node: the caller's node ends there, so the resumed descriptor
# and its step are on the tree.
law resume_nt:
  for f: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +y: Nat
  for +end: Nat
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{y}}} : Maybe<&2, Spec.Item>}
  for +pop: N1.NtEnds(grammar, input, root, y, i, end)
  AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end)))

def resume_nt(f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, y, end, itEq, pop):
  match f:
    case Nil{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits([], grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+a}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts}:
      match pop:
        case (q2, (g2, (lhs2, (node2, ends2)))):
          +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
          +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
            Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
          +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), fitF2)
          +lch = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +e = Nat.add(i, List.length(&2, Nat, lch))
          +spCh = G.spells_first(input, i, lch, lts, spF)
          +spT = G.spells_second(input, i, lch, lts, spF)
          +here = Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
          +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, e)
          +inA = N1.all_in_tail_n(here, List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF)
          +inCh = N1.all_in_left_n(wCh, wT, Spec.steps(root, 0n), inA)
          +inT = N1.all_in_right_n(wCh, wT, Spec.steps(root, 0n), inA)
          +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n)), inF)
          +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), G.end_split(i, lch, lts), finF)
          +same = N1.nodes_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, y, i, q, q2, ch, g2, lhsQ, lhs2, (fitCh, (spCh, inCh)), node2)
          +ge = N1.U_and_right({q == q2 : Nat}, {ch == g2 : +List<Spec.Tree>}, same)
          +eEnd = Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g2))), end, Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g2, ge), ends2)
          %eEnd : AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, _}, Gll.stepAt(index, rpath, 1n+dot, k, i, _)))
          on_when(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, e}), [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, e}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, e)}], grammar, input, root,
            ((p0, (g, (ts, (occ, (fitT, (spT, (inT, finT))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), step_at_eq(index, rpath, 1n+dot, k, i, e)), onAt), {==})))
    case Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Skip{}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{+rs}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))

# Two callers of one sequence position, at one input position, have the same forest from
# there on.
law suffix_same:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +kc1: Nat
  for +kc2: Nat
  for +k: Nat
  for +f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +even: {L.evenLength(prefixOf(rpath)) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +fit1: {Spec.fits(f1, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +fit2: {Spec.fits(f2, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +sp1: G.Spells(f1, input, k)
  for +sp2: G.Spells(f2, input, k)
  for +in1: {Spec.allIn(Spec.walk(f1, False{}, index, prefixOf(rpath), dot, kc1, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +in2: {Spec.allIn(Spec.walk(f2, False{}, index, prefixOf(rpath), dot, kc2, k), Spec.steps(root, 0n)) == True{} : Bool}
  {f1 == f2 : +List<Spec.Tree>}

def suffix_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, kc1, kc2, k, f1, f2, even, seqEq, fit1, fit2, sp1, sp2, in1, in2):
  +p = prefixOf(rpath)
  +items = Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, p))
  +iEq = Equal.trans(+List<Spec.Item>, items, Gll.dropFrom(dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)),
    L.items_from_eq(dot, Spec.sequenceAt(grammar, index, p)), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, rpath), seqEq))
  +fitS1 = Equal.trans(Bool, Spec.fits(f1, grammar, items), Spec.fits(f1, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f1, grammar, v), items, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), iEq), fit1)
  +fitS2 = Equal.trans(Bool, Spec.fits(f2, grammar, items), Spec.fits(f2, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), items, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), iEq), fit2)
  N1.same_or_clash(grammar, start, t, po, noConf, f1, f2,
    U.compare(f1, False{}, f2, items, grammar, start, input, root, rootFit, rootSp, root, rootFit, rootSp, index, p, dot, kc1, kc2, k, Spec.Group{}, [], [], False{}, 0n, 0n,
      (fitS1, (fitS2, (sp1, (sp2, (in1, (in2, ({==}, even)))))))))

law move_round:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +fe: {f1 == f2 : +List<Spec.Tree>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +a: Nat
  for +k: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ri: RoundIn(f1, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  RoundIn(f2, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)

def move_round(grammar, input, root, f1, f2, fe, index, outer, m, a, k, p0, g, kind, alts, ri):
  %fe : RoundIn(_, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  ri

law resume_next:
  for kind0: Spec.Bracket
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +p0c: Nat
  for +gc: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0c, gc)
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, i)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind0, alts}} : Maybe<&2, Spec.Item>}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +a3: Nat
  for +g3: +List<Spec.Tree>
  for +r3: +List<Spec.Tree>
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3), grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3)), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3), input, p0)
  for +ready: {G.roundsReady(kind0, i, p0, Spec.Pick{a, g} <> (Spec.Pick{a3, g3} <> r3)) == True{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}) == True{} : Bool}
  AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}]))

def resume_next(kind0, grammar, start, t, po, noConf, input, root, rootFit, rootSp, rs, ts, index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, alts, itEq, seqEq, a, p0, g, a3, g3, r3, endEq, fitR, spR, ready, bEq):
  match kind0:
    case Spec.Closure{}:
      +allR = Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, g}), Spec.allConsume(Spec.Pick{a3, g3} <> r3), ready)
      +next = List.get(&2, Nat, input, end)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +sp3 = G.spells_first(input, Nat.add(p0, List.length(&2, Nat, lg)), Spec.leaves(g3), Spec.leaves(r3), sp2)
      +n3 = List.length(&2, Nat, Spec.leaves(g3))
      +spG3 = Equal.trans(+List<Nat>, Spec.leaves(g3), Lemma.slice(input, Nat.add(p0, List.length(&2, Nat, lg)), n3), Lemma.slice(input, end, n3), sp3, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, n3), Nat.add(p0, List.length(&2, Nat, lg)), end, endEq))
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, rpath, dot, alts, a3, n, next, U.lt_ne(a3, n, isA3), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a3, next, isA3, hsA3), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))), noConf)))
    case Spec.Positive{}:
      +allR = G.positive_next(i, p0, end, a, g, Spec.Pick{a3, g3} <> r3, ready)
      +next = List.get(&2, Nat, input, end)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +sp3 = G.spells_first(input, Nat.add(p0, List.length(&2, Nat, lg)), Spec.leaves(g3), Spec.leaves(r3), sp2)
      +n3 = List.length(&2, Nat, Spec.leaves(g3))
      +spG3 = Equal.trans(+List<Nat>, Spec.leaves(g3), Lemma.slice(input, Nat.add(p0, List.length(&2, Nat, lg)), n3), Lemma.slice(input, end, n3), sp3, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, n3), Nat.add(p0, List.length(&2, Nat, lg)), end, endEq))
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, after_conflict(grammar, t, index, rpath, dot, alts, a3, n, next, U.lt_ne(a3, n, isA3), seqEq, itEq, alt_has(False{}, True{}, grammar, t, index, rpath, dot, alts, a3, next, isA3, hsA3), leave_has2(False{}, grammar, t, index, rpath, dot, alts, next, bEq))), noConf)))
    case Spec.Group{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Group{}, alts}, itEq)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Group{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)))
    case Spec.Optional{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{Spec.Optional{}, alts}, itEq)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)))

# At the end of a round of a loop on the tree: the loop's end, or a resume that prediction
# does not admit (another round follows, and it reads something).
law resume_loop:
  for r2: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +p0c: Nat
  for +gc: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0c, gc)
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, i)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))) : Nat}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +ready: {G.roundsReady(kind, i, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(i, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}]))

def resume_loop(r2, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, rs, ts, index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, kind, alts, itEq, seqEq, a, p0, g, endEq, fitR, spR, ready, sumEq, bEq):
  match r2 b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Pick{+a3, +g3}, +r3} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +r3} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +r3} False{}:
      {==}
    case Con{Spec.Skip{}, +r3} False{}:
      {==}
    case Con{Spec.Loop{+rr}, +r3} False{}:
      {==}
    case Nil{} True{}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{kind, alts}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
      +fitT = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{kind, alts}, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), fitF2)
      +lx = Spec.leaves(rs)
      +lts = Spec.leaves(ts)
      +e = Nat.add(i, List.length(&2, Nat, lx))
      +spT = G.spells_second(input, i, lx, lts, spF)
      +here = Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e)
      +wX = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefixOf(rpath), [dot]), 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, e)
      +inA = N1.all_in_tail_n(here, List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n), inF)
      +inT = N1.all_in_right_n(wX, wT, Spec.steps(root, 0n), inA)
      +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lx, lts))), Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))), G.end_split(i, lx, lts), finF)
      +lg = Spec.leaves(g)
      +eEnd = Equal.trans(Nat, e, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), end, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), e, sumEq),
        Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), Nat.add(p0, List.length(&2, Nat, lg)), end, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, lg)), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), G.end_alone(p0, lg)), endEq))
      %eEnd : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, _}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, _)}]))
      ((p0c, (gc, (ts, (occ, (fitT, (spT, (inT, finT))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), step_at_eq(index, rpath, 1n+dot, k, i, e)), onAt), {==}))
    case Con{Spec.Pick{+a3, +g3}, +r3} True{}:
      resume_next(kind, grammar, start, t, po, noConf, input, root, rootFit, rootSp, rs, ts, index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, alts, itEq, seqEq, a, p0, g, a3, g3, r3, endEq, fitR, spR, ready, bEq)
    case Con{Spec.Leaf{+x}, +r3} True{}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Leaf{x} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Leaf{x} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Node{+q, +ch}, +r3} True{}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Node{q, ch} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Node{q, ch} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Skip{}, +r3} True{}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Skip{} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Skip{} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Loop{+rr}, +r3} True{}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Loop{rr} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Loop{rr} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(inner))

law resume_br_f:
  for ff: +List<Spec.Tree>
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +p0c: Nat
  for +gc: +List<Spec.Tree>
  for +occ: SeqOcc(rpath, grammar, input, root, index, k, p0c, gc)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +spF: G.Spells(ff, input, i)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(rpath), dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))) : Nat}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +ri: RoundIn(ff, grammar, input, root, index, rpath, dot, a, i, p0, g, kind, alts)
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}]))

def resume_br_f(ff, b, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, kind, alts, itEq, seqEq, a, p0, g, ri, endEq, bEq):
  match ff b:
    case Nil{} False{}:
      {==}
    case Con{Spec.Leaf{+x}, +ts} False{}:
      {==}
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Pick{+a2, +ch}, +ts} False{}:
      {==}
    case Con{Spec.Skip{}, +ts} False{}:
      {==}
    case Con{Spec.Loop{+rs}, +ts} False{}:
      {==}
    case Nil{} True{}:
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(ri))
    case Con{Spec.Leaf{+x}, +ts} True{}:
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(ri))
    case Con{Spec.Node{+q, +ch}, +ts} True{}:
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(ri))
    case Con{Spec.Pick{+a2, +ch}, +ts} True{}:
      match ri:
        case (ae, (ce, pe)):
          +dEq = N1.nth_drop(Gll.seqAt(grammar, index, rpath), dot, Spec.Brack{kind, alts}, itEq)
          +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))), True{},
            Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Spec.Brack{kind, alts} <> Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), dEq)), fitF)
          +fitT = Fits.fits_tail(Spec.Pick{a2, ch}, ts, grammar, Spec.Brack{kind, alts}, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, rpath)), fitF2)
          +lx = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +e = Nat.add(i, List.length(&2, Nat, lx))
          +spT = G.spells_second(input, i, lx, lts, spF)
          +here = Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e)
          +wX = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefixOf(rpath), [dot, a2]), 0n, i, i)
          +wT = Spec.walk(ts, False{}, index, prefixOf(rpath), 1n+dot, k, e)
          +inA = N1.all_in_tail_n(here, List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n), inF)
          +inT = N1.all_in_right_n(wX, wT, Spec.steps(root, 0n), inA)
          +onAt = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wX, wT), Spec.steps(root, 0n)), inF)
          +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lx, lts))), Nat.add(p0c, List.length(&2, Nat, Spec.leaves(gc))), G.end_split(i, lx, lts), finF)
          +eEnd = Equal.trans(Nat, e, Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), end,
            Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g))), Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))), Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g, ce),
              Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves(g))), i, p0, Equal.sym(Nat, p0, i, pe))), endEq)
          %eEnd : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, _}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, _)}]))
          ((p0c, (gc, (ts, (occ, (fitT, (spT, (inT, finT))))))), (Equal.trans(Bool, Spec.bsrMember(Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.steps(root, 0n)), Spec.bsrMember(Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), Gll.stepAt(index, rpath, 1n+dot, k, i, e), Spec.at(index, prefixOf(rpath), 1n+dot, k, i, e), step_at_eq(index, rpath, 1n+dot, k, i, e)), onAt), {==}))
    case Con{Spec.Skip{}, +ts} True{}:
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, rpath, 1n+dot, k, end}}, Support.FactStep{Gll.stepAt(index, rpath, 1n+dot, k, i, end)}])), Lemma.false_is_not_true(ri))
    case Con{Spec.Loop{+rs}, +ts} True{}:
      match ri:
        case (r2, (fitR, (spR, (inR, (ready, sumEq))))):
          resume_loop(r2, True{}, grammar, start, t, po, noConf, input, root, rootFit, rootSp, rs, ts, index, rpath, dot, k, i, end, p0c, gc, occ, fitF, spF, inF, finF, kind, alts, itEq, seqEq, a, p0, g, endEq, fitR, spR, ready, sumEq, bEq)

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
  %ie : popOn(grammar, input, root, Gll.CKey{Gll.TBr{_, rp2}, i}, end)
  %re : popOn(grammar, input, root, Gll.CKey{Gll.TBr{index2, _}, i}, end)
  pop

law resume_br:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +end: Nat
  for +d: descOn(grammar, input, root, Gll.Desc{index, rpath, dot, k, i})
  for +pop: popOn(grammar, input, root, Gll.CKey{Gll.TBr{index, dot <> rpath}, i}, end)
  AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}, Gll.stepAt(index, rpath, 1n+dot, k, i, end)))

def resume_br(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, end, d, pop):
  match d:
    case (p0c, (gc, (f2, (occ2, (fitF2, (spF2, (inF2, finF2))))))):
      match pop:
        case (a, (p0, (g, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, (gAt, ri)))))))))), endEq)))):
          +sq = seq_of(rpath, grammar, input, root, index, k, p0c, gc, occ2)
          +even = N1_and_left({L.evenLength(prefixOf(rpath)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}, sq)
          +seqEq = N1_and_right({L.evenLength(prefixOf(rpath)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(rpath)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}, sq)
          +fe = suffix_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, kc, k, i, ff, f2, even, seqEq, fitF, fitF2, spF, spF2, inF, inF2)
          +ri2 = move_round(grammar, input, root, ff, f2, fe, index, rpath, dot, a, i, p0, g, kind, alts, ri)
          resume_br_f(f2, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, rpath, 1n+dot, k, end}), grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, end, p0c, gc, occ2, fitF2, spF2, inF2, finF2, kind, alts, itEqP, seqEq, a, p0, g, ri2, endEq, {==})

# A return edge on the tree, resumed at a pop on the tree.
law resume_on:
  for key: Gll.CKey
  for edge: Gll.Edge
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +end: Nat
  for +here: returnOn(grammar, input, root, key, edge)
  for +pop: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, PS.resumeGives(Gll.Predict{t}, grammar, input, key, edge, end))

def resume_on(key, edge, grammar, start, t, po, noConf, input, root, rootFit, rootSp, end, here, pop):
  match key edge:
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      match here:
        case ((p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))), itEq):
          resume_nt(f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, y, end, itEq, pop)
    case Gll.CKey{Gll.TBr{+index2, +rp}, +i} Gll.Edge{+index, +rpath, +dot, +k}:
      match here:
        case (kindR, (altsR, (d, (ie, (re, itEqR))))):
          resume_br(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, end, d, pop_br_move(grammar, input, root, index2, index, rp, dot <> rpath, i, end, ie, re, pop))

law again_same_closure:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +a1: Nat
  for +a3: Nat
  for +ae: {a1 == a3 : Nat}
  for +g3: +List<Spec.Tree>
  for +r3: +List<Spec.Tree>
  for +end: Nat
  for +fitRest: {Spec.fits(Spec.Pick{a3, g3} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a3, g3} <> r3), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spRest: G.Spells(Spec.Pick{a3, g3} <> r3, input, end)
  for +inRest: {Spec.allIn(Spec.walk(Spec.Pick{a3, g3} <> r3, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, end), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready3: {G.roundsReady(Spec.Closure{}, k, end, Spec.Pick{a3, g3} <> r3) == True{} : Bool}
  for +sum3: {Nat.add(end, List.length(&2, Nat, Spec.leaves(Spec.Pick{a3, g3} <> r3))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +fitG3: {Spec.fits(g3, grammar, Spec.altOf(alts, a3)) == True{} : Bool}
  AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_same_closure(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3):
  +ea = Equal.sym(Nat, a1, a3, ae)
  %ea : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, end}}]))
  +fitC = alt_fits(grammar, index, outer, m, a3, Spec.Closure{}, alts, g3, itEqP, fitG3)
  +spC = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
  +inC = round_child_walk(root, index, outer, m, k, end, a3, g3, r3, inRest)
  +ff = {Spec.Loop{rs} <> ts : +List<Spec.Tree>}
  ((end, (g3, (g3, ((kc, (p1, (g1, (ff, (Spec.Closure{}, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, ((fitC, (spC, inC)), (r3, (fitRest, (spRest, (inRest, (ready3, sum3))))))))))))))), (fitC, (spC, (inC, {==}))))))), {==})

# Another round of the closure loop, at a round's end that is not the loop's start.
law again_next_closure:
  for r2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Closure{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == False{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}) == True{} : Bool}
  AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_next_closure(r2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq):
  match r2:
    case Nil{}:
      +next = List.get(&2, Nat, input, end)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Closure{}, alts}}, k, end), grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, end), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, end), grammar, t, index, a1 <> (m <> outer))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqP)), bEq)
      +h1b = h1
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a1), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a1), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a1), t))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqP)), h1b)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +tmR = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +fitT = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tmR)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +lrs = Spec.leaves(rs)
      +lts = Spec.leaves(ts)
      +eL = Nat.add(k, List.length(&2, Nat, lrs))
      +spT = G.spells_second(input, k, lrs, lts, spF)
      +hsL0 = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, eL, Spec.Loop{rs}, ts, seqEqO, fitF, fitT, spT, inF, Equal.sym(Nat, Nat.add(eL, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), G.end_split(k, lrs, lts)))
      +lg = Spec.leaves(g)
      +endL = Equal.trans(Nat, end, Nat.add(p0, List.length(&2, Nat, lg)), eL, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, lg)), end, endEq),
        Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, lg)), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), eL, G.end_alone(p0, lg), sumEq))
      +hsL = Equal.trans(Bool, Gll.lsHas(next, Gll.predictAt(grammar, t, index, outer, 1n+m)), Gll.lsHas(List.get(&2, Nat, input, eL), Gll.predictAt(grammar, t, index, outer, 1n+m)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.predictAt(grammar, t, index, outer, 1n+m)), end, eL, endL), hsL0)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, outer, m, alts, a1, n, next, U.lt_ne(a1, n, isA1), seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL))), noConf)))
    case Con{Spec.Pick{+a3, +g3}, +r3}:
      +next = List.get(&2, Nat, input, end)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Closure{}, alts}}, k, end), grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, end), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, end), grammar, t, index, a1 <> (m <> outer))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqP)), bEq)
      +h1b = h1
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a1), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a1), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a1), t))), Some{Spec.Brack{Spec.Closure{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Closure{}, alts}}, itEqP)), h1b)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +allR = Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, g}), Spec.allConsume(rest2), ready)
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +eg = Nat.add(p0, List.length(&2, Nat, lg))
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +nR = List.length(&2, Nat, Spec.leaves(rest2))
      +spRest = Equal.trans(+List<Nat>, Spec.leaves(rest2), Lemma.slice(input, eg, nR), Lemma.slice(input, end, nR), sp2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, nR), eg, end, endEq))
      +spG3 = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
      +wG = Spec.walk(g, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefixOf(outer), [m]), [a]), 0n, k, p0)
      +wRest = Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, eg)
      +inRest0 = N1.all_in_right_n(wG, wRest, Spec.steps(root, 0n), inR)
      +inRest = Equal.trans(Bool, Spec.allIn(Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, end), Spec.steps(root, 0n)), Spec.allIn(wRest, Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, v), Spec.steps(root, 0n)), end, eg, Equal.sym(Nat, eg, end, endEq)), inRest0)
      +ready3 = G.round_next(Spec.Closure{}, k, p0, end, a, g, rest2, {==}, ready)
      +sum3 = Equal.trans(Nat, Nat.add(end, nR), Nat.add(eg, nR), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), Equal.cong(Nat, Nat, v => Nat.add(v, nR), end, eg, Equal.sym(Nat, eg, end, endEq)),
        Equal.trans(Nat, Nat.add(eg, nR), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, Spec.leaves(rest2)))), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), G.end_split(p0, lg, Spec.leaves(rest2)), sumEq))
      L.either_case({a1 == a3 : Nat}, {Nat.is_eq(a1, a3) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), U.decide(Nat.is_eq(a1, a3), a1, a3, {==}),
        +ae => again_same_closure(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, enter_conflict(Spec.Closure{}, grammar, t, index, outer, m, alts, a1, a3, next, neq, seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a3, next, isA3, hsA3))), noConf))))
    case Con{Spec.Leaf{+x}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Leaf{x} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Leaf{x} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Node{+q, +ch}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Node{q, ch} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Node{q, ch} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Skip{}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Skip{} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Skip{} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Loop{+rr}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Loop{rr} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Loop{rr} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))

law again_one_closure:
  for b: Bool
  for b2: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +r2: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Closure{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == b2 : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_one_closure(b, b2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq):
  match b b2:
    case False{} _:
      {==}
    case True{} True{}:
      +ke = Lemma.nat_eq_sound(k, end, b2Eq)
      %ke : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, _}}]))
      +bK = Equal.trans(Bool, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, k}), Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), True{},
        Equal.cong(Nat, Bool, v => Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, v}), k, end, ke), bEq)
      seed_closure(Spec.Loop{rs} <> ts, True{}, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a1, isA1, bK)
    case True{} False{}:
      again_next_closure(r2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq)

law again_same_positive:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +a1: Nat
  for +a3: Nat
  for +ae: {a1 == a3 : Nat}
  for +g3: +List<Spec.Tree>
  for +r3: +List<Spec.Tree>
  for +end: Nat
  for +fitRest: {Spec.fits(Spec.Pick{a3, g3} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a3, g3} <> r3), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spRest: G.Spells(Spec.Pick{a3, g3} <> r3, input, end)
  for +inRest: {Spec.allIn(Spec.walk(Spec.Pick{a3, g3} <> r3, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, end), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready3: {G.roundsReady(Spec.Positive{}, k, end, Spec.Pick{a3, g3} <> r3) == True{} : Bool}
  for +sum3: {Nat.add(end, List.length(&2, Nat, Spec.leaves(Spec.Pick{a3, g3} <> r3))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +fitG3: {Spec.fits(g3, grammar, Spec.altOf(alts, a3)) == True{} : Bool}
  AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_same_positive(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3):
  +ea = Equal.sym(Nat, a1, a3, ae)
  %ea : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, _ <> (m <> outer), 0n, k, end}}]))
  +fitC = alt_fits(grammar, index, outer, m, a3, Spec.Positive{}, alts, g3, itEqP, fitG3)
  +spC = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
  +inC = round_child_walk(root, index, outer, m, k, end, a3, g3, r3, inRest)
  +ff = {Spec.Loop{rs} <> ts : +List<Spec.Tree>}
  ((end, (g3, (g3, ((kc, (p1, (g1, (ff, (Spec.Positive{}, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, ((fitC, (spC, inC)), (r3, (fitRest, (spRest, (inRest, (ready3, sum3))))))))))))))), (fitC, (spC, (inC, {==}))))))), {==})

# Another round of the positive loop, at a round's end that is not the loop's start.
law again_next_positive:
  for r2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Positive{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == False{} : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}) == True{} : Bool}
  AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_next_positive(r2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq):
  match r2:
    case Nil{}:
      +next = List.get(&2, Nat, input, end)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Positive{}, alts}}, k, end), grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, end), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, end), grammar, t, index, a1 <> (m <> outer))), Some{Spec.Brack{Spec.Positive{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Positive{}, alts}}, itEqP)), bEq)
      +h1b = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(True{}, grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Bool.not(Nat.is_eq(k, end)), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Bool, Bool, v => Gll.lsHas(next, Gll.roundPick(Bool.not(v), grammar, t, index, a1 <> (m <> outer))), False{}, Nat.is_eq(k, end), Equal.sym(Bool, Nat.is_eq(k, end), False{}, b2Eq)), h1)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a1), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a1), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a1), t))), Some{Spec.Brack{Spec.Positive{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Positive{}, alts}}, itEqP)), h1b)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      +tmR = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})
      +fitT = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tmR)), Spec.fits(ts, grammar, Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), fitF2)
      +lrs = Spec.leaves(rs)
      +lts = Spec.leaves(ts)
      +eL = Nat.add(k, List.length(&2, Nat, lrs))
      +spT = G.spells_second(input, k, lrs, lts, spF)
      +hsL0 = leave_set(grammar, start, t, po, input, root, rootFit, rootSp, index, outer, m, kc, k, eL, Spec.Loop{rs}, ts, seqEqO, fitF, fitT, spT, inF, Equal.sym(Nat, Nat.add(eL, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lrs, lts))), G.end_split(k, lrs, lts)))
      +lg = Spec.leaves(g)
      +endL = Equal.trans(Nat, end, Nat.add(p0, List.length(&2, Nat, lg)), eL, Equal.sym(Nat, Nat.add(p0, List.length(&2, Nat, lg)), end, endEq),
        Equal.trans(Nat, Nat.add(p0, List.length(&2, Nat, lg)), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, []))), eL, G.end_alone(p0, lg), sumEq))
      +hsL = Equal.trans(Bool, Gll.lsHas(next, Gll.predictAt(grammar, t, index, outer, 1n+m)), Gll.lsHas(List.get(&2, Nat, input, eL), Gll.predictAt(grammar, t, index, outer, 1n+m)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.predictAt(grammar, t, index, outer, 1n+m)), end, eL, endL), hsL0)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, after_conflict(grammar, t, index, outer, m, alts, a1, n, next, U.lt_ne(a1, n, isA1), seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), leave_has2(False{}, grammar, t, index, outer, m, alts, next, hsL))), noConf)))
    case Con{Spec.Pick{+a3, +g3}, +r3}:
      +next = List.get(&2, Nat, input, end)
      +h1 = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Some{Spec.Brack{Spec.Positive{}, alts}}, k, end), grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, end), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.roundPick(Gll.roundReads(v, k, end), grammar, t, index, a1 <> (m <> outer))), Some{Spec.Brack{Spec.Positive{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Positive{}, alts}}, itEqP)), bEq)
      +h1b = Equal.trans(Bool, Gll.lsHas(next, Gll.roundPick(True{}, grammar, t, index, a1 <> (m <> outer))), Gll.lsHas(next, Gll.roundPick(Bool.not(Nat.is_eq(k, end)), grammar, t, index, a1 <> (m <> outer))), True{},
        Equal.cong(Bool, Bool, v => Gll.lsHas(next, Gll.roundPick(Bool.not(v), grammar, t, index, a1 <> (m <> outer))), False{}, Nat.is_eq(k, end), Equal.sym(Bool, Nat.is_eq(k, end), False{}, b2Eq)), h1)
      +hsA = Equal.trans(Bool, Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Spec.altOf(alts, a1), t))), Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), a1), t))), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.firstOf(Gll.infoItems(Gll.bracketAlt(v, a1), t))), Some{Spec.Brack{Spec.Positive{}, alts}}, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{Spec.Positive{}, alts}}, itEqP)), h1b)
      +sq = seq_of(outer, grammar, input, root, index, kc, p1, g1, occO)
      +evenO = N1_and_left({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +seqEqO = N1_and_right({L.evenLength(prefixOf(outer)) == True{} : Bool}, {Spec.sequenceAt(grammar, index, prefixOf(outer)) == Gll.seqAt(grammar, index, outer) : +List<Spec.Item>}, sq)
      +n = List.length(&2, +List<Spec.Item>, alts)
      +rest2 = {Spec.Pick{a3, g3} <> r3 : +List<Spec.Tree>}
      +allR = G.positive_next(k, p0, end, a, g, rest2, ready)
      +fitRest = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(rest2, grammar, Spec.times(List.length(&2, Spec.Tree, rest2), Spec.Brack{Spec.Group{}, alts})), fitR)
      +h3 = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3))), Spec.fits(r3, grammar, Spec.times(List.length(&2, Spec.Tree, r3), Spec.Brack{Spec.Group{}, alts})), fitRest)
      +isA3 = Lemma.and_true_left(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +fitG3 = Lemma.and_true_right_side(Spec.isAlt(alts, a3), Spec.fits(g3, grammar, Spec.altOf(alts, a3)), h3)
      +reads3 = G.consumes_child(a3, g3, Lemma.and_true_left(Spec.consumes(Spec.Pick{a3, g3}), Spec.allConsume(r3), allR))
      +lg = Spec.leaves(g)
      +eg = Nat.add(p0, List.length(&2, Nat, lg))
      +sp2 = G.spells_second(input, p0, lg, Spec.leaves(rest2), spR)
      +nR = List.length(&2, Nat, Spec.leaves(rest2))
      +spRest = Equal.trans(+List<Nat>, Spec.leaves(rest2), Lemma.slice(input, eg, nR), Lemma.slice(input, end, nR), sp2, Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, nR), eg, end, endEq))
      +spG3 = G.spells_first(input, end, Spec.leaves(g3), Spec.leaves(r3), spRest)
      +hsA3 = round_first_set(grammar, start, t, po, input, Spec.altOf(alts, a3), end, g3, fitG3, spG3, reads3)
      +wG = Spec.walk(g, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefixOf(outer), [m]), [a]), 0n, k, p0)
      +wRest = Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, eg)
      +inRest0 = N1.all_in_right_n(wG, wRest, Spec.steps(root, 0n), inR)
      +inRest = Equal.trans(Bool, Spec.allIn(Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, end), Spec.steps(root, 0n)), Spec.allIn(wRest, Spec.steps(root, 0n)), True{},
        Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(rest2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, v), Spec.steps(root, 0n)), end, eg, Equal.sym(Nat, eg, end, endEq)), inRest0)
      +ready3 = G.round_next(Spec.Positive{}, k, p0, end, a, g, rest2, {==}, ready)
      +sum3 = Equal.trans(Nat, Nat.add(end, nR), Nat.add(eg, nR), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), Equal.cong(Nat, Nat, v => Nat.add(v, nR), end, eg, Equal.sym(Nat, eg, end, endEq)),
        Equal.trans(Nat, Nat.add(eg, nR), Nat.add(p0, List.length(&2, Nat, List.append(&2, Nat, lg, Spec.leaves(rest2)))), Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), G.end_split(p0, lg, Spec.leaves(rest2)), sumEq))
      L.either_case({a1 == a3 : Nat}, {Nat.is_eq(a1, a3) == False{} : Bool}, AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), U.decide(Nat.is_eq(a1, a3), a1, a3, {==}),
        +ae => again_same_positive(grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a1, a3, ae, g3, r3, end, fitRest, spRest, inRest, ready3, sum3, fitG3),
        neq => Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(Equal.trans(Bool, False{}, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), True{}, Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), False{}, after_conflict(grammar, t, index, outer, m, alts, a1, a3, next, neq, seqEqO, itEqP, alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a1, next, isA1, hsA), alt_has(False{}, True{}, grammar, t, index, outer, m, alts, a3, next, isA3, hsA3))), noConf))))
    case Con{Spec.Leaf{+x}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Leaf{x} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Leaf{x} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Node{+q, +ch}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Node{q, ch} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Node{q, ch} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Skip{}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Skip{} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Skip{} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))
    case Con{Spec.Loop{+rr}, +r3}:
      +inner = Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(g, grammar, Spec.altOf(alts, a))), Spec.fits(Spec.Loop{rr} <> r3, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Loop{rr} <> r3), Spec.Brack{Spec.Group{}, alts})), fitR)
      Empty.absurd(AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}])), Lemma.false_is_not_true(inner))

law again_one_positive:
  for b: Bool
  for b2: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +r2: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Positive{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +a1: Nat
  for +isA1: {Nat.is_lt(a1, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +b2Eq: {Nat.is_eq(k, end) == b2 : Bool}
  for +bEq: {Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}) == b : Bool}
  AllOn(grammar, input, root, Support.whenTrue(b, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}}]))

def again_one_positive(b, b2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq):
  match b b2:
    case False{} _:
      {==}
    case True{} True{}:
      +ke = Lemma.nat_eq_sound(k, end, b2Eq)
      %ke : AllOn(grammar, input, root, Support.whenTrue(True{}, [Support.FactDescriptor{Gll.Desc{index, a1 <> (m <> outer), 0n, k, _}}]))
      +bK = Equal.trans(Bool, Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, k}), Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), True{},
        Equal.cong(Nat, Bool, v => Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, v}), k, end, ke), bEq)
      seed_positive(Spec.Loop{rs} <> ts, True{}, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a1, isA1, bK)
    case True{} False{}:
      again_next_positive(r2, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, isA1, b2Eq, bEq)

# ======== ANOTHER ROUND OF A LOOP ON THE TREE ========

law again_alts_closure:
  for n: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +r2: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Closure{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +hn: {Nat.is_lt(n, 1n+List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(n, index, m <> outer, k, end)))

def again_alts_closure(n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, hn):
  match n:
    case 0n:
      {==}
    case 1n+(+a1):
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(a1, index, m <> outer, k, end)), grammar, input, root,
        again_one_closure(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), Nat.is_eq(k, end), grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, hn, {==}, {==}),
        again_alts_closure(a1, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, lt_up(a1, List.length(&2, +List<Spec.Item>, alts), hn)))

law again_alts_positive:
  for n: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +r2: +List<Spec.Tree>
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +fitF: {Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +inF: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +fitR: {Spec.fits(Spec.Pick{a, g} <> r2, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, g} <> r2), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +spR: G.Spells(Spec.Pick{a, g} <> r2, input, p0)
  for +inR: {Spec.allIn(Spec.walk(Spec.Pick{a, g} <> r2, True{}, index, List.append(&2, Nat, prefixOf(outer), [m]), 0n, k, p0), Spec.steps(root, 0n)) == True{} : Bool}
  for +ready: {G.roundsReady(Spec.Positive{}, k, p0, Spec.Pick{a, g} <> r2) == True{} : Bool}
  for +sumEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, g} <> r2))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))) : Nat}
  for +hn: {Nat.is_lt(n, 1n+List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(n, index, m <> outer, k, end)))

def again_alts_positive(n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, hn):
  match n:
    case 0n:
      {==}
    case 1n+(+a1):
      on_append(PS.descWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.alternatives(a1, index, m <> outer, k, end)), grammar, input, root,
        again_one_positive(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, a1 <> (m <> outer), 0n, k, end}), Nat.is_eq(k, end), grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, a1, hn, {==}, {==}),
        again_alts_positive(a1, grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, lt_up(a1, List.length(&2, +List<Spec.Item>, alts), hn)))

# The rounds that may follow a round of a bracket on the tree, ending at end.
law again_kind:
  for kind: Spec.Bracket
  for ff: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +outer: +List<Nat>
  for +m: Nat
  for +kc: Nat
  for +k: Nat
  for +p1: Nat
  for +g1: +List<Spec.Tree>
  for +occO: SeqOcc(outer, grammar, input, root, index, kc, p1, g1)
  for +fitF: {Spec.fits(ff, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))) == True{} : Bool}
  for +spF: G.Spells(ff, input, k)
  for +inF: {Spec.allIn(Spec.walk(ff, False{}, index, prefixOf(outer), m, kc, k), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(k, List.length(&2, Nat, Spec.leaves(ff))) == Nat.add(p1, List.length(&2, Nat, Spec.leaves(g1))) : Nat}
  for +alts: +List<+List<Spec.Item>>
  for +itEqP: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +a: Nat
  for +p0: Nat
  for +g: +List<Spec.Tree>
  for +end: Nat
  for +endEq: {Nat.add(p0, List.length(&2, Nat, Spec.leaves(g))) == end : Nat}
  for +ri: RoundIn(ff, grammar, input, root, index, outer, m, a, k, p0, g, kind, alts)
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(kind), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end)))

def again_kind(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, ri):
  match kind ff:
    case Spec.Group{} _:
      {==}
    case Spec.Optional{} _:
      {==}
    case Spec.Closure{} Con{Spec.Loop{+rs}, +ts}:
      match ri:
        case (r2, (fitR, (spR, (inR, (ready, sumEq))))):
          again_alts_closure(List.length(&2, +List<Spec.Item>, alts), grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, L.lt_succ_self(List.length(&2, +List<Spec.Item>, alts)))
    case Spec.Closure{} Con{Spec.Pick{+a2, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Closure{}, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Closure{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Closure{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(fitF2))
    case Spec.Closure{} Nil{}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Closure{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Closure{} Con{Spec.Leaf{x}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Closure{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Closure{} Con{Spec.Node{q, ch}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Closure{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Closure{} Con{Spec.Skip{}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Closure{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Positive{} Con{Spec.Loop{+rs}, +ts}:
      match ri:
        case (r2, (fitR, (spR, (inR, (ready, sumEq))))):
          again_alts_positive(List.length(&2, +List<Spec.Item>, alts), grammar, start, t, po, noConf, input, root, rootFit, rootSp, r2, index, outer, m, kc, k, p1, g1, occO, rs, ts, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, fitR, spR, inR, ready, sumEq, L.lt_succ_self(List.length(&2, +List<Spec.Item>, alts)))
    case Spec.Positive{} Con{Spec.Pick{+a2, +ch}, +ts}:
      +dEq = N1.nth_drop(Gll.seqAt(grammar, index, outer), m, Spec.Brack{Spec.Positive{}, alts}, itEqP)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer))), Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a2, ch} <> ts, grammar, v), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(m, Gll.seqAt(grammar, index, outer)), Spec.Brack{Spec.Positive{}, alts} <> Gll.dropFrom(1n+m, Gll.seqAt(grammar, index, outer)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Positive{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(fitF2))
    case Spec.Positive{} Nil{}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Positive{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Positive{} Con{Spec.Leaf{x}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Positive{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Positive{} Con{Spec.Node{q, ch}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Positive{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))
    case Spec.Positive{} Con{Spec.Skip{}, ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againPick(Gll.isLoop(Spec.Positive{}), List.length(&2, +List<Spec.Item>, alts), index, m <> outer, k, end))), Lemma.false_is_not_true(ri))

# The rounds that may follow a round that ended on the tree are on it.
law again_on:
  for key: Gll.CKey
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +end: Nat
  for +here: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Check.againOfKey(grammar, key, end)))

def again_on(key, grammar, start, t, po, noConf, input, root, rootFit, rootSp, end, here):
  match key:
    case Gll.CKey{Gll.TNt{x}, k}:
      {==}
    case Gll.CKey{Gll.TBr{index, Nil{}}, k}:
      {==}
    case Gll.CKey{Gll.TBr{+index, Con{+m, +outer}}, +k}:
      match here:
        case (a, (p0, (g, ((kc, (p1, (g1, (ff, (kind, (alts, (occO, ((fitF, (spF, (inF, finF))), (itEqP, (gAt, ri)))))))))), endEq)))):
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itEqP)
          %itS : AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.againOf(_, index, m <> outer, k, end)))
          again_kind(kind, ff, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, outer, m, kc, k, p1, g1, occO, fitF, spF, inF, finF, alts, itEqP, a, p0, g, end, endEq, ri)

# ======== RULES ON THE TREE, AND THE LAW ========

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
  %kp : popOn(grammar, input, root, _, end)
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
  %ke : returnOn(grammar, input, root, _, edge)
  here

law edge_when:
  for same: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +key: Gll.CKey
  for +popKey: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(key, popKey) == same : Bool}
  for +here: returnOn(grammar, input, root, key, edge)
  for +pop: popOn(grammar, input, root, popKey, end)
  AllOn(grammar, input, root, Support.whenTrue(same, PS.resumeGives(Gll.Predict{t}, grammar, input, key, edge, end)))

def edge_when(same, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, popKey, edge, end, sameEq, here, pop):
  match same:
    case True{}:
      +pk = G.key_eq_sound(key, popKey, sameEq)
      resume_on(key, edge, grammar, start, t, po, noConf, input, root, rootFit, rootSp, end, here, pop_moved(grammar, input, root, key, popKey, end, pk, pop))
    case False{}:
      {==}

# A return edge against the pops reached.
law edge_on:
  for reached: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +here: returnOn(grammar, input, root, key, edge)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.edgeGives(Gll.Predict{t}, grammar, input, reached, key, edge))

def edge_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactPop{+popKey, +end}, +rest}:
      match all:
        case (h0, t0):
          +h = {h0 : popOn(grammar, input, root, popKey, end)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(Support.whenTrue(Gll.keyEq(key, popKey), PS.resumeGives(Gll.Predict{t}, grammar, input, key, edge, end)), PS.edgeGives(Gll.Predict{t}, grammar, input, rest, key, edge), grammar, input, root,
            edge_when(Gll.keyEq(key, popKey), grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, popKey, edge, end, {==}, here, h),
            edge_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, tl))
    case Con{Support.FactDescriptor{+x}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          edge_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, tl)
    case Con{Support.FactCluster{+x}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          edge_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, tl)
    case Con{Support.FactReturn{+k2, +e2}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          edge_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, tl)
    case Con{Support.FactStep{+y}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          edge_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, tl)

law pop_when:
  for same: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +edgeKey: Gll.CKey
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +end: Nat
  for +sameEq: {Gll.keyEq(edgeKey, key) == same : Bool}
  for +ret: returnOn(grammar, input, root, edgeKey, edge)
  for +pop: popOn(grammar, input, root, key, end)
  AllOn(grammar, input, root, Support.whenTrue(same, PS.resumeGives(Gll.Predict{t}, grammar, input, edgeKey, edge, end)))

def pop_when(same, grammar, start, t, po, noConf, input, root, rootFit, rootSp, edgeKey, key, edge, end, sameEq, ret, pop):
  match same:
    case True{}:
      +ek = G.key_eq_sound(edgeKey, key, sameEq)
      resume_on(edgeKey, edge, grammar, start, t, po, noConf, input, root, rootFit, rootSp, end, ret, pop_moved(grammar, input, root, edgeKey, key, end, ek, pop))
    case False{}:
      {==}

# A pop against the return edges reached.
law pop_on:
  for reached: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +key: Gll.CKey
  for +end: Nat
  for +pop: popOn(grammar, input, root, key, end)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.popGives(Gll.Predict{t}, grammar, input, reached, key, end))

def pop_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, all):
  match reached:
    case Nil{}:
      {==}
    case Con{Support.FactReturn{+edgeKey, +edge}, +rest}:
      match all:
        case (h0, t0):
          +h = {h0 : returnOn(grammar, input, root, edgeKey, edge)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(Support.whenTrue(Gll.keyEq(edgeKey, key), PS.resumeGives(Gll.Predict{t}, grammar, input, edgeKey, edge, end)), PS.popGives(Gll.Predict{t}, grammar, input, rest, key, end), grammar, input, root,
            pop_when(Gll.keyEq(edgeKey, key), grammar, start, t, po, noConf, input, root, rootFit, rootSp, edgeKey, key, edge, end, {==}, h, pop),
            pop_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, tl))
    case Con{Support.FactDescriptor{+x}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          pop_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, tl)
    case Con{Support.FactCluster{+x}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          pop_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, tl)
    case Con{Support.FactPop{+k2, +j2}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          pop_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, tl)
    case Con{Support.FactStep{+y}, +rest}:
      match all:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          pop_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, pop, tl)

# What a fact on the tree gives, with facts reached that are all on it, is on it.
law fact_on:
  for fact: Support.Fact
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +reached: +List<Support.Fact>
  for +here: On(grammar, input, root, fact)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.factGives(fact, Gll.Predict{t}, grammar, input, reached))

def fact_on(fact, grammar, start, t, po, noConf, input, root, rootFit, rootSp, reached, here, all):
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, +rpath, +dot, +k, +i}}:
      match here:
        case (p0, (g, (f, (occ, (fitF, (spF, (inF, finF))))))):
          item_on(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, rpath, dot, k, i, p0, g, occ, fitF, spF, inF, finF, {==})
    case Support.FactCluster{Gll.CKey{Gll.TNt{+x}, +i}}:
      match here:
        case (q, (g, (lhsQ, node))):
          seeds_on(grammar, 0n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, {==})
    case Support.FactCluster{Gll.CKey{Gll.TBr{+index, +rpath}, +i}}:
      bracket_seeds_on(rpath, grammar, start, t, po, noConf, input, root, rootFit, rootSp, index, i, here)
    case Support.FactReturn{+key, +edge}:
      edge_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, all)
    case Support.FactPop{+key, +end}:
      on_append(PS.popGives(Gll.Predict{t}, grammar, input, reached, key, end), PS.descsWhen(Gll.Predict{t}, grammar, input, Check.againOfKey(grammar, key, end)), grammar, input, root,
        pop_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, here, all), again_on(key, grammar, start, t, po, noConf, input, root, rootFit, rootSp, end, here))
    case Support.FactStep{+y}:
      {==}

# ======== GROWING THE FACTS REACHED KEEPS THEM ON THE TREE ========

law all_give_on:
  for facts: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +reached: +List<Support.Fact>
  for +here: AllOn(grammar, input, root, facts)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.allGive(facts, Gll.Predict{t}, grammar, input, reached))

def all_give_on(facts, grammar, start, t, po, noConf, input, root, rootFit, rootSp, reached, here, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      match here:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, fact)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(PS.factGives(fact, Gll.Predict{t}, grammar, input, reached), PS.allGive(rest, Gll.Predict{t}, grammar, input, reached), grammar, input, root,
            fact_on(fact, grammar, start, t, po, noConf, input, root, rootFit, rootSp, reached, h, all),
            all_give_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, reached, tl, all))

law grow_on:
  for n: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.grow(n, Gll.Predict{t}, grammar, input, s, reached))

def grow_on(n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, s, reached, all):
  match n:
    case 0n:
      all
    case 1n+(+m):
      +next = PS.round(Gll.Predict{t}, grammar, input, s, reached)
      grow_on(m, grammar, start, t, po, noConf, input, root, rootFit, rootSp, s, next,
        on_add(PS.allGive(reached, Gll.Predict{t}, grammar, input, reached), s, reached, grammar, input, root, all_give_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, reached, all, all), all))

# The roots are on the tree.
law roots_on:
  for tree: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root0: Spec.Tree
  for +rootFitX: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSpX: {Spec.leaves([tree]) == input : +List<Nat>}
  AllOn(grammar, input, tree, PS.roots(Gll.Predict{t}, grammar, input, start))

def roots_on(tree, grammar, start, t, po, noConf, input, root0, rootFitX, rootSpX):
  match tree:
    case Spec.Node{+q, +ch}:
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, rootFitX)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +node = {(fitCh, (G.root_spells(input, q, ch, rootSpX), U.all_in_refl(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)))) : N1.NodeAt(grammar, input, Spec.Node{q, ch}, q, 0n, ch)}
      ((q, (ch, (lhsQ, node))), seeds_on(grammar, 0n, grammar, start, t, po, noConf, input, Spec.Node{q, ch}, rootFitX, rootSpX, start, 0n, q, ch, lhsQ, node, {==}))
    case Spec.Leaf{kind}:
      Empty.absurd(AllOn(grammar, input, Spec.Leaf{kind}, PS.roots(Gll.Predict{t}, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Pick{a, ch}:
      Empty.absurd(AllOn(grammar, input, Spec.Pick{a, ch}, PS.roots(Gll.Predict{t}, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Skip{}:
      Empty.absurd(AllOn(grammar, input, Spec.Skip{}, PS.roots(Gll.Predict{t}, grammar, input, start)), Lemma.false_is_not_true(rootFitX))
    case Spec.Loop{rs}:
      Empty.absurd(AllOn(grammar, input, Spec.Loop{rs}, PS.roots(Gll.Predict{t}, grammar, input, start)), Lemma.false_is_not_true(rootFitX))

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
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +s: Gll.GState
  for +sup: {PS.supportedWith(Gll.Predict{t}, grammar, start, input, s) == True{} : Bool}
  AllOn(grammar, input, root, Support.factsOf(s))

def supported_on(grammar, start, t, po, noConf, input, root, rootFit, rootSp, s, sup):
  +facts = Support.factsOf(s)
  +first = Support.addWithin(PS.roots(Gll.Predict{t}, grammar, input, start), s, [])
  +reached = PS.grow(List.length(&2, Support.Fact, facts), Gll.Predict{t}, grammar, input, s, first)
  reached_on(facts, reached, grammar, input, root, sup,
    grow_on(List.length(&2, Support.Fact, facts), grammar, start, t, po, noConf, input, root, rootFit, rootSp, s, first,
      on_add(PS.roots(Gll.Predict{t}, grammar, input, start), s, [], grammar, input, root, roots_on(root, grammar, start, t, po, noConf, input, root, rootFit, rootSp), {==})))

# ======== THE STEPS OF A STATE ON THE TREE ========

law on_right:
  for xs: +List<Support.Fact>
  for +ys: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, List.append(&2, Support.Fact, xs, ys))
  AllOn(grammar, input, root, ys)

def on_right(xs, ys, grammar, input, root, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      match h:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, List.append(&2, Support.Fact, rest, ys))}
          on_right(rest, ys, grammar, input, root, tl)

law steps_on:
  for ys: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, Support.stepFacts(ys))
  for +m: {Spec.bsrMember(y, ys) == True{} : Bool}
  {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}

def steps_on(ys, y, grammar, input, root, h, m):
  match ys:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+z, +rest}:
      match h:
        case (h0, t0):
          +hz = {h0 : {Spec.bsrMember(z, Spec.steps(root, 0n)) == True{} : Bool}}
          +tl = {t0 : AllOn(grammar, input, root, Support.stepFacts(rest))}
          L.either_case({y == z : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}, {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}, G.ebnf_member_cases(y, z, rest, m),
            same => Equal.trans(Bool, Spec.bsrMember(y, Spec.steps(root, 0n)), Spec.bsrMember(z, Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), y, z, same), hz),
            later => steps_on(rest, y, grammar, input, root, tl, later))

law state_steps_on:
  for s: Gll.GState
  for +y: Spec.Bsr
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, Support.factsOf(s))
  for +m: {Spec.bsrMember(y, Check.stepsOf(s)) == True{} : Bool}
  {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}

def state_steps_on(s, y, grammar, input, root, h, m):
  match s:
    case Gll.GState{+seen, todo, +cs, +rs, +ps, +ys}:
      +f1 = Support.descriptorFacts(seen)
      +f2 = Support.clusterFacts(cs)
      +f3 = Support.returnFacts(rs)
      +f4 = Support.popFacts(ps)
      +f5 = Support.stepFacts(ys)
      +h2 = on_right(f1, List.append(&2, Support.Fact, f2, List.append(&2, Support.Fact, f3, List.append(&2, Support.Fact, f4, f5))), grammar, input, root, h)
      +h3 = on_right(f2, List.append(&2, Support.Fact, f3, List.append(&2, Support.Fact, f4, f5)), grammar, input, root, h2)
      +h4 = on_right(f3, List.append(&2, Support.Fact, f4, f5), grammar, input, root, h3)
      +h5 = on_right(f4, f5, grammar, input, root, h4)
      steps_on(ys, y, grammar, input, root, h5, m)

# ======== THE LAW ========

law state_exact:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for facts: {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}
  Spec.IsExactBsr(grammar, start, input, set)

def state_exact(grammar, start, t, ll1, input, tree, fit, sp, s, set, facts):
  match facts:
    case (ok0, same0):
      +ok = {ok0 : {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool}}
      +same = {same0 : {Check.stepsOf(s) == set : +List<Spec.Bsr>}}
      +closedRoot = Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s))
      +cr = Lemma.and_true_left(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +sup = Lemma.and_true_right_side(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +po = Lemma.and_true_left(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +noConf = Lemma.and_true_right_side(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +onTree = supported_on(grammar, start, t, po, noConf, input, tree, fit, sp, s, sup)
      (+element => +m =>
        (tree, (fit, (sp, state_steps_on(s, element, grammar, input, tree, onTree,
          Equal.trans(Bool, Spec.bsrMember(element, Check.stepsOf(s)), Spec.bsrMember(element, set), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.bsrMember(element, v), Check.stepsOf(s), set, same), m))))),
       G.state_done(Gll.Predict{t}, grammar, start, input, s, set, po, (cr, same)))

law run_exact:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +set: +List<Spec.Bsr>
  for got: {PS.runLL(r, Gll.Predict{t}, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def run_exact(r, grammar, start, t, ll1, input, tree, fit, sp, set, got):
  match r:
    case Gll.GDone{+s}:
      +ok = Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s))
      state_exact(grammar, start, t, ll1, input, tree, fit, sp, s, set, G.check_pick(ok, s, set, got))
    case Gll.OutOfFuel{s}:
      Empty.absurd(Spec.IsExactBsr(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# NO DEAD WOOD: an LL(1) grammar (by the checked tables) gives the checked LL(1) parser
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

# The law ll1_no_dead_wood.
def Laws.ll1_no_dead_wood(fuel, grammar, start, input, set, t, tablesEq, ll1, tree, fit, sp, got):
  ll1_no_dead_wood(fuel, grammar, start, input, set, t, tablesEq, ll1, tree, fit, sp, got)
