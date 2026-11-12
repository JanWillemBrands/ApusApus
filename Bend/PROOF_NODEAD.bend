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

# NO DEAD WOOD FOR AN LL(1) GRAMMAR WITHOUT BRACKETS. Fix a parse tree T of the input. Every
# fact the predicting engine's rules can give, from the root, is on T: a descriptor is at a
# node of T, with the forest for the rest of its production; a cluster has a node of its
# nonterminal at its position; a pop is where such a node ends; a return edge comes from a
# descriptor on T; a step is a step of T. Only T's own production gets past prediction (else
# the table check would have found a conflict), and two nodes of one nonterminal at one
# position are the same (else there would be a clash). So a supported state's steps are
# steps of T. PROOF_NODEAD2.bend builds on this for grammars with brackets, and proves the
# law ll1_no_dead_wood; ll1_no_dead_wood_bnf here is its first stage.

# ======== FACTS ON THE TREE ========

def And(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def No() -> Data:
  {False{} == True{} : Bool}

# A node of the tree: production q at k, with children G.
def NodeAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +q: Nat, +k: Nat, +g: +List<Spec.Tree>) -> Data:
  And({Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}, And(G.Spells(g, input, k), {Spec.allIn(Spec.walk(g, False{}, q, [], 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}))

# A node of nonterminal x at k.
def NtAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +x: Nat, +k: Nat) -> Data:
  Sigma<&2, &2, Nat, q => Sigma<&2, &2, +List<Spec.Tree>, g => And({Spec.lhsIs(grammar, q, x) == True{} : Bool}, NodeAt(grammar, input, root, q, k, g))>>

# A node of x at k that ends at j.
def NtEnds(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +x: Nat, +k: Nat, +j: Nat) -> Data:
  Sigma<&2, &2, Nat, q => Sigma<&2, &2, +List<Spec.Tree>, g => And({Spec.lhsIs(grammar, q, x) == True{} : Bool}, And(NodeAt(grammar, input, root, q, k, g), {Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) == j : Nat}))>>

# The rest of a node's children, after dot of them, at i.
def RestAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +dot: Nat, +k: Nat, +i: Nat, +g: +List<Spec.Tree>, +f: +List<Spec.Tree>) -> Data:
  And({Spec.fits(f, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))) == True{} : Bool}, And(G.Spells(f, input, i),
    And({Spec.allIn(Spec.walk(f, False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}, {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) : Nat})))

# A descriptor of production index, started at k, at the slot after dot items, at i.
def DescAt(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +dot: Nat, +k: Nat, +i: Nat) -> Data:
  Sigma<&2, &2, Nat, x => Sigma<&2, &2, +List<Spec.Tree>, g => Sigma<&2, &2, +List<Spec.Tree>, f =>
    And({Spec.lhsIs(grammar, index, x) == True{} : Bool}, And(NodeAt(grammar, input, root, index, k, g), RestAt(grammar, input, root, index, dot, k, i, g, f)))>>>

def descPath(rpath: +List<Nat>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, +index: Nat, +dot: Nat, +k: Nat, +i: Nat) -> Data:
  match rpath:
    case Nil{}:
      DescAt(grammar, input, root, index, dot, k, i)
    case Con{a, rest}:
      No()

def descOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, d: Gll.Desc) -> Data:
  match d:
    case Gll.Desc{+index, rpath, +dot, +k, +i}:
      descPath(rpath, grammar, input, root, index, dot, k, i)

def clusterOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey) -> Data:
  match key:
    case Gll.CKey{Gll.TNt{+x}, +i}:
      NtAt(grammar, input, root, x, i)
    case Gll.CKey{Gll.TBr{index, rpath}, i}:
      No()

def returnOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey, edge: Gll.Edge) -> Data:
  match key edge:
    case Gll.CKey{Gll.TNt{+x}, +i} Gll.Edge{+index, rpath, +dot, +k}:
      And(descPath(rpath, grammar, input, root, index, dot, k, i), {Gll.nthItem(Spec.rhsOf(grammar, index), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>})
    case Gll.CKey{Gll.TBr{index, rpath}, i} e:
      No()

def popOn(+grammar: +List<Spec.Production>, +input: +List<Nat>, +root: Spec.Tree, key: Gll.CKey, +j: Nat) -> Data:
  match key:
    case Gll.CKey{Gll.TNt{+x}, +k}:
      NtEnds(grammar, input, root, x, k, j)
    case Gll.CKey{Gll.TBr{index, rpath}, k}:
      No()

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
      And(On(grammar, input, root, fact), AllOn(grammar, input, root, rest))

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

# ======== THE TABLE CHECK RULES OUT CLASHES ========

law clash_empty:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for c: U.Clash(grammar, start)
  Empty

def clash_empty(grammar, start, t, po, noConf, c):
  match c:
    case (point, (first, (second, (next, (neq, (cp1, cp2)))))):
      +none = List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t))
      Lemma.false_is_not_true(Equal.trans(Bool, False{}, none, True{}, Equal.sym(Bool, none, False{}, L.ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2)), noConf))

law same_or_clash:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for -g1: +List<Spec.Tree>
  for -g2: +List<Spec.Tree>
  for r: U.Same(grammar, start, g1, g2)
  {g1 == g2 : +List<Spec.Tree>}

def same_or_clash(grammar, start, t, po, noConf, g1, g2, r):
  match r:
    case Inl{e}:
      e
    case Inr{c}:
      Empty.absurd({g1 == g2 : +List<Spec.Tree>}, clash_empty(grammar, start, t, po, noConf, c))

# ======== TWO NODES OF ONE NONTERMINAL AT ONE POSITION ARE THE SAME ========

law nodes_same_eq:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {First.tablesClosed(grammar, start, t) == True{} : Bool}
  for +noConf: {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == True{} : Bool}
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +k: Nat
  for +q1: Nat
  for +q2: Nat
  for +qe: {q1 == q2 : Nat}
  for +g1: +List<Spec.Tree>
  for +g2: +List<Spec.Tree>
  for +n1: NodeAt(grammar, input, root, q1, k, g1)
  for +n2: NodeAt(grammar, input, root, q2, k, g2)
  {g1 == g2 : +List<Spec.Tree>}

def nodes_same_eq(grammar, start, t, po, noConf, input, root, rootFit, rootSp, k, q1, q2, qe, g1, g2, n1, n2):
  match n1:
    case (fit10, (sp10, in10)):
      match n2:
        case (fit20, (sp20, in20)):
          +fit1 = {fit10 : {Spec.fits(g1, grammar, Spec.rhsOf(grammar, q1)) == True{} : Bool}}
          +sp1 = {sp10 : G.Spells(g1, input, k)}
          +in1 = {in10 : {Spec.allIn(Spec.walk(g1, False{}, q1, [], 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fit2 = {fit20 : {Spec.fits(g2, grammar, Spec.rhsOf(grammar, q2)) == True{} : Bool}}
          +sp2 = {sp20 : G.Spells(g2, input, k)}
          +in2 = {in20 : {Spec.allIn(Spec.walk(g2, False{}, q2, [], 0n, k, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fit2b = Equal.trans(Bool, Spec.fits(g2, grammar, Spec.rhsOf(grammar, q1)), Spec.fits(g2, grammar, Spec.rhsOf(grammar, q2)), True{}, Equal.cong(Nat, Bool, v => Spec.fits(g2, grammar, Spec.rhsOf(grammar, v)), q1, q2, qe), fit2)
          +in2b = Equal.trans(Bool, Spec.allIn(Spec.walk(g2, False{}, q1, [], 0n, k, k), Spec.steps(root, 0n)), Spec.allIn(Spec.walk(g2, False{}, q2, [], 0n, k, k), Spec.steps(root, 0n)), True{},
            Equal.cong(Nat, Bool, v => Spec.allIn(Spec.walk(g2, False{}, v, [], 0n, k, k), Spec.steps(root, 0n)), q1, q2, qe), in2)
          same_or_clash(grammar, start, t, po, noConf, g1, g2,
            U.compare(g1, False{}, g2, Spec.rhsOf(grammar, q1), grammar, start, input, root, rootFit, rootSp, root, rootFit, rootSp, q1, [], 0n, k, k, k, Spec.Group{}, [], [], False{}, 0n, 0n,
              (fit1, (fit2b, (sp1, (sp2, (in1, (in2b, ({==}, {==})))))))))

# PREDICT of a node's production, at its position.
law node_predicts:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +k: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +node: NodeAt(grammar, input, root, q, k, g)
  Spec.Predicts(grammar, start, Spec.rhsOf(grammar, q), q, [], List.get(&2, Nat, input, k))

def node_predicts(grammar, start, input, root, rootFit, rootSp, k, q, g, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +e = Nat.add(k, List.length(&2, Nat, Spec.leaves(g)))
      U.predicts_in(List.get(&2, Nat, input, k), grammar, start, input, root, rootFit, rootSp, g, Spec.rhsOf(grammar, q), q, [], [], k, k, e, Spec.walk(g, False{}, q, [], 0n, k, k), fit, sp0, {==}, {==}, {==},
        U.end_walk(g, Spec.rhsOf(grammar, q), 0n, grammar, q, [], k, k, e, fit, {==}, {==}, {==}), in0)

law nodes_same:
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
  for +k: Nat
  for +q1: Nat
  for +q2: Nat
  for +g1: +List<Spec.Tree>
  for +g2: +List<Spec.Tree>
  for +lhs1: {Spec.lhsIs(grammar, q1, x) == True{} : Bool}
  for +lhs2: {Spec.lhsIs(grammar, q2, x) == True{} : Bool}
  for +n1: NodeAt(grammar, input, root, q1, k, g1)
  for +n2: NodeAt(grammar, input, root, q2, k, g2)
  And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>})

def nodes_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, k, q1, q2, g1, g2, lhs1, lhs2, n1, n2):
  +next = List.get(&2, Nat, input, k)
  cp1 = U.nt_cp(Spec.lhsIs(grammar, q1, x), grammar, start, q1, next, lhs1, node_predicts(grammar, start, input, root, rootFit, rootSp, k, q1, g1, n1))
  cp2 = U.nt_cp(Spec.lhsIs(grammar, q2, x), grammar, start, q2, next, lhs2, node_predicts(grammar, start, input, root, rootFit, rootSp, k, q2, g2, n2))
  L.either_case({q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}, And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>}), U.decide(Nat.is_eq(q1, q2), q1, q2, {==}),
    +qe => (qe, nodes_same_eq(grammar, start, t, po, noConf, input, root, rootFit, rootSp, k, q1, q2, qe, g1, g2, n1, n2)),
    neq => Empty.absurd(And({q1 == q2 : Nat}, {g1 == g2 : +List<Spec.Tree>}), clash_empty(grammar, start, t, po, noConf, (Spec.NonterminalAt{x}, (q1, (q2, (next, (neq, (cp1, cp2)))))))))

# ======== SEQUENCES OF A GRAMMAR WITHOUT BRACKETS ========

def itemOr(m: Maybe<&2, Spec.Item>, +d: Spec.Item) -> Spec.Item:
  match m:
    case Some{x}:
      x
    case None{}:
      d

law nth_drop:
  for seq: +List<Spec.Item>
  for n: Nat
  for +y: Spec.Item
  for +e: {Gll.nthItem(seq, n) == Some{y} : Maybe<&2, Spec.Item>}
  {Gll.dropFrom(n, seq) == y <> Gll.dropFrom(1n+n, seq) : +List<Spec.Item>}

def nth_drop(seq, n, y, e):
  match seq n:
    case Nil{} _:
      Empty.absurd({Gll.dropFrom(n, []) == y <> Gll.dropFrom(1n+n, []) : +List<Spec.Item>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{y}, e)))
    case Con{+x, +rest} 0n:
      Equal.cong(Spec.Item, +List<Spec.Item>, v => v <> rest, x, y, Equal.cong(Maybe<&2, Spec.Item>, Spec.Item, v => itemOr(v, x), Some{x}, Some{y}, e))
    case Con{x, +rest} 1n+(+m):
      nth_drop(rest, m, y, e)

law nth_none_drop:
  for seq: +List<Spec.Item>
  for n: Nat
  for +e: {Gll.nthItem(seq, n) == None{} : Maybe<&2, Spec.Item>}
  {Gll.dropFrom(n, seq) == [] : +List<Spec.Item>}

def nth_none_drop(seq, n, e):
  match seq n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      {==}
    case Con{+x, +rest} 0n:
      Empty.absurd({x <> rest == [] : +List<Spec.Item>}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), Some{x}, None{}, e)))
    case Con{x, +rest} 1n+(+m):
      nth_none_drop(rest, m, e)

def isBrackOf(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{Spec.Brack{kd, alts}}:
      True{}
    case _:
      False{}

law plain_items:
  for items: +List<Spec.Item>
  for n: Nat
  for +kd: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +plain: {PS.itemsPlain(items) == True{} : Bool}
  for +e: {Gll.nthItem(items, n) == Some{Spec.Brack{kd, alts}} : Maybe<&2, Spec.Item>}
  Empty

def plain_items(items, n, kd, alts, plain, e):
  match items n:
    case Nil{} _:
      Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Brack{k2, a2}, rest} _:
      Lemma.false_is_not_true(plain)
    case Con{Spec.Sym{+s}, +rest} 0n:
      Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackOf(v), Some{Spec.Sym{s}}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Sym{s}, +rest} 1n+(+m):
      plain_items(rest, m, kd, alts, plain, e)
    case Con{Spec.Eps{}, +rest} 0n:
      Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackOf(v), Some{Spec.Eps{}}, Some{Spec.Brack{kd, alts}}, e))
    case Con{Spec.Eps{}, +rest} 1n+(+m):
      plain_items(rest, m, kd, alts, plain, e)

law plain_rhs:
  for grammar: +List<Spec.Production>
  for index: Nat
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  {PS.itemsPlain(Spec.rhsOf(grammar, index)) == True{} : Bool}

def plain_rhs(grammar, index, plain):
  match grammar index:
    case Nil{} _:
      {==}
    case Con{Spec.Production{lhs, +rhs}, +rest} 0n:
      Lemma.and_true_left(PS.itemsPlain(rhs), PS.withoutBrackets(rest), plain)
    case Con{Spec.Production{lhs, +rhs}, +rest} 1n+(+m):
      plain_rhs(rest, m, Lemma.and_true_right_side(PS.itemsPlain(rhs), PS.withoutBrackets(rest), plain))

law all_in_tail_n:
  for +x: Spec.Bsr
  for +xs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(x <> xs, set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_tail_n(x, xs, set, h):
  U.all_in_tail(x, xs, set, h)

law all_in_left_n:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def all_in_left_n(xs, ys, set, h):
  U.all_in_left(xs, ys, set, h)

law all_in_right_n:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(ys, set) == True{} : Bool}

def all_in_right_n(xs, ys, set, h):
  U.all_in_right(xs, ys, set, h)

# ======== WHAT A DESCRIPTOR ON THE TREE GIVES ========

law empty_on:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +index: Nat
  for +k: Nat
  for +i: Nat
  for +inF: {Spec.allIn(Spec.walk([], False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  AllOn(grammar, input, root, Support.emptyStep(dot, index, [], k, i))

def empty_on(dot, grammar, input, root, index, k, i, inF):
  match dot:
    case 0n:
      (Lemma.and_true_left(Spec.bsrMember(Spec.at(index, [], 0n, k, i, i), Spec.steps(root, 0n)), True{}, inF), {==})
    case 1n+d:
      {==}

law item_on:
  for it: Maybe<&2, Spec.Item>
  for f: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +pr: Gll.Pred
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +i: Nat
  for +x: Nat
  for +g: +List<Spec.Tree>
  for +lhs: {Spec.lhsIs(grammar, index, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, index, k, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +itEq: {Gll.nthItem(Spec.rhsOf(grammar, index), dot) == it : Maybe<&2, Spec.Item>}
  AllOn(grammar, input, root, PS.itemGives(it, pr, grammar, input, index, [], dot, k, i))

def item_on(it, f, grammar, input, root, pr, plain, index, dot, k, i, x, g, lhs, node, fitF, spF, inF, finF, itEq):
  match it f:
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Nil{}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits([], grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      +fitT = Fits.fits_tail(Spec.Leaf{a}, ts, grammar, Spec.Sym{Spec.Terminal{tm}}, Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), fitF2)
      +lts = List.length(&2, Nat, Spec.leaves(ts))
      +spT = G.leaf_rest(input, i, a, Spec.leaves(ts), spF)
      +here = Spec.at(index, [], 1n+dot, k, i, 1n+i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, 1n+i)
      +inT = all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      +finT = Equal.trans(Nat, 1n+Nat.add(i, lts), Nat.add(i, 1n+lts), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Equal.sym(Nat, Nat.add(i, 1n+lts), 1n+Nat.add(i, lts), Lemma.add_succ_right(i, lts)), finF)
      on_when(Gll.tokenIs(List.get(&2, Nat, input, i), tm), PS.pairWhen(pr, grammar, input, Gll.Desc{index, [], 1n+dot, k, 1n+i}, Gll.stepAt(index, [], 1n+dot, k, i, 1n+i)), grammar, input, root,
        on_when(Gll.admits(pr, grammar, input, Gll.Desc{index, [], 1n+dot, k, 1n+i}), [Support.FactDescriptor{Gll.Desc{index, [], 1n+dot, k, 1n+i}}, Support.FactStep{Gll.stepAt(index, [], 1n+dot, k, i, 1n+i)}], grammar, input, root, ((x, (g, (ts, (lhs, (node, (fitT, (spT, (inT, finT)))))))), (onS, {==}))))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Skip{}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Terminal{+tm}}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Terminal{tm}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Terminal{tm}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Terminal{tm}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Nil{}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits([], grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), fitF2)
      +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +lch = Spec.leaves(ch)
      +e = Nat.add(i, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, i, lch, Spec.leaves(ts), spF)
      +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, e)
      +inCh = all_in_left_n(wCh, wT, Spec.steps(root, 0n), all_in_tail_n(Spec.at(index, [], 1n+dot, k, i, e), List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF))
      ((q, (ch, (lhsQ, (fitCh, (spCh, inCh))))), (((x, (g, (Spec.Node{q, ch} <> ts, (lhs, (node, (fitF, (spF, (inF, finF)))))))), itEq), {==}))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Skip{}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Sym{Spec.Nonterminal{+y}}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Sym{Spec.Nonterminal{y}}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Nil{}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits([], grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Leaf{+a}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Node{+q, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Eps{}} Con{Spec.Skip{}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      +here = Spec.at(index, [], 1n+dot, k, i, i)
      +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, i)
      +inT = all_in_tail_n(here, wT, Spec.steps(root, 0n), inF)
      +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(wT, Spec.steps(root, 0n)), inF)
      on_when(Gll.admits(pr, grammar, input, Gll.Desc{index, [], 1n+dot, k, i}), [Support.FactDescriptor{Gll.Desc{index, [], 1n+dot, k, i}}, Support.FactStep{Gll.stepAt(index, [], 1n+dot, k, i, i)}], grammar, input, root, ((x, (g, (ts, (lhs, (node, (fitF2, (spF, (inT, finF)))))))), (onS, {==})))
    case Some{Spec.Eps{}} Con{Spec.Loop{+rs}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Eps{}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Eps{} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Eps{}}, pr, grammar, input, index, [], dot, k, i)), Lemma.false_is_not_true(fitF2))
    case Some{Spec.Brack{+kd, +alts}} Nil{}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case Some{Spec.Brack{+kd, +alts}} Con{Spec.Leaf{+a}, +ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case Some{Spec.Brack{+kd, +alts}} Con{Spec.Node{+q, +ch}, +ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case Some{Spec.Brack{+kd, +alts}} Con{Spec.Pick{+a, +ch}, +ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case Some{Spec.Brack{+kd, +alts}} Con{Spec.Skip{}, +ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case Some{Spec.Brack{+kd, +alts}} Con{Spec.Loop{+rs}, +ts}:
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(Some{Spec.Brack{kd, alts}}, pr, grammar, input, index, [], dot, k, i)), plain_items(Spec.rhsOf(grammar, index), dot, kd, alts, plain_rhs(grammar, index, plain), itEq))
    case None{} Nil{}:
      +lhsIdx = Equal.trans(Bool, Spec.lhsIs(grammar, index, Gll.lhsOf(grammar, index)), Spec.lhsIs(grammar, index, x), True{}, Equal.cong(Nat, Bool, v => Spec.lhsIs(grammar, index, v), Gll.lhsOf(grammar, index), x, G.lhs_of_is(grammar, index, x, lhs)), lhs)
      +endEq = Equal.trans(Nat, Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), Nat.add(i, 0n), i, Equal.sym(Nat, Nat.add(i, 0n), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), finF), Lemma.add_zero_right(i))
      ((index, (g, (lhsIdx, (node, endEq)))), empty_on(dot, grammar, input, root, index, k, i, inF))
    case None{} Con{Spec.Leaf{+a}, +ts}:
      +dNil = nth_none_drop(Spec.rhsOf(grammar, index), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, pr, grammar, input, index, [], dot, k, i)), Fits.fits_cons_nil(Spec.Leaf{a}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, []), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), [], Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), [], dNil)), fitF)))
    case None{} Con{Spec.Node{+q, +ch}, +ts}:
      +dNil = nth_none_drop(Spec.rhsOf(grammar, index), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, pr, grammar, input, index, [], dot, k, i)), Fits.fits_cons_nil(Spec.Node{q, ch}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, []), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), [], Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), [], dNil)), fitF)))
    case None{} Con{Spec.Pick{+a, +ch}, +ts}:
      +dNil = nth_none_drop(Spec.rhsOf(grammar, index), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, pr, grammar, input, index, [], dot, k, i)), Fits.fits_cons_nil(Spec.Pick{a, ch}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, []), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), [], Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), [], dNil)), fitF)))
    case None{} Con{Spec.Skip{}, +ts}:
      +dNil = nth_none_drop(Spec.rhsOf(grammar, index), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, pr, grammar, input, index, [], dot, k, i)), Fits.fits_cons_nil(Spec.Skip{}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, []), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), [], Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), [], dNil)), fitF)))
    case None{} Con{Spec.Loop{+rs}, +ts}:
      +dNil = nth_none_drop(Spec.rhsOf(grammar, index), dot, itEq)
      Empty.absurd(AllOn(grammar, input, root, PS.itemGives(None{}, pr, grammar, input, index, [], dot, k, i)), Fits.fits_cons_nil(Spec.Loop{rs}, ts, grammar, Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, []), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), [], Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), [], dNil)), fitF)))

# ======== A CLUSTER ON THE TREE STARTS ONLY THE TREE'S PRODUCTION ========

def dropProds(n: Nat, grammar: +List<Spec.Production>) -> +List<Spec.Production>:
  match n grammar:
    case 0n _:
      grammar
    case 1n+m Nil{}:
      []
    case 1n+m Con{p, rest}:
      dropProds(m, rest)

def lhsHead(ps: +List<Spec.Production>) -> Nat:
  match ps:
    case Con{Spec.Production{lhs, rhs}, rest}:
      lhs
    case Nil{}:
      0n

def prodsTail(ps: +List<Spec.Production>) -> +List<Spec.Production>:
  match ps:
    case Con{p, rest}:
      rest
    case Nil{}:
      []

def prodsEmpty(ps: +List<Spec.Production>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      False{}

law drop_lhs:
  for grammar: +List<Spec.Production>
  for n: Nat
  for +lhs: Nat
  for +rhs: +List<Spec.Item>
  for +rest: +List<Spec.Production>
  for +y: Nat
  for +e: {dropProds(n, grammar) == Spec.Production{lhs, rhs} <> rest : +List<Spec.Production>}
  {Spec.lhsIs(grammar, n, y) == Nat.is_eq(lhs, y) : Bool}

def drop_lhs(grammar, n, lhs, rhs, rest, y, e):
  match grammar n:
    case Nil{} 0n:
      Empty.absurd({False{} == Nat.is_eq(lhs, y) : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], Spec.Production{lhs, rhs} <> rest, e)))
    case Nil{} 1n+m:
      Empty.absurd({False{} == Nat.is_eq(lhs, y) : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], Spec.Production{lhs, rhs} <> rest, e)))
    case Con{Spec.Production{+l2, +r2}, +rest2} 0n:
      Equal.cong(Nat, Bool, v => Nat.is_eq(v, y), l2, lhs, Equal.cong(+List<Spec.Production>, Nat, v => lhsHead(v), Spec.Production{l2, r2} <> rest2, Spec.Production{lhs, rhs} <> rest, e))
    case Con{p, +rest2} 1n+(+m):
      drop_lhs(rest2, m, lhs, rhs, rest, y, e)

law drop_next:
  for grammar: +List<Spec.Production>
  for n: Nat
  for +p: Spec.Production
  for +rest: +List<Spec.Production>
  for +e: {dropProds(n, grammar) == p <> rest : +List<Spec.Production>}
  {dropProds(1n+n, grammar) == rest : +List<Spec.Production>}

def drop_next(grammar, n, p, rest, e):
  match grammar n:
    case Nil{} 0n:
      Empty.absurd({[] == rest : +List<Spec.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], p <> rest, e)))
    case Nil{} 1n+m:
      Empty.absurd({[] == rest : +List<Spec.Production>}, Lemma.true_is_not_false(Equal.cong(+List<Spec.Production>, Bool, v => prodsEmpty(v), [], p <> rest, e)))
    case Con{+p2, +rest2} 0n:
      Equal.cong(+List<Spec.Production>, +List<Spec.Production>, v => prodsTail(v), p2 <> rest2, p <> rest, e)
    case Con{p2, +rest2} 1n+(+m):
      drop_next(rest2, m, p, rest, e)

law seed_node:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +x: Nat
  for +i: Nat
  for +q: Nat
  for +g: +List<Spec.Tree>
  for +lhsQ: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, q, i, g)
  AllOn(grammar, input, root, [Support.FactDescriptor{Gll.Desc{q, [], 0n, i, i}}])

def seed_node(grammar, input, root, x, i, q, g, lhsQ, node):
  match node:
    case (fit0, (sp0, in0)):
      +fit = {fit0 : {Spec.fits(g, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}}
      +sp = {sp0 : G.Spells(g, input, i)}
      +inG = {in0 : {Spec.allIn(Spec.walk(g, False{}, q, [], 0n, i, i), Spec.steps(root, 0n)) == True{} : Bool}}
      ((x, (g, (g, (lhsQ, ((fit, (sp, inG)), (fit, (sp, (inG, {==})))))))), {==})

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
  for +node: NodeAt(grammar, input, root, q, i, g)
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
  for +node: NodeAt(grammar, input, root, q, i, g)
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
                (lhsQ, L.predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, node_predicts(grammar, start, input, root, rootFit, rootSp, i, q, g, node))))), noConf))))

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
  for +node: NodeAt(grammar, input, root, q, i, g)
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
  for +node: NodeAt(grammar, input, root, q, i, g)
  for +sub: {dropProds(n, grammar) == prods : +List<Spec.Production>}
  AllOn(grammar, input, root, PS.descsWhen(Gll.Predict{t}, grammar, input, Gll.productionsOf(prods, x, n, i)))

def seeds_on(prods, n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, sub):
  match prods:
    case Nil{}:
      {==}
    case Con{Spec.Production{+lhs, +rhs}, +rest}:
      +rec = seeds_on(rest, 1n+n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, drop_next(grammar, n, Spec.Production{lhs, rhs}, rest, sub))
      keep_seed(Nat.is_eq(lhs, x), grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, n, lhs, q, g, lhsQ, node, Gll.productionsOf(rest, x, 1n+n, i), {==}, drop_lhs(grammar, n, lhs, rhs, rest, x, sub), rec)

law U_and_right:
  for -A: Data
  for -B: Data
  for +p: And(A, B)
  B

def U_and_right(A, B, p):
  match p:
    case (a, b):
      b

# A caller on the tree, resumed at a pop of its node: the node ends there, so the
# resumed descriptor and its step are on the tree.
law resume_f:
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
  for +y: Nat
  for +i: Nat
  for +index: Nat
  for +dot: Nat
  for +k: Nat
  for +end: Nat
  for +x: Nat
  for +g: +List<Spec.Tree>
  for +lhs: {Spec.lhsIs(grammar, index, x) == True{} : Bool}
  for +node: NodeAt(grammar, input, root, index, k, g)
  for +fitF: {Spec.fits(f, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))) == True{} : Bool}
  for +spF: G.Spells(f, input, i)
  for +inF: {Spec.allIn(Spec.walk(f, False{}, index, [], dot, k, i), Spec.steps(root, 0n)) == True{} : Bool}
  for +finF: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f))) == Nat.add(k, List.length(&2, Nat, Spec.leaves(g))) : Nat}
  for +itEq: {Gll.nthItem(Spec.rhsOf(grammar, index), dot) == Some{Spec.Sym{Spec.Nonterminal{y}}} : Maybe<&2, Spec.Item>}
  for +pop: NtEnds(grammar, input, root, y, i, end)
  AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end)))

def resume_f(f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, y, i, index, dot, k, end, x, g, lhs, node, fitF, spF, inF, finF, itEq, pop):
  match f:
    case Nil{}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits([], grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits([], grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits([], grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Leaf{+a}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Leaf{a} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Leaf{a} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Node{+q, +ch}, +ts}:
      match pop:
        case (q2, (g2, (lhs2, (node2, ends2)))):
          +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
          +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Node{q, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
            Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Node{q, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
          +h = Bool.and(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), fitF2)
          +lhsQ = Lemma.and_true_left(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, y), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), fitF2)
          +lch = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +e = Nat.add(i, List.length(&2, Nat, lch))
          +spCh = G.spells_first(input, i, lch, lts, spF)
          +spT = G.spells_second(input, i, lch, lts, spF)
          +here = Spec.at(index, [], 1n+dot, k, i, e)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, i, i)
          +wT = Spec.walk(ts, False{}, index, [], 1n+dot, k, e)
          +inA = all_in_tail_n(here, List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n), inF)
          +inCh = all_in_left_n(wCh, wT, Spec.steps(root, 0n), inA)
          +inT = all_in_right_n(wCh, wT, Spec.steps(root, 0n), inA)
          +onS = Lemma.and_true_left(Spec.bsrMember(here, Spec.steps(root, 0n)), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wT), Spec.steps(root, 0n)), inF)
          +finT = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lts)), Nat.add(i, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), Nat.add(k, List.length(&2, Nat, Spec.leaves(g))), G.end_split(i, lch, lts), finF)
          +same = nodes_same(grammar, start, t, po, noConf, input, root, rootFit, rootSp, y, i, q, q2, ch, g2, lhsQ, lhs2, (fitCh, (spCh, inCh)), node2)
          +ge = U_and_right({q == q2 : Nat}, {ch == g2 : +List<Spec.Tree>}, same)
          +eEnd = Equal.trans(Nat, e, Nat.add(i, List.length(&2, Nat, Spec.leaves(g2))), end, Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(i, List.length(&2, Nat, Spec.leaves(v))), ch, g2, ge), ends2)
          %eEnd : AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, _}, Gll.stepAt(index, [], 1n+dot, k, i, _)))
          on_when(Gll.admits(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, e}), [Support.FactDescriptor{Gll.Desc{index, [], 1n+dot, k, e}}, Support.FactStep{Gll.stepAt(index, [], 1n+dot, k, i, e)}], grammar, input, root,
            ((x, (g, (ts, (lhs, (node, (fitT, (spT, (inT, finT)))))))), (onS, {==})))
    case Con{Spec.Pick{+a, +ch}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Pick{a, ch} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Skip{}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Skip{} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Skip{} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))
    case Con{Spec.Loop{+rs}, +ts}:
      +dEq = nth_drop(Spec.rhsOf(grammar, index), dot, Spec.Sym{Spec.Nonterminal{y}}, itEq)
      +fitF2 = Equal.trans(Bool, Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index))), Spec.fits(Spec.Loop{rs} <> ts, grammar, Gll.dropFrom(dot, Spec.rhsOf(grammar, index))), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(Spec.Loop{rs} <> ts, grammar, v), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Equal.sym(+List<Spec.Item>, Gll.dropFrom(dot, Spec.rhsOf(grammar, index)), Spec.Sym{Spec.Nonterminal{y}} <> Gll.dropFrom(1n+dot, Spec.rhsOf(grammar, index)), dEq)), fitF)
      Empty.absurd(AllOn(grammar, input, root, PS.pairWhen(Gll.Predict{t}, grammar, input, Gll.Desc{index, [], 1n+dot, k, end}, Gll.stepAt(index, [], 1n+dot, k, i, end))), Lemma.false_is_not_true(fitF2))

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
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, Nil{}, +dot, +k}:
      match here:
        case (d, itEq):
          match d:
            case (x, (g, (f, (lhs, (node, (fitF, (spF, (inF, finF)))))))):
              resume_f(f, grammar, start, t, po, noConf, input, root, rootFit, rootSp, y, i, index, dot, k, end, x, g, lhs, node, fitF, spF, inF, finF, itEq, pop)
    case Gll.CKey{Gll.TNt{+y}, +i} Gll.Edge{+index, Con{+a, +r}, +dot, +k}:
      match here:
        case (d, itEq):
          Empty.absurd(AllOn(grammar, input, root, PS.resumeGives(Gll.Predict{t}, grammar, input, Gll.CKey{Gll.TNt{y}, i}, Gll.Edge{index, a <> r, dot, k}, end)), Lemma.false_is_not_true(d))
    case Gll.CKey{Gll.TBr{+index, +rpath}, +i} +e:
      Empty.absurd(AllOn(grammar, input, root, PS.resumeGives(Gll.Predict{t}, grammar, input, Gll.CKey{Gll.TBr{index, rpath}, i}, e, end)), Lemma.false_is_not_true(here))

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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +reached: +List<Support.Fact>
  for +here: On(grammar, input, root, fact)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.factGives(fact, Gll.Predict{t}, grammar, input, reached))

def fact_on(fact, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, reached, here, all):
  match fact:
    case Support.FactDescriptor{Gll.Desc{+index, Nil{}, +dot, +k, +i}}:
      match here:
        case (x, (g, (f, (lhs, (node, (fitF, (spF, (inF, finF)))))))):
          item_on(Gll.nthItem(Spec.rhsOf(grammar, index), dot), f, grammar, input, root, Gll.Predict{t}, plain, index, dot, k, i, x, g, lhs, node, fitF, spF, inF, finF, {==})
    case Support.FactDescriptor{Gll.Desc{+index, Con{+a, +r}, +dot, +k, +i}}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactDescriptor{Gll.Desc{index, a <> r, dot, k, i}}, Gll.Predict{t}, grammar, input, reached)), Lemma.false_is_not_true(here))
    case Support.FactCluster{Gll.CKey{Gll.TNt{+x}, +i}}:
      match here:
        case (q, (g, (lhsQ, node))):
          seeds_on(grammar, 0n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, x, i, q, g, lhsQ, node, {==})
    case Support.FactCluster{Gll.CKey{Gll.TBr{+index, +rpath}, +i}}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactCluster{Gll.CKey{Gll.TBr{index, rpath}, i}}, Gll.Predict{t}, grammar, input, reached)), Lemma.false_is_not_true(here))
    case Support.FactReturn{+key, +edge}:
      edge_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, edge, here, all)
    case Support.FactPop{Gll.CKey{Gll.TNt{+x}, +k}, +end}:
      +key = {Gll.CKey{Gll.TNt{x}, k} : Gll.CKey}
      on_append(PS.popGives(Gll.Predict{t}, grammar, input, reached, key, end), [], grammar, input, root, pop_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, key, end, here, all), {==})
    case Support.FactPop{Gll.CKey{Gll.TBr{+index, +rpath}, +k}, +end}:
      Empty.absurd(AllOn(grammar, input, root, PS.factGives(Support.FactPop{Gll.CKey{Gll.TBr{index, rpath}, k}, end}, Gll.Predict{t}, grammar, input, reached)), Lemma.false_is_not_true(here))
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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +reached: +List<Support.Fact>
  for +here: AllOn(grammar, input, root, facts)
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.allGive(facts, Gll.Predict{t}, grammar, input, reached))

def all_give_on(facts, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, reached, here, all):
  match facts:
    case Nil{}:
      {==}
    case Con{+fact, +rest}:
      match here:
        case (h0, t0):
          +h = {h0 : On(grammar, input, root, fact)}
          +tl = {t0 : AllOn(grammar, input, root, rest)}
          on_append(PS.factGives(fact, Gll.Predict{t}, grammar, input, reached), PS.allGive(rest, Gll.Predict{t}, grammar, input, reached), grammar, input, root,
            fact_on(fact, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, reached, h, all),
            all_give_on(rest, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, reached, tl, all))

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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +s: Gll.GState
  for +reached: +List<Support.Fact>
  for +all: AllOn(grammar, input, root, reached)
  AllOn(grammar, input, root, PS.grow(n, Gll.Predict{t}, grammar, input, s, reached))

def grow_on(n, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, s, reached, all):
  match n:
    case 0n:
      all
    case 1n+(+m):
      +next = PS.round(Gll.Predict{t}, grammar, input, s, reached)
      grow_on(m, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, s, next,
        on_add(PS.allGive(reached, Gll.Predict{t}, grammar, input, reached), s, reached, grammar, input, root, all_give_on(reached, grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, reached, all, all), all))

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
      +node = {(fitCh, (G.root_spells(input, q, ch, rootSpX), U.all_in_refl(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)))) : NodeAt(grammar, input, Spec.Node{q, ch}, q, 0n, ch)}
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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +s: Gll.GState
  for +sup: {PS.supportedWith(Gll.Predict{t}, grammar, start, input, s) == True{} : Bool}
  AllOn(grammar, input, root, Support.factsOf(s))

def supported_on(grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, s, sup):
  +facts = Support.factsOf(s)
  +first = Support.addWithin(PS.roots(Gll.Predict{t}, grammar, input, start), s, [])
  +reached = PS.grow(List.length(&2, Support.Fact, facts), Gll.Predict{t}, grammar, input, s, first)
  reached_on(facts, reached, grammar, input, root, sup,
    grow_on(List.length(&2, Support.Fact, facts), grammar, start, t, po, noConf, input, root, rootFit, rootSp, plain, s, first,
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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for facts: {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}
  Spec.IsExactBsr(grammar, start, input, set)

def state_exact(grammar, start, t, ll1, plain, input, tree, fit, sp, s, set, facts):
  match facts:
    case (ok0, same0):
      +ok = {ok0 : {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool}}
      +same = {same0 : {Check.stepsOf(s) == set : +List<Spec.Bsr>}}
      +closedRoot = Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s))
      +cr = Lemma.and_true_left(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +sup = Lemma.and_true_right_side(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +po = Lemma.and_true_left(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +noConf = Lemma.and_true_right_side(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +onTree = supported_on(grammar, start, t, po, noConf, input, tree, fit, sp, plain, s, sup)
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
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +set: +List<Spec.Bsr>
  for got: {PS.runLL(r, Gll.Predict{t}, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def run_exact(r, grammar, start, t, ll1, plain, input, tree, fit, sp, set, got):
  match r:
    case Gll.GDone{+s}:
      +ok = Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s))
      state_exact(grammar, start, t, ll1, plain, input, tree, fit, sp, s, set, G.check_pick(ok, s, set, got))
    case Gll.OutOfFuel{s}:
      Empty.absurd(Spec.IsExactBsr(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# NO DEAD WOOD, FOR A GRAMMAR WITHOUT BRACKETS.
law ll1_no_dead_wood_bnf:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +t: Gll.Tables
  for +tablesEq: {First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start) == Some{t} : Maybe<&2, Gll.Tables>}
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for got: {PS.llSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def ll1_no_dead_wood_bnf(fuel, grammar, start, input, set, plain, t, tablesEq, ll1, tree, fit, sp, got):
  +tb = First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start)
  run_exact(Gll.parseWith(fuel, Gll.Predict{t}, grammar, start, input), grammar, start, t, ll1, plain, input, tree, fit, sp, set,
    Equal.trans(Maybe<&2, +List<Spec.Bsr>>, PS.llPick(Some{t}, fuel, grammar, start, input), PS.llPick(tb, fuel, grammar, start, input), Some{set},
      Equal.cong(Maybe<&2, Gll.Tables>, Maybe<&2, +List<Spec.Bsr>>, v => PS.llPick(v, fuel, grammar, start, input), Some{t}, tb, Equal.sym(Maybe<&2, Gll.Tables>, tb, Some{t}, tablesEq)), got))
