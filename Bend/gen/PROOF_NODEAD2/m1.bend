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
