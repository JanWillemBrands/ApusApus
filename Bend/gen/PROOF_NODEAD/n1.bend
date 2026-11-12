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
