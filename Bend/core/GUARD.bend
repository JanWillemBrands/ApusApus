import Base
import ../LEMMAS.bend as Lemma
import ../SPEC.bend as Spec
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./EBNF.bend as E
import ./CLOSURE.bend as C

# PHASE 1 ON THE CORE: lookahead, @left and @right.
#
# Every rule sits on a production of the core (a rule on a bracket alternative sits on that
# alternative's group production). A node keeps the rules of its production: each listed
# nonterminal derives a prefix of the tokens from where the node starts (>?>), or none does
# (>!>); the node's last child spells nothing that the production itself (bare @left) or a
# listed nonterminal derives, and likewise its first child (@right).

# ======== THE MEANING ========

type Guard is Data:
  Ahead{ids: +List<Nat>}
  NotAhead{ids: +List<Nat>}
  LeftAssoc{ids: +List<Nat>}
  RightAssoc{ids: +List<Nat>}

type GuardMark is Data:
  GuardMark{index: Nat, guard: Guard}

def nt(+x: Nat) -> +List<Core.Sym>:
  [Core.Nonterminal{x, Core.Anything{}}]

def DerivesAhead(+grammar: +List<Core.Production>, +x: Nat, +ahead: +List<Nat>) -> Type:
  &pre: +List<Nat> -> &post: +List<Nat> -> {List.append(&2, Nat, pre, post) == ahead : +List<Nat>} & Core.Derives(grammar, nt(x), pre)

def AllAhead(+grammar: +List<Core.Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      DerivesAhead(grammar, x, ahead) & AllAhead(grammar, rest, ahead)

def NoneAhead(+grammar: +List<Core.Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      (DerivesAhead(grammar, x, ahead) -> Empty) & NoneAhead(grammar, rest, ahead)

def NoneDerive(+grammar: +List<Core.Production>, xs: +List<Nat>, +w: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      (Core.Derives(grammar, nt(x), w) -> Empty) & NoneDerive(grammar, rest, w)

# Bare: the production's own right side must not derive w; listed: no listed nonterminal may.
def EdgeOk(+grammar: +List<Core.Production>, ids: +List<Nat>, +q: Nat, +w: +List<Nat>) -> Type:
  match ids:
    case Nil{}:
      Core.Derives(grammar, Core.rhsOf(grammar, q), w) -> Empty
    case Con{+x, +rest}:
      NoneDerive(grammar, x <> rest, w)

def guardIf(hit: Bool, +g: Guard, +rest: +List<Guard>) -> +List<Guard>:
  match hit:
    case True{}:
      g <> rest
    case False{}:
      rest

def guardsOf(marks: +List<GuardMark>, +q: Nat) -> +List<Guard>:
  match marks:
    case Nil{}:
      []
    case Con{GuardMark{+p, +g}, rest}:
      guardIf(Nat.is_eq(p, q), g, guardsOf(rest, q))

# A condition that applies only when b holds.
def When(b: Bool, t: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      Unit

# THE RULES A STEP DECIDES. A step of production q (with n items) after dot d, whose node
# starts at i, and whose last item spans k .. j. The completed step (d = n) decides >?> and
# >!> (over the tokens from the node's start) and @left (over what its last item spells);
# the first step (d = 1) decides @right (over what its first item spells). Every other step
# decides nothing. A node's last item is its last child and its first item its first child,
# so these are the rules on the node, read where the parse records them.
def StepHolds(+grammar: +List<Core.Production>, g: Guard, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Type:
  match g:
    case Ahead{+ids}:
      When(Nat.is_eq(d, n), AllAhead(grammar, ids, Lemma.dropN(i, input)))
    case NotAhead{+ids}:
      When(Nat.is_eq(d, n), NoneAhead(grammar, ids, Lemma.dropN(i, input)))
    case LeftAssoc{+ids}:
      When(Bool.and(Nat.is_eq(d, n), Bool.not(Nat.is_eq(d, 0n))), EdgeOk(grammar, ids, q, Lemma.slice(input, k, Nat.sub(j, k))))
    case RightAssoc{+ids}:
      When(Nat.is_eq(d, 1n), EdgeOk(grammar, ids, q, Lemma.slice(input, k, Nat.sub(j, k))))

def StepRules(+grammar: +List<Core.Production>, gs: +List<Guard>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{+g, rest}:
      StepHolds(grammar, g, input, q, n, d, i, k, j) & StepRules(grammar, rest, input, q, n, d, i, k, j)

def StepOk(+grammar: +List<Core.Production>, +marks: +List<GuardMark>, +input: +List<Nat>, x: Core.Bsr) -> Type:
  match x:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      StepRules(grammar, guardsOf(marks, q), input, q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), d, i, k, j)

def AllStepsOk(+grammar: +List<Core.Production>, +marks: +List<GuardMark>, +input: +List<Nat>, xs: +List<Core.Bsr>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      StepOk(grammar, marks, input, x) & AllStepsOk(grammar, marks, input, rest)

# An admissible tree: every one of its steps keeps the rules it decides.
def Admissible(+grammar: +List<Core.Production>, +marks: +List<GuardMark>, +input: +List<Nat>, +tree: Core.Tree) -> Type:
  AllStepsOk(grammar, marks, input, Core.steps([tree], 0n))

# A set that embeds exactly the admissible trees: a parse tree of the input uses only steps
# of the set when, and only when, it is admissible. (The set may hold other steps too.)
def EmbedsAdmissible(+grammar: +List<Core.Production>, +marks: +List<GuardMark>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>) -> Type:
  @tree: Core.Tree -> Core.ParseTree(grammar, start, input, tree) ->
    ({Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool} -> Admissible(grammar, marks, input, tree)) &
    (Admissible(grammar, marks, input, tree) -> {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool})

# ======== THE RULES AS WRITTEN, ON THE CORE ========

def guardOf(g: Spec.Guard) -> Guard:
  match g:
    case Spec.Ahead{+ids}:
      Ahead{ids}
    case Spec.NotAhead{+ids}:
      NotAhead{ids}
    case Spec.LeftAssoc{+ids}:
      LeftAssoc{ids}
    case Spec.RightAssoc{+ids}:
      RightAssoc{ids}

def originIs(o: E.Origin, +index: Nat, +path: +List<Nat>) -> Bool:
  match o:
    case E.Sequence{+i2, +p2}:
      Bool.and(Nat.is_eq(index, i2), E.natsEq(path, p2))
    case _:
      False{}

def prodPick(hit: Bool, +q: Nat, +later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{q}
    case False{}:
      later

def productionAt(os: +List<E.Origin>, +index: Nat, +path: +List<Nat>, +q: Nat) -> Maybe<&2, Nat>:
  match os:
    case Nil{}:
      None{}
    case Con{+o, rest}:
      prodPick(originIs(o, index, path), q, productionAt(rest, index, path, 1n+q))

def markAt(m: Maybe<&2, Nat>, +g: Spec.Guard, +rest: +List<GuardMark>) -> +List<GuardMark>:
  match m:
    case Some{+q}:
      GuardMark{q, guardOf(g)} <> rest
    case None{}:
      rest

# A rule on production `index` stays there; a rule on alternative a of the bracket at
# (index, path) moves to the production whose origin is that alternative's sequence.
def marksOf(ms: +List<Spec.GuardMark>, +origins: +List<E.Origin>) -> +List<GuardMark>:
  match ms:
    case Nil{}:
      []
    case Con{Spec.ProdGuard{+index, +g}, rest}:
      GuardMark{index, guardOf(g)} <> marksOf(rest, origins)
    case Con{Spec.AltGuard{+index, +path, +a, +g}, rest}:
      markAt(productionAt(origins, index, List.append(&2, Nat, path, [a]), 0n), g, marksOf(rest, origins))

# ======== THE VERDICT ON A STEP ========
#
# A rule is decided at the steps of its production: >?>, >!> and @left at the last step
# (the node and its last child are known there), @right at the first. Each question "does
# production q derive w?" is answered by the exact parser on w: Yes with a witness forest,
# checked here with `reads`; No when the exact set over w has no completed step of q;
# Unknown otherwise. ORACLE.bend filters the exact set by these verdicts.

type Tri is Data:
  Yes{}
  No{}
  Unknown{}

def andTri(a: Tri, b: Tri) -> Tri:
  match a b:
    case No{} _:
      No{}
    case _ No{}:
      No{}
    case Yes{} Yes{}:
      Yes{}
    case _ _:
      Unknown{}

def orTri(a: Tri, b: Tri) -> Tri:
  match a b:
    case Yes{} _:
      Yes{}
    case _ Yes{}:
      Yes{}
    case No{} No{}:
      No{}
    case _ _:
      Unknown{}

def notTri(a: Tri) -> Tri:
  match a:
    case Yes{}:
      No{}
    case No{}:
      Yes{}
    case Unknown{}:
      Unknown{}

def forestOk(+grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +f: +List<Core.Tree>) -> Bool:
  Bool.and(Core.reads(f, grammar, Core.rhsOf(grammar, q), w, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves(f)), List.length(&2, Nat, w)))

def yesIf(ok: Bool) -> Tri:
  match ok:
    case True{}:
      Yes{}
    case False{}:
      Unknown{}

def noIf(ok: Bool) -> Tri:
  match ok:
    case True{}:
      No{}
    case False{}:
      Unknown{}

# Yes with the forest of a segment that completes q over w, checked with `reads`; No when
# the closed segments from q at 0 do not complete q (CLOSURE.bend); Unknown otherwise.
def foundPick(found: Bool, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +segs: +List<C.Seg>) -> Tri:
  match found:
    case True{}:
      yesIf(forestOk(grammar, q, w, C.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs)))
    case False{}:
      noIf(Bool.and(C.closedAll(segs, grammar, w, segs), C.hasSeg(q, 0n, 0n, 0n, segs)))

# Does production q derive w, judged by the closure from q at 0 on w?
def closureTri(+fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  +segs = C.segsFrom(fuel, grammar, w, q, 0n)
  foundPick(C.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs), grammar, q, w, segs)

# Past the end of the grammar a production has the empty right side: it derives just [].
def emptyTri(w: +List<Nat>) -> Tri:
  match w:
    case Nil{}:
      Yes{}
    case Con{x, rest}:
      No{}

def rhsPick(real: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  match real:
    case True{}:
      closureTri(fuel, grammar, q, w)
    case False{}:
      emptyTri(w)

def rhsTri(+fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  rhsPick(Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), fuel, grammar, q, w)

def ntPick(hit: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  match hit:
    case True{}:
      rhsTri(fuel, grammar, q, w)
    case False{}:
      No{}

# Does nonterminal x derive w: does one of its productions?
def ntFrom(prods: +List<Core.Production>, +fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +q: Nat, +w: +List<Nat>) -> Tri:
  match prods:
    case Nil{}:
      No{}
    case Con{p, rest}:
      orTri(ntPick(Core.lhsIs(grammar, q, x), fuel, grammar, q, w), ntFrom(rest, fuel, grammar, x, 1n+q, w))

def ntTri(+fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +w: +List<Nat>) -> Tri:
  ntFrom(grammar, fuel, grammar, x, 0n, w)

# Does x derive a prefix of `ahead`: one of length m, for m from n down to 0?
def aheadFrom(m: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +ahead: +List<Nat>) -> Tri:
  match m:
    case 0n:
      ntTri(fuel, grammar, x, [])
    case 1n+(+p):
      orTri(ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)), aheadFrom(p, fuel, grammar, x, ahead))

def aheadTri(+fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +ahead: +List<Nat>) -> Tri:
  aheadFrom(List.length(&2, Nat, ahead), fuel, grammar, x, ahead)

def allAheadTri(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(aheadTri(fuel, grammar, x, ahead), allAheadTri(rest, fuel, grammar, ahead))

def noneAheadTri(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(aheadTri(fuel, grammar, x, ahead)), noneAheadTri(rest, fuel, grammar, ahead))

def noneDeriveTri(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(ntTri(fuel, grammar, x, w)), noneDeriveTri(rest, fuel, grammar, w))

def edgeTri(ids: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  match ids:
    case Nil{}:
      notTri(rhsTri(fuel, grammar, q, w))
    case Con{+x, +rest}:
      noneDeriveTri(x <> rest, fuel, grammar, w)

def only(here: Bool, t: Tri) -> Tri:
  match here:
    case True{}:
      t
    case False{}:
      Yes{}

# One rule at the step after dot d of production q (with n items): the node started at i,
# the item before the slot spans k .. j.
def ruleAt(g: Guard, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match g:
    case Ahead{+ids}:
      only(Nat.is_eq(d, n), allAheadTri(ids, fuel, grammar, Lemma.dropN(i, input)))
    case NotAhead{+ids}:
      only(Nat.is_eq(d, n), noneAheadTri(ids, fuel, grammar, Lemma.dropN(i, input)))
    case LeftAssoc{+ids}:
      only(Bool.and(Nat.is_eq(d, n), Bool.not(Nat.is_eq(d, 0n))), edgeTri(ids, fuel, grammar, q, Lemma.slice(input, k, Nat.sub(j, k))))
    case RightAssoc{+ids}:
      only(Nat.is_eq(d, 1n), edgeTri(ids, fuel, grammar, q, Lemma.slice(input, k, Nat.sub(j, k))))

def rulesAt(gs: +List<Guard>, +fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match gs:
    case Nil{}:
      Yes{}
    case Con{+g, rest}:
      andTri(ruleAt(g, fuel, grammar, input, q, n, d, i, k, j), rulesAt(rest, fuel, grammar, input, q, n, d, i, k, j))

def stepTri(+fuel: Nat, +grammar: +List<Core.Production>, +marks: +List<GuardMark>, +input: +List<Nat>, e: Core.Bsr) -> Tri:
  match e:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      rulesAt(guardsOf(marks, q), fuel, grammar, input, q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), d, i, k, j)

def isUnknown(t: Tri) -> Bool:
  match t:
    case Unknown{}:
      True{}
    case _:
      False{}

def isYes(t: Tri) -> Bool:
  match t:
    case Yes{}:
      True{}
    case _:
      False{}
