import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./GUARD.bend as Guard

# PHASE 2'S RIVAL SEARCH: is there a forest for production m over i .. e whose steps keep
# their rules? Segments are grown Earley-style on the input (not trusted): from a prefix of
# a node of q at ks read up to dot d and position k, one more item, only through steps that
# phase 1 answers Yes; each segment carries a forest. Then the segments are checked closed:
# every step that extends a segment and is not answered No leads to a segment of the set,
# and no such step is answered Unknown. A closed set with m's start but without m's whole
# segment shows that no rival exists (PROOF_RIVAL.bend).

type Seg is Data:
  Seg{q: Nat, ks: Nat, d: Nat, end: Nat, forest: +List<Core.Tree>}

def keyIs(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, s: Seg) -> Bool:
  match s:
    case Seg{q2, ks2, d2, e2, fo}:
      Bool.and(Nat.is_eq(q2, q), Bool.and(Nat.is_eq(ks2, ks), Bool.and(Nat.is_eq(d2, d), Nat.is_eq(e2, e))))

def hasSeg(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, segs: +List<Seg>) -> Bool:
  match segs:
    case Nil{}:
      False{}
    case Con{+s, rest}:
      Bool.or(keyIs(q, ks, d, e, s), hasSeg(q, ks, d, e, rest))

def forestPick(hit: Bool, +fo: +List<Core.Tree>, +later: +List<Core.Tree>) -> +List<Core.Tree>:
  match hit:
    case True{}:
      fo
    case False{}:
      later

# The forest of the first segment with this key ([] when there is none).
def forestAt(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, segs: +List<Seg>) -> +List<Core.Tree>:
  match segs:
    case Nil{}:
      []
    case Con{Seg{+q2, +ks2, +d2, +e2, +fo}, rest}:
      forestPick(keyIs(q, ks, d, e, Seg{q2, ks2, d2, e2, fo}), fo, forestAt(q, ks, d, e, rest))

def tri(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +y: Core.Bsr) -> Guard.Tri:
  Guard.stepTri(fuel, grammar, gmarks, input, y)

# The step that ends a node of p over k .. e, beyond the steps of its items: the one step of
# an empty right side.
def endTri(rhs: +List<Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +p: Nat, +k: Nat, +e: Nat) -> Guard.Tri:
  match rhs:
    case Nil{}:
      tri(fuel, grammar, gmarks, input, Core.Bsr{p, 0n, k, k, e})
    case Con{s, rest}:
      Guard.Yes{}

# ======== THE CHECK ========

# What a step's verdict asks of the set: Yes, the conclusion; No, nothing; Unknown, fails.
def clause(t: Guard.Tri, c: Bool) -> Bool:
  match t:
    case Guard.Yes{}:
      c
    case Guard.No{}:
      True{}
    case Guard.Unknown{}:
      False{}

def whenB(b: Bool, c: Bool) -> Bool:
  match b:
    case True{}:
      c
    case False{}:
      True{}

# A completed segment of p over k .. e lets the prefix (q, ks, d, k) read its item x.
def compOk(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e: Nat) -> Bool:
  clause(endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e),
    whenB(Gll.needHolds(need, k, e), clause(tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e}), hasSeg(q, ks, 1n+d, e, segs))))

def compsOk(ss: +List<Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Seg{+p2, +k2, +d2, +e, fo}, rest}:
      Bool.and(whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))),
          compOk(fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k, e)),
        compsOk(rest, fuel, grammar, gmarks, input, segs, need, p, q, ks, d, k))

# Every production of x starts at k, and every completed one lets the prefix go on.
def prodsOk(g: +List<Core.Production>, +base: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +x: Nat, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match g:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, rhs}, rest}:
      Bool.and(whenB(Nat.is_eq(lhs, x), Bool.and(hasSeg(base, k, 0n, k, segs), compsOk(segs, fuel, grammar, gmarks, input, segs, need, base, q, ks, d, k))),
        prodsOk(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k))

def extOk(item: Maybe<&2, Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match item:
    case Some{Core.Terminal{+t}}:
      whenB(Core.tokIs(Core.tokAt(input, k), t), clause(tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}), hasSeg(q, ks, 1n+d, 1n+k, segs)))
    case Some{Core.Nonterminal{+x, +need}}:
      prodsOk(grammar, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k)
    case None{}:
      True{}

def closedAll(ss: +List<Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Seg{+q, +ks, +d, +k, fo}, rest}:
      Bool.and(extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k), closedAll(rest, fuel, grammar, gmarks, input, segs))

# ======== GROWING THE SEGMENTS (not trusted) ========

def segIf(b: Bool, +s: Seg) -> +List<Seg>:
  match b:
    case True{}:
      [s]
    case False{}:
      []

def isYes(t: Guard.Tri) -> Bool:
  Guard.isYes(t)

def completeWith(ss: +List<Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match ss:
    case Nil{}:
      []
    case Con{Seg{+p2, +k2, +d2, +e, +fp}, rest}:
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))),
        Bool.and(isYes(endTri(Core.rhsOf(grammar, p), fuel, grammar, gmarks, input, p, k, e)),
          Bool.and(Gll.needHolds(need, k, e), isYes(tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, e})))))
      List.append(&2, Seg, segIf(hit, Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}),
        completeWith(rest, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f))

def prodPick(hit: Bool, +segs: +List<Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match hit:
    case True{}:
      completeWith(segs, fuel, grammar, gmarks, input, need, p, q, ks, d, k, f)
    case False{}:
      []

def growProds(g: +List<Core.Production>, +base: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +x: Nat, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match g:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, rhs}, rest}:
      List.append(&2, Seg, segIf(Nat.is_eq(lhs, x), Seg{base, k, 0n, k, []}),
        List.append(&2, Seg, prodPick(Nat.is_eq(lhs, x), segs, fuel, grammar, gmarks, input, need, base, q, ks, d, k, f),
          growProds(rest, 1n+base, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f)))

def growItem(item: Maybe<&2, Core.Sym>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match item:
    case Some{Core.Terminal{+t}}:
      segIf(Bool.and(Core.tokIs(Core.tokAt(input, k), t), isYes(tri(fuel, grammar, gmarks, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}))),
        Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])})
    case Some{Core.Nonterminal{+x, +need}}:
      growProds(grammar, 0n, fuel, grammar, gmarks, input, segs, x, need, q, ks, d, k, f)
    case None{}:
      []

def growAll(ss: +List<Seg>, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>) -> +List<Seg>:
  match ss:
    case Nil{}:
      []
    case Con{Seg{+q, +ks, +d, +k, +f}, rest}:
      List.append(&2, Seg, growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), fuel, grammar, gmarks, input, segs, q, ks, d, k, f),
        growAll(rest, fuel, grammar, gmarks, input, segs))

def addPick(have: Bool, +s: Seg, +segs: +List<Seg>) -> +List<Seg>:
  match have:
    case True{}:
      segs
    case False{}:
      List.append(&2, Seg, segs, [s])

def addNew(new: +List<Seg>, +segs: +List<Seg>) -> +List<Seg>:
  match new:
    case Nil{}:
      segs
    case Con{Seg{+q, +ks, +d, +e, +f}, rest}:
      addNew(rest, addPick(hasSeg(q, ks, d, e, segs), Seg{q, ks, d, e, f}, segs))

def grow(n: Nat, +fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +segs: +List<Seg>) -> +List<Seg>:
  match n:
    case 0n:
      segs
    case 1n+(+p):
      grow(p, fuel, grammar, gmarks, input, addNew(growAll(segs, fuel, grammar, gmarks, input, segs), segs))

# The segments grown from a node of m at i.
def segsFrom(+fuel: Nat, +grammar: +List<Core.Production>, +gmarks: +List<Guard.GuardMark>, +input: +List<Nat>, +m: Nat, +i: Nat) -> +List<Seg>:
  grow(fuel, fuel, grammar, gmarks, input, [Seg{m, i, 0n, i, []}])
