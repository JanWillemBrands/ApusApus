import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll

# DOES PRODUCTION q DERIVE w? A judge-free closure on w (not trusted), the same Earley-style
# growth as phase 2's rival search (RIVAL.bend) with every step allowed: from a prefix of a
# node of q at ks read up to dot d and position k, one more item; each segment carries a
# forest. Then the segments are checked closed: every step that extends a segment leads to a
# segment of the set. A closed set with q's start but without q's whole segment over w shows
# that q does not derive w (PROOF_CLOSURE.bend); a segment that completes q carries a forest
# that GUARD.bend checks with `reads`.

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

# ======== THE CHECK ========

def whenB(b: Bool, c: Bool) -> Bool:
  match b:
    case True{}:
      c
    case False{}:
      True{}

# A completed segment of p over k .. e lets the prefix (q, ks, d, k) read its item.
def compOk(+segs: +List<Seg>, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +e: Nat) -> Bool:
  whenB(Gll.needHolds(need, k, e), hasSeg(q, ks, 1n+d, e, segs))

def compsOk(ss: +List<Seg>, +grammar: +List<Core.Production>, +segs: +List<Seg>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Seg{+p2, +k2, +d2, +e, fo}, rest}:
      Bool.and(whenB(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))),
          compOk(segs, need, q, ks, d, k, e)),
        compsOk(rest, grammar, segs, need, p, q, ks, d, k))

# Every production of x starts at k, and every completed one lets the prefix go on.
def prodsOk(g: +List<Core.Production>, +base: Nat, +grammar: +List<Core.Production>, +segs: +List<Seg>,
  +x: Nat, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match g:
    case Nil{}:
      True{}
    case Con{Core.Production{+lhs, rhs}, rest}:
      Bool.and(whenB(Nat.is_eq(lhs, x), Bool.and(hasSeg(base, k, 0n, k, segs), compsOk(segs, grammar, segs, need, base, q, ks, d, k))),
        prodsOk(rest, 1n+base, grammar, segs, x, need, q, ks, d, k))

def extOk(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat) -> Bool:
  match item:
    case Some{Core.Terminal{+t}}:
      whenB(Core.tokIs(Core.tokAt(input, k), t), hasSeg(q, ks, 1n+d, 1n+k, segs))
    case Some{Core.Nonterminal{+x, +need}}:
      prodsOk(grammar, 0n, grammar, segs, x, need, q, ks, d, k)
    case None{}:
      True{}

def closedAll(ss: +List<Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<Seg>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{Seg{+q, +ks, +d, +k, fo}, rest}:
      Bool.and(extOk(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k), closedAll(rest, grammar, input, segs))

# ======== GROWING THE SEGMENTS (not trusted) ========

def segIf(b: Bool, +s: Seg) -> +List<Seg>:
  match b:
    case True{}:
      [s]
    case False{}:
      []

def completeWith(ss: +List<Seg>, +grammar: +List<Core.Production>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match ss:
    case Nil{}:
      []
    case Con{Seg{+p2, +k2, +d2, +e, +fp}, rest}:
      +hit = Bool.and(Bool.and(Nat.is_eq(p2, p), Bool.and(Nat.is_eq(k2, k), Nat.is_eq(d2, List.length(&2, Core.Sym, Core.rhsOf(grammar, p))))), Gll.needHolds(need, k, e))
      List.append(&2, Seg, segIf(hit, Seg{q, ks, 1n+d, e, List.append(&2, Core.Tree, f, [Core.Node{p, fp}])}),
        completeWith(rest, grammar, need, p, q, ks, d, k, f))

def prodPick(hit: Bool, +segs: +List<Seg>, +grammar: +List<Core.Production>,
  +need: Core.Need, +p: Nat, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match hit:
    case True{}:
      completeWith(segs, grammar, need, p, q, ks, d, k, f)
    case False{}:
      []

def growProds(g: +List<Core.Production>, +base: Nat, +grammar: +List<Core.Production>, +segs: +List<Seg>,
  +x: Nat, +need: Core.Need, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match g:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, rhs}, rest}:
      List.append(&2, Seg, segIf(Nat.is_eq(lhs, x), Seg{base, k, 0n, k, []}),
        List.append(&2, Seg, prodPick(Nat.is_eq(lhs, x), segs, grammar, need, base, q, ks, d, k, f),
          growProds(rest, 1n+base, grammar, segs, x, need, q, ks, d, k, f)))

def growItem(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<Seg>,
  +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: +List<Core.Tree>) -> +List<Seg>:
  match item:
    case Some{Core.Terminal{+t}}:
      segIf(Core.tokIs(Core.tokAt(input, k), t), Seg{q, ks, 1n+d, 1n+k, List.append(&2, Core.Tree, f, [Core.Leaf{t}])})
    case Some{Core.Nonterminal{+x, +need}}:
      growProds(grammar, 0n, grammar, segs, x, need, q, ks, d, k, f)
    case None{}:
      []

def growAll(ss: +List<Seg>, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<Seg>) -> +List<Seg>:
  match ss:
    case Nil{}:
      []
    case Con{Seg{+q, +ks, +d, +k, +f}, rest}:
      List.append(&2, Seg, growItem(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, segs, q, ks, d, k, f),
        growAll(rest, grammar, input, segs))

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

def grow(n: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +segs: +List<Seg>) -> +List<Seg>:
  match n:
    case 0n:
      segs
    case 1n+(+p):
      grow(p, grammar, input, addNew(growAll(segs, grammar, input, segs), segs))

# The segments grown from a node of m at i, with `fuel` rounds.
def segsFrom(+fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +m: Nat, +i: Nat) -> +List<Seg>:
  grow(fuel, grammar, input, [Seg{m, i, 0n, i, []}])
