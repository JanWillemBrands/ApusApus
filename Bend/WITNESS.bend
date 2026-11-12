import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune

# WITNESS TREES (not trusted): parse trees built from the pruned steps, so that every
# kept step shows up in one of them. EXACT.bend checks each tree against SPEC.bend.
#
# `witnesses` (for EXACT.bend) is the covering search at the end of this file: one tree
# per kept step that no earlier tree covers, from a least fixpoint of facts. `solve`
# (for the certificates of GUARD.bend and EXTENT.bend) lists every forest of a segment.
#
# `solve` builds forests for segments, guided by the kept steps: the forest of a
# segment ends with the item of one of its steps, after a forest for the segment
# before that step. A loop's rounds are built from the last one back. Everything is
# one recursive function over a task, as Bend allows no mutual recursion; a segment
# may appear at most twice on a path, which keeps the search finite and still lets
# a loop have empty rounds. It is exponential, and on a cyclic grammar it may miss
# a forest that repeats a segment more often.

type Cand is Data:
  Cand{forest: +List<Spec.Tree>, start: Nat}

type Task is Data:
  TSeq{seg: Prune.Seg}
  TSeqGo{ok: Bool, seg: Prune.Seg}
  TElems{elems: +List<Spec.Bsr>, index: Nat, rpath: +List<Nat>, ctx: Nat, d: Nat, j: Nat}
  TItem{item: Maybe<&2, Spec.Item>, index: Nat, rpath: +List<Nat>, d: Nat, k: Nat, j: Nat}
  TProds{prods: +List<Spec.Production>, idx: Nat, x: Nat, k: Nat, j: Nat}
  TProdIf{hit: Bool, idx: Nat, len: Nat, k: Nat, j: Nat}
  TAlts{n: Nat, alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, j: Nat}
  TRounds{alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, j: Nat}
  TRoundsGo{ok: Bool, alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, j: Nat}
  TRoundAlts{n: Nat, alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, j: Nat}
  TCands{cands: +List<Cand>, a: Nat, alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, j: Nat}
  TRound1{first: Bool, a: Nat, cs: +List<Spec.Tree>, alts: +List<+List<Spec.Item>>, index: Nat, rpath: +List<Nat>, k: Nat, s: Nat}

def countOne(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# ---- Small helpers ----

def segCount(+x: Prune.Seg, xs: +List<Prune.Seg>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{y, rest}:
      Nat.add(countOne(Prune.segEq(x, y)), segCount(x, rest))

def pivotOf(e: Spec.Bsr) -> Nat:
  match e:
    case Spec.Bsr{slot, i, k, j}:
      k

def keepIf(b: Bool, +e: Spec.Bsr, es: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match b:
    case True{}:
      e <> es
    case False{}:
      es

# The kept steps of a segment.
def elemsOf(ps: +List<Spec.Bsr>, +seg: Prune.Seg) -> +List<Spec.Bsr>:
  match ps:
    case Nil{}:
      []
    case Con{+e, rest}:
      keepIf(Prune.segMatch(Prune.segOf(e), seg), e, elemsOf(rest, seg))

def addItem(+f1: +List<Spec.Tree>, +s1: Nat, items: +List<Cand>) -> +List<Cand>:
  match items:
    case Nil{}:
      []
    case Con{Cand{f2, s2}, rest}:
      Cand{List.append(&2, Spec.Tree, f1, f2), s1} <> addItem(f1, s1, rest)

# Every prefix forest followed by every item tree.
def joinItem(prefixes: +List<Cand>, +items: +List<Cand>) -> +List<Cand>:
  match prefixes:
    case Nil{}:
      []
    case Con{Cand{+f1, +s1}, rest}:
      List.append(&2, Cand, addItem(f1, s1, items), joinItem(rest, items))

def startsAt(b: Bool, +c: Cand, cs: +List<Cand>) -> +List<Cand>:
  match b:
    case True{}:
      c <> cs
    case False{}:
      cs

def wrapNode(+idx: Nat, +k: Nat, cands: +List<Cand>) -> +List<Cand>:
  match cands:
    case Nil{}:
      []
    case Con{Cand{+cs, +st}, rest}:
      startsAt(Nat.is_eq(st, k), Cand{[Spec.Node{idx, cs}], k}, wrapNode(idx, k, rest))

def wrapPick(+a: Nat, +k: Nat, cands: +List<Cand>) -> +List<Cand>:
  match cands:
    case Nil{}:
      []
    case Con{Cand{+cs, +st}, rest}:
      startsAt(Nat.is_eq(st, k), Cand{[Spec.Pick{a, cs}], k}, wrapPick(a, k, rest))

def wrapLoop(+k: Nat, cands: +List<Cand>) -> +List<Cand>:
  match cands:
    case Nil{}:
      []
    case Con{Cand{+rs, st}, rest}:
      Cand{[Spec.Loop{rs}], k} <> wrapLoop(k, rest)

def appendRound(+round: Spec.Tree, +k: Nat, cands: +List<Cand>) -> +List<Cand>:
  match cands:
    case Nil{}:
      []
    case Con{Cand{+rs, st}, rest}:
      Cand{List.append(&2, Spec.Tree, rs, [round]), k} <> appendRound(round, k, rest)

def tokCand(ok: Bool, +t: Nat, +k: Nat) -> +List<Cand>:
  match ok:
    case True{}:
      [Cand{[Spec.Leaf{t}], k}]
    case False{}:
      []

def emptyCand(ok: Bool, +tree: Spec.Tree, +k: Nat) -> +List<Cand>:
  match ok:
    case True{}:
      [Cand{[tree], k}]
    case False{}:
      []

# A round that reads nothing is only the first one (of a < > over nothing).
def roundIf(ok: Bool, cands: +List<Cand>) -> +List<Cand>:
  match ok:
    case True{}:
      cands
    case False{}:
      []

# ---- The search ----

def solve(fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +ps: +List<Spec.Bsr>, +path: +List<Prune.Seg>, task: Task) -> +List<Cand>:
  match fuel task:
    case 0n _:
      []
    case 1n+(+f) TSeq{+seg}:
      solve(f, grammar, input, ps, path, TSeqGo{Nat.is_lt(segCount(seg, path), 2n), seg})
    case 1n+(+f) TSeqGo{False{}, seg}:
      []
    case 1n+(+f) TSeqGo{True{}, Prune.Seg{+ix, +rp, +ctx, 0n, +j}}:
      [Cand{[], j}]
    case 1n+(+f) TSeqGo{True{}, Prune.Seg{+ix, +rp, +ctx, 1n+(+d), +j}}:
      +seg = {Prune.Seg{ix, rp, ctx, 1n+d, j} : Prune.Seg}
      solve(f, grammar, input, ps, seg <> path, TElems{elemsOf(ps, seg), ix, rp, ctx, d, j})
    case 1n+(+f) TElems{Nil{}, ix, rp, ctx, d, j}:
      []
    case 1n+(+f) TElems{Con{+e, +rest}, +ix, +rp, +ctx, +d, +j}:
      +k = pivotOf(e)
      List.append(&2, Cand,
        joinItem(solve(f, grammar, input, ps, path, TSeq{Prune.Seg{ix, rp, ctx, d, k}}), solve(f, grammar, input, ps, path, TItem{Gll.nthItem(Gll.seqAt(grammar, ix, rp), d), ix, rp, d, k, j})),
        solve(f, grammar, input, ps, path, TElems{rest, ix, rp, ctx, d, j}))
    case 1n+(+f) TItem{Some{Spec.Sym{Spec.Terminal{+t}}}, ix, rp, d, +k, +j}:
      tokCand(Bool.and(Gll.tokenIs(List.get(&2, Nat, input, k), t), Nat.is_eq(j, 1n+k)), t, k)
    case 1n+(+f) TItem{Some{Spec.Sym{Spec.Nonterminal{+x}}}, ix, rp, d, +k, +j}:
      solve(f, grammar, input, ps, path, TProds{grammar, 0n, x, k, j})
    case 1n+(+f) TItem{Some{Spec.Brack{Spec.Group{}, +alts}}, +ix, +rp, +d, +k, +j}:
      solve(f, grammar, input, ps, path, TAlts{List.length(&2, +List<Spec.Item>, alts), alts, ix, d <> rp, k, j})
    case 1n+(+f) TItem{Some{Spec.Brack{Spec.Optional{}, +alts}}, +ix, +rp, +d, +k, +j}:
      List.append(&2, Cand, emptyCand(Nat.is_eq(k, j), Spec.Skip{}, k), solve(f, grammar, input, ps, path, TAlts{Nat.mul(countOne(Nat.is_lt(k, j)), List.length(&2, +List<Spec.Item>, alts)), alts, ix, d <> rp, k, j}))
    case 1n+(+f) TItem{Some{Spec.Brack{Spec.Closure{}, +alts}}, +ix, +rp, +d, +k, +j}:
      List.append(&2, Cand, emptyCand(Nat.is_eq(k, j), Spec.Loop{[]}, k), wrapLoop(k, solve(f, grammar, input, ps, path, TRounds{alts, ix, d <> rp, k, j})))
    case 1n+(+f) TItem{Some{Spec.Eps{}}, ix, rp, d, +k, +j}:
      emptyCand(Nat.is_eq(k, j), Spec.Skip{}, k)
    case 1n+(+f) TItem{Some{Spec.Brack{Spec.Positive{}, +alts}}, +ix, +rp, +d, +k, +j}:
      wrapLoop(k, solve(f, grammar, input, ps, path, TRounds{alts, ix, d <> rp, k, j}))
    case 1n+(+f) TItem{None{}, ix, rp, d, k, j}:
      []
    case 1n+(+f) TProds{Nil{}, idx, x, k, j}:
      []
    case 1n+(+f) TProds{Con{Spec.Production{lhs, +rhs}, +rest}, +idx, +x, +k, +j}:
      List.append(&2, Cand, solve(f, grammar, input, ps, path, TProdIf{Nat.is_eq(lhs, x), idx, List.length(&2, Spec.Item, rhs), k, j}), solve(f, grammar, input, ps, path, TProds{rest, 1n+idx, x, k, j}))
    case 1n+(+f) TProdIf{False{}, idx, len, k, j}:
      []
    case 1n+(+f) TProdIf{True{}, +idx, +len, +k, +j}:
      wrapNode(idx, k, solve(f, grammar, input, ps, path, TSeq{Prune.Seg{idx, [], k, len, j}}))
    case 1n+(+f) TAlts{0n, alts, ix, rpb, k, j}:
      []
    case 1n+(+f) TAlts{1n+(+a), +alts, +ix, +rpb, +k, +j}:
      List.append(&2, Cand, wrapPick(a, k, solve(f, grammar, input, ps, path, TSeq{Prune.Seg{ix, a <> rpb, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}})), solve(f, grammar, input, ps, path, TAlts{a, alts, ix, rpb, k, j}))
    case 1n+(+f) TRounds{+alts, +ix, +rpl, +k, +j}:
      +key = {Prune.Seg{ix, rpl, k, 0n, j} : Prune.Seg}
      solve(f, grammar, input, ps, path, TRoundsGo{Nat.is_lt(segCount(key, path), 2n), alts, ix, rpl, k, j})
    case 1n+(+f) TRoundsGo{False{}, alts, ix, rpl, k, j}:
      []
    case 1n+(+f) TRoundsGo{True{}, +alts, +ix, +rpl, +k, +j}:
      solve(f, grammar, input, ps, Prune.Seg{ix, rpl, k, 0n, j} <> path, TRoundAlts{List.length(&2, +List<Spec.Item>, alts), alts, ix, rpl, k, j})
    case 1n+(+f) TRoundAlts{0n, alts, ix, rpl, k, j}:
      []
    case 1n+(+f) TRoundAlts{1n+(+a), +alts, +ix, +rpl, +k, +j}:
      List.append(&2, Cand,
        solve(f, grammar, input, ps, path, TCands{solve(f, grammar, input, ps, path, TSeq{Prune.Seg{ix, a <> rpl, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}}), a, alts, ix, rpl, k, j}),
        solve(f, grammar, input, ps, path, TRoundAlts{a, alts, ix, rpl, k, j}))
    case 1n+(+f) TCands{Nil{}, a, alts, ix, rpl, k, j}:
      []
    case 1n+(+f) TCands{Con{Cand{+cs, +s}, +rest}, +a, +alts, +ix, +rpl, +k, +j}:
      List.append(&2, Cand, roundIf(Bool.or(Nat.is_lt(s, j), Nat.is_eq(s, k)), solve(f, grammar, input, ps, path, TRound1{Nat.is_eq(s, k), a, cs, alts, ix, rpl, k, s})), solve(f, grammar, input, ps, path, TCands{rest, a, alts, ix, rpl, k, j}))
    case 1n+(+f) TRound1{True{}, +a, +cs, +alts, +ix, +rpl, +k, s}:
      [Cand{[Spec.Pick{a, cs}], k}]
    case 1n+(+f) TRound1{False{}, +a, +cs, +alts, +ix, +rpl, +k, +s}:
      appendRound(Spec.Pick{a, cs}, k, solve(f, grammar, input, ps, path, TRounds{alts, ix, rpl, k, s}))

# ---- The covering search (used by `witnesses`) ----
#
# `solve` lists every forest it can build, which is exponential, and on a cyclic grammar
# it may still miss a step whose trees repeat a segment more often than it allows
# (BendDifferential seed 86). EXACT.bend needs only trees that together cover the kept
# steps, so `witnesses` searches for one tree per kept step that no earlier tree covers.
#
# A fact is one forest for a segment (the first `dot` items of a sequence, from where it
# starts to `end`), with the position where the forest starts and whether it contains
# the target step. There is at most one fact per segment, start and flag, so the facts
# are finite; they are found as a least fixpoint over the kept steps, by the same item
# rules as `solve`. A loop's rounds are built by end position, from the facts of their
# round sequences.

type Fact is Data:
  Fact{seg: Prune.Seg, start: Nat, uses: Bool, forest: +List<Spec.Tree>}

# A forest for one item (its start is the item's start), or for a prefix (with its start).
type Opt is Data:
  Opt{uses: Bool, forest: +List<Spec.Tree>}

type Part is Data:
  Part{start: Nat, uses: Bool, forest: +List<Spec.Tree>}

# The rounds of a loop that end at `end`.
type Ends is Data:
  Ends{end: Nat, opts: +List<Opt>}

def boolEq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# Segment equality that compares the paths only when everything else is equal.
def pathsIf(ok: Bool, r1: +List<Nat>, r2: +List<Nat>) -> Bool:
  match ok:
    case True{}:
      Gll.natsEq(r1, r2)
    case False{}:
      False{}

def segSame(a: Prune.Seg, b: Prune.Seg) -> Bool:
  match a b:
    case Prune.Seg{p1, r1, c1, d1, e1} Prune.Seg{p2, r2, c2, d2, e2}:
      pathsIf(Bool.and(Nat.is_eq(p1, p2), Bool.and(Nat.is_eq(e1, e2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(c1, c2)))), r1, r2)

def hasFact(+seg: Prune.Seg, +s: Nat, +u: Bool, facts: +List<Fact>) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Con{Fact{+g, +s2, +u2, f}, rest}:
      Bool.or(Bool.and(segSame(seg, g), Bool.and(Nat.is_eq(s, s2), boolEq(u, u2))), hasFact(seg, s, u, rest))

def addIf(have: Bool, +fact: Fact, +facts: +List<Fact>) -> +List<Fact>:
  match have:
    case True{}:
      facts
    case False{}:
      fact <> facts

def addFact(fact: Fact, +facts: +List<Fact>) -> +List<Fact>:
  match fact:
    case Fact{+g, +s, +u, +f}:
      addIf(hasFact(g, s, u, facts), Fact{g, s, u, f}, facts)

def partIf(b: Bool, +p: Part, ps: +List<Part>) -> +List<Part>:
  match b:
    case True{}:
      p <> ps
    case False{}:
      ps

# The facts of a segment, whatever their start.
def partsOf(+seg: Prune.Seg, facts: +List<Fact>) -> +List<Part>:
  match facts:
    case Nil{}:
      []
    case Con{Fact{+g, +s, +u, +f}, rest}:
      partIf(segSame(seg, g), Part{s, u, f}, partsOf(seg, rest))

def optIf(b: Bool, +o: Opt, os: +List<Opt>) -> +List<Opt>:
  match b:
    case True{}:
      o <> os
    case False{}:
      os

# The facts of a segment that start at k.
def optsAt(+seg: Prune.Seg, +k: Nat, facts: +List<Fact>) -> +List<Opt>:
  match facts:
    case Nil{}:
      []
    case Con{Fact{+g, +s, +u, +f}, rest}:
      optIf(Bool.and(segSame(seg, g), Nat.is_eq(s, k)), Opt{u, f}, optsAt(seg, k, rest))

def hasFlag(+u: Bool, os: +List<Opt>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{Opt{+u2, f}, rest}:
      Bool.or(boolEq(u, u2), hasFlag(u, rest))

# At most one option per flag: the first.
def dedupe(os: +List<Opt>, +acc: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      acc
    case Con{Opt{+u, +f}, rest}:
      dedupe(rest, optIf(Bool.not(hasFlag(u, acc)), Opt{u, f}, acc))

def wrapNodes(+idx: Nat, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+u, +f}, rest}:
      Opt{u, [Spec.Node{idx, f}]} <> wrapNodes(idx, rest)

def wrapPicks(+a: Nat, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+u, +f}, rest}:
      Opt{u, [Spec.Pick{a, f}]} <> wrapPicks(a, rest)

def wrapLoops(os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+u, +rs}, rest}:
      Opt{u, [Spec.Loop{rs}]} <> wrapLoops(rest)

def prodIf(hit: Bool, +idx: Nat, +len: Nat, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match hit:
    case True{}:
      wrapNodes(idx, optsAt(Prune.Seg{idx, [], k, len, j}, k, facts))
    case False{}:
      []

# A nonterminal x over k..j: a node for each production of x whose sequence has a fact.
def prodOpts(prods: +List<Spec.Production>, +idx: Nat, +x: Nat, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match prods:
    case Nil{}:
      []
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      List.append(&2, Opt, prodIf(Nat.is_eq(lhs, x), idx, List.length(&2, Spec.Item, rhs), k, j, facts), prodOpts(rest, 1n+idx, x, k, j, facts))

# A bracket over k..j: a pick for each alternative (counting down from n) with a fact.
def altOpts(n: Nat, +alts: +List<+List<Spec.Item>>, +ix: Nat, +rpb: +List<Nat>, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match n:
    case 0n:
      []
    case 1n+(+a):
      List.append(&2, Opt, wrapPicks(a, optsAt(Prune.Seg{ix, a <> rpb, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), j}, k, facts)), altOpts(a, alts, ix, rpb, k, j, facts))

def endsPick(b: Bool, +os: +List<Opt>, +other: +List<Opt>) -> +List<Opt>:
  match b:
    case True{}:
      os
    case False{}:
      other

def endsAt(+s: Nat, table: +List<Ends>) -> +List<Opt>:
  match table:
    case Nil{}:
      []
    case Con{Ends{+e, +os}, rest}:
      endsPick(Nat.is_eq(s, e), os, endsAt(s, rest))

# Earlier rounds (from the loop start to s), each followed by the round `round`.
def thenRound(+u: Bool, +round: Spec.Tree, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+u2, +rs}, rest}:
      Opt{Bool.or(u, u2), List.append(&2, Spec.Tree, rs, [round])} <> thenRound(u, round, rest)

def roundPick(first: Bool, before: Bool, +u: Bool, +round: Spec.Tree, +s: Nat, +table: +List<Ends>) -> +List<Opt>:
  match first before:
    case True{} _:
      [Opt{u, [round]}]
    case False{} True{}:
      thenRound(u, round, endsAt(s, table))
    case False{} False{}:
      []

# A round of alternative a that starts at s: the only round when s is the loop start k,
# otherwise after the rounds from k to s (s < e: every later round reads something).
def roundFrom(ps: +List<Part>, +a: Nat, +k: Nat, +e: Nat, +table: +List<Ends>) -> +List<Opt>:
  match ps:
    case Nil{}:
      []
    case Con{Part{+s, +u, +f}, rest}:
      List.append(&2, Opt,
        roundPick(Nat.is_eq(s, k), Nat.is_lt(s, e), u, Spec.Pick{a, f}, s, table),
        roundFrom(rest, a, k, e, table))

def roundsEnding(n: Nat, +alts: +List<+List<Spec.Item>>, +ix: Nat, +rpl: +List<Nat>, +k: Nat, +e: Nat, +facts: +List<Fact>, +table: +List<Ends>) -> +List<Opt>:
  match n:
    case 0n:
      []
    case 1n+(+a):
      List.append(&2, Opt,
        roundFrom(partsOf(Prune.Seg{ix, a <> rpl, k, List.length(&2, Spec.Item, Spec.altOf(alts, a)), e}, facts), a, k, e, table),
        roundsEnding(a, alts, ix, rpl, k, e, facts, table))

# The rounds from k to every end k, k+1, …, in that order, so each end can use the earlier ones.
def roundTable(n: Nat, +e: Nat, +alts: +List<+List<Spec.Item>>, +ix: Nat, +rpl: +List<Nat>, +k: Nat, +facts: +List<Fact>, +table: +List<Ends>) -> +List<Ends>:
  match n:
    case 0n:
      table
    case 1n+(+m):
      roundTable(m, 1n+e, alts, ix, rpl, k, facts,
        Ends{e, dedupe(roundsEnding(List.length(&2, +List<Spec.Item>, alts), alts, ix, rpl, k, e, facts, table), [])} <> table)

def roundOpts(+alts: +List<+List<Spec.Item>>, +ix: Nat, +rpl: +List<Nat>, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  wrapLoops(endsAt(j, roundTable(1n+Nat.sub(j, k), k, alts, ix, rpl, k, facts, [])))

# A closure that reads nothing has no rounds; one that reads something has rounds that each read something.
def closureOpts(empty: Bool, +alts: +List<+List<Spec.Item>>, +ix: Nat, +rpl: +List<Nat>, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match empty:
    case True{}:
      [Opt{False{}, [Spec.Loop{[]}]}]
    case False{}:
      roundOpts(alts, ix, rpl, k, j, facts)

# The forests of item d of sequence (ix, rp) over k..j; rpb is d <> rp.
def itemOpts(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +ix: Nat, +rpb: +List<Nat>, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      optIf(Bool.and(Gll.tokenIs(List.get(&2, Nat, input, k), t), Nat.is_eq(j, 1n+k)), Opt{False{}, [Spec.Leaf{t}]}, [])
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      dedupe(prodOpts(grammar, 0n, x, k, j, facts), [])
    case Some{Spec.Brack{Spec.Group{}, +alts}}:
      dedupe(altOpts(List.length(&2, +List<Spec.Item>, alts), alts, ix, rpb, k, j, facts), [])
    case Some{Spec.Brack{Spec.Optional{}, +alts}}:
      optIf(Nat.is_eq(k, j), Opt{False{}, [Spec.Skip{}]}, dedupe(altOpts(Nat.mul(countOne(Nat.is_lt(k, j)), List.length(&2, +List<Spec.Item>, alts)), alts, ix, rpb, k, j, facts), []))
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      closureOpts(Nat.is_eq(k, j), alts, ix, rpb, k, j, facts)
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      roundOpts(alts, ix, rpb, k, j, facts)
    case Some{Spec.Eps{}}:
      optIf(Nat.is_eq(k, j), Opt{False{}, [Spec.Skip{}]}, [])
    case None{}:
      []

# Every prefix forest followed by every item forest, as facts of the step's segment.
def joinOpt(+seg: Prune.Seg, +s: Nat, +pu: Bool, +pf: +List<Spec.Tree>, +hit: Bool, os: +List<Opt>, +facts: +List<Fact>) -> +List<Fact>:
  match os:
    case Nil{}:
      facts
    case Con{Opt{+u, +f}, rest}:
      joinOpt(seg, s, pu, pf, hit, rest, addFact(Fact{seg, s, Bool.or(hit, Bool.or(pu, u)), List.append(&2, Spec.Tree, pf, f)}, facts))

def joinParts(+seg: Prune.Seg, ps: +List<Part>, +hit: Bool, +os: +List<Opt>, +facts: +List<Fact>) -> +List<Fact>:
  match ps:
    case Nil{}:
      facts
    case Con{Part{+s, +u, +f}, rest}:
      joinParts(seg, rest, hit, os, joinOpt(seg, s, u, f, hit, os, facts))

# The prefix before item d: nothing, starting where the item starts, or the prefix's facts.
def prefixParts(+ix: Nat, +rp: +List<Nat>, +ctx: Nat, d: Nat, +k: Nat, +facts: +List<Fact>) -> +List<Part>:
  match d:
    case 0n:
      [Part{k, False{}, []}]
    case 1n+(+m):
      partsOf(Prune.Seg{ix, rp, ctx, 1n+m, k}, facts)

def stepSeg(seg: Maybe<&2, Prune.Seg>, +k: Nat, +hit: Bool, +grammar: +List<Spec.Production>, +input: +List<Nat>, +facts: +List<Fact>) -> +List<Fact>:
  match seg:
    case Some{Prune.Seg{+ix, +rp, +ctx, 1n+(+d), +j}}:
      joinParts(Prune.Seg{ix, rp, ctx, 1n+d, j}, prefixParts(ix, rp, ctx, d, k, facts), hit,
        itemOpts(Gll.nthItem(Gll.seqAt(grammar, ix, rp), d), grammar, input, ix, d <> rp, k, j, facts), facts)
    case _:
      facts

# The segments whose facts a step reads: its prefix and its item's sequences.
type Dep is Data:
  Dep{step: Spec.Bsr, reads: +List<Prune.Seg>}

def segIf(b: Bool, +g: Prune.Seg) -> +List<Prune.Seg>:
  match b:
    case True{}:
      [g]
    case False{}:
      []

def prodSegs(prods: +List<Spec.Production>, +idx: Nat, +x: Nat, +k: Nat, +j: Nat) -> +List<Prune.Seg>:
  match prods:
    case Nil{}:
      []
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      List.append(&2, Prune.Seg, segIf(Nat.is_eq(lhs, x), Prune.Seg{idx, [], k, List.length(&2, Spec.Item, rhs), j}), prodSegs(rest, 1n+idx, x, k, j))

# The alternatives' sequences of a bracket from k to every end in ends.
def segsTo(ends: +List<Nat>, +ix: Nat, +rp: +List<Nat>, +k: Nat, +len: Nat) -> +List<Prune.Seg>:
  match ends:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.Seg{ix, rp, k, len, e} <> segsTo(rest, ix, rp, k, len)

def altSegs(n: Nat, +alts: +List<+List<Spec.Item>>, +ix: Nat, +rpb: +List<Nat>, +k: Nat, +ends: +List<Nat>) -> +List<Prune.Seg>:
  match n:
    case 0n:
      []
    case 1n+(+a):
      List.append(&2, Prune.Seg, segsTo(ends, ix, a <> rpb, k, List.length(&2, Spec.Item, Spec.altOf(alts, a))), altSegs(a, alts, ix, rpb, k, ends))

def upTo(n: Nat, +e: Nat) -> +List<Nat>:
  match n:
    case 0n:
      []
    case 1n+(+m):
      e <> upTo(m, 1n+e)

def itemSegs(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +ix: Nat, +rpb: +List<Nat>, +k: Nat, +j: Nat) -> +List<Prune.Seg>:
  match item:
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      prodSegs(grammar, 0n, x, k, j)
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      altSegs(List.length(&2, +List<Spec.Item>, alts), alts, ix, rpb, k, upTo(1n+Nat.sub(j, k), k))
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      altSegs(List.length(&2, +List<Spec.Item>, alts), alts, ix, rpb, k, upTo(1n+Nat.sub(j, k), k))
    case Some{Spec.Brack{kind, +alts}}:
      altSegs(List.length(&2, +List<Spec.Item>, alts), alts, ix, rpb, k, [j])
    case _:
      []

def prefixSegs(+ix: Nat, +rp: +List<Nat>, +ctx: Nat, d: Nat, +k: Nat) -> +List<Prune.Seg>:
  match d:
    case 0n:
      []
    case 1n+(+m):
      [Prune.Seg{ix, rp, ctx, 1n+m, k}]

def depSegs(seg: Maybe<&2, Prune.Seg>, +k: Nat, +grammar: +List<Spec.Production>) -> +List<Prune.Seg>:
  match seg:
    case Some{Prune.Seg{+ix, +rp, +ctx, 1n+(+d), +j}}:
      List.append(&2, Prune.Seg, prefixSegs(ix, rp, ctx, d, k), itemSegs(Gll.nthItem(Gll.seqAt(grammar, ix, rp), d), grammar, ix, d <> rp, k, j))
    case _:
      []

def depsOf(steps: +List<Spec.Bsr>, +grammar: +List<Spec.Production>) -> +List<Dep>:
  match steps:
    case Nil{}:
      []
    case Con{+e, rest}:
      Dep{e, depSegs(Prune.segOf(e), pivotOf(e), grammar)} <> depsOf(rest, grammar)

def factSegIn(+g: Prune.Seg, fs: +List<Fact>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{Fact{+h, s, u, f}, rest}:
      Bool.or(segSame(g, h), factSegIn(g, rest))

def anyChanged(gs: +List<Prune.Seg>, +changed: +List<Fact>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{+g, rest}:
      Bool.or(factSegIn(g, changed), anyChanged(rest, changed))

def stepIf(run: Bool, +e: Spec.Bsr, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Spec.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  match run:
    case True{}:
      stepSeg(Prune.segOf(e), pivotOf(e), Spec.bsrMember(e, [target]), grammar, input, facts)
    case False{}:
      facts

# One pass: every step when `all`, otherwise only the steps that read a segment with a
# fact added in the previous pass (`changed`). New facts are added at the front.
def pass(deps: +List<Dep>, +all: Bool, +changed: +List<Fact>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Spec.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  match deps:
    case Nil{}:
      facts
    case Con{Dep{+e, +reads}, rest}:
      pass(rest, all, changed, grammar, input, target, stepIf(Bool.or(all, anyChanged(reads, changed)), e, grammar, input, target, facts))

def takeFacts(n: Nat, fs: +List<Fact>) -> +List<Fact>:
  match n fs:
    case 0n _:
      []
    case _ Nil{}:
      []
    case 1n+(+m) Con{+x, rest}:
      x <> takeFacts(m, rest)

# Passes over the steps until no fact is added (semi-naive: after the first pass, only
# steps that read a segment that gained a fact are run again).
def fixpoint(fuel: Nat, all: Bool, +changed: +List<Fact>, +deps: +List<Dep>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Spec.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  match fuel all changed:
    case 0n _ _:
      facts
    case 1n+(+f) False{} Nil{}:
      facts
    case 1n+(+f) _ _:
      +next = pass(deps, all, changed, grammar, input, target, facts)
      fixpoint(f, False{}, takeFacts(Nat.sub(List.length(&2, Fact, next), List.length(&2, Fact, facts)), next), deps, grammar, input, target, next)

def treePick(ok: Bool, +t: Spec.Tree, +other: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match ok:
    case True{}:
      [t]
    case False{}:
      other

# A tree of the whole input that contains the target step, if there is one.
def firstUsing(os: +List<Opt>, +grammar: +List<Spec.Production>, +start: Nat) -> +List<Spec.Tree>:
  match os:
    case Nil{}:
      []
    case Con{Opt{True{}, Con{+t, Nil{}}}, rest}:
      treePick(Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), t, firstUsing(rest, grammar, start))
    case Con{o, rest}:
      firstUsing(rest, grammar, start)

# Starts from `base`, the facts that do not need the target.
def treeThrough(fuel: Nat, +deps: +List<Dep>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +base: +List<Fact>, +target: Spec.Bsr) -> +List<Spec.Tree>:
  +n = List.length(&2, Nat, input)
  firstUsing(prodOpts(grammar, 0n, start, 0n, n, fixpoint(fuel, True{}, [], deps, grammar, input, target, base)), grammar, start)

def stepsOf(ts: +List<Spec.Tree>) -> +List<Spec.Bsr>:
  match ts:
    case Nil{}:
      []
    case Con{+t, rest}:
      List.append(&2, Spec.Bsr, Spec.steps(t, 0n), stepsOf(rest))

def coverPick(covered: Bool, fuel: Nat, +deps: +List<Dep>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +base: +List<Fact>, +e: Spec.Bsr, +trees: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match covered:
    case True{}:
      trees
    case False{}:
      List.append(&2, Spec.Tree, trees, treeThrough(fuel, deps, grammar, start, input, base, e))

# One tree through each kept step that the trees so far do not cover.
def cover(steps: +List<Spec.Bsr>, +fuel: Nat, +deps: +List<Dep>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +base: +List<Fact>, +trees: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match steps:
    case Nil{}:
      trees
    case Con{+e, rest}:
      cover(rest, fuel, deps, grammar, start, input, base, coverPick(Spec.bsrMember(e, stepsOf(trees)), fuel, deps, grammar, start, input, base, e, trees))

# Steps sorted by the length of their span, then by their dot, so that most facts are
# found in the first pass (a step needs facts of shorter or equal spans).
def spanOf(e: Spec.Bsr) -> Nat:
  match e:
    case Spec.Bsr{slot, +i, k, +j}:
      Nat.sub(j, i)

def dotOf(e: Spec.Bsr) -> Nat:
  match e:
    case Spec.Bsr{Spec.Slot{index, +path}, i, k, j}:
      List.length(&2, Nat, path)

def keyPick(same: Bool, +a: Spec.Bsr, +b: Spec.Bsr) -> Bool:
  match same:
    case True{}:
      Nat.is_lt(dotOf(a), dotOf(b))
    case False{}:
      Nat.is_lt(spanOf(a), spanOf(b))

# Does a come before b: a shorter span, or the same span and a smaller dot?
def before(+a: Spec.Bsr, +b: Spec.Bsr) -> Bool:
  keyPick(Nat.is_eq(spanOf(a), spanOf(b)), a, b)

def insertPick(later: Bool, +e: Spec.Bsr, +x: Spec.Bsr, +inserted: +List<Spec.Bsr>, +rest: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match later:
    case True{}:
      x <> inserted
    case False{}:
      e <> (x <> rest)

def insertStep(+e: Spec.Bsr, sorted: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match sorted:
    case Nil{}:
      [e]
    case Con{+x, +rest}:
      insertPick(before(x, e), e, x, insertStep(e, rest), rest)

def sortSteps(ps: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match ps:
    case Nil{}:
      []
    case Con{+e, rest}:
      insertStep(e, sortSteps(rest))

# Parse trees of the input built from the kept steps, together covering every kept step
# they can.
def witnesses(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Spec.Bsr>) -> +List<Spec.Tree>:
  +f = fuel
  +sorted = sortSteps(ps)
  +deps = depsOf(sorted, grammar)
  # No kept step has an empty path (it would have no segment), so this target never matches.
  +base = fixpoint(f, True{}, [], deps, grammar, input, Spec.Bsr{Spec.Slot{0n, []}, 0n, 0n, 0n}, [])
  cover(sorted, f, deps, grammar, start, input, base, [])
