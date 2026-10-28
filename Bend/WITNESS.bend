import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune

# WITNESS TREES (not trusted): parse trees built from the pruned steps, so that every
# kept step shows up in one of them. EXACT.bend checks each tree against SPEC.bend.
#
# The search builds forests for segments, guided by the kept steps: the forest of a
# segment ends with the item of one of its steps, after a forest for the segment
# before that step. A loop's rounds are built from the last one back. Everything is
# one recursive function over a task, as Bend allows no mutual recursion; a segment
# may appear at most twice on a path, which keeps the search finite and still lets
# a loop have empty rounds.

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

def treeIf(ok: Bool, +t: Spec.Tree, ts: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match ok:
    case True{}:
      t <> ts
    case False{}:
      ts

# The candidates for the whole input that fit the start symbol.
def rootTrees(cands: +List<Cand>, +grammar: +List<Spec.Production>, +start: Nat) -> +List<Spec.Tree>:
  match cands:
    case Nil{}:
      []
    case Con{Cand{Con{+t, Nil{}}, 0n}, rest}:
      treeIf(Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), t, rootTrees(rest, grammar, start))
    case Con{c, rest}:
      rootTrees(rest, grammar, start)

# Parse trees of the input built from the kept steps.
def witnesses(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Spec.Bsr>) -> +List<Spec.Tree>:
  rootTrees(solve(fuel, grammar, input, ps, [], TProds{grammar, 0n, start, 0n, List.length(&2, Nat, input)}), grammar, start)
