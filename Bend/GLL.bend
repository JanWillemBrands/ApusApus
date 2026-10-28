import Base
import ./SPEC.bend as Spec

# A GLL PARSER FOR EBNF GRAMMARS (reference engine, not verified; its results will be
# checked instead). After tinyGLL (descriptors, clusters, returns and pops) and Swift
# Apus (every bracket is a cluster of its own; [ ] and { } may be skipped; a closure
# re-enters its own cluster from where it started).
#
# A position in the grammar is a production, a path into nested brackets kept in
# reverse (innermost first: alternative, then item), and a dot. A descriptor
# Desc{index, rpath, dot, k, i} means: at that position, in a sequence that started at
# k, the input has been read up to i.

type Desc is Data:
  Desc{index: Nat, rpath: +List<Nat>, dot: Nat, k: Nat, i: Nat}

# What a cluster is for: a nonterminal, or the bracket at a position.
type Target is Data:
  TNt{id: Nat}
  TBr{index: Nat, rpath: +List<Nat>}

type CKey is Data:
  CKey{target: Target, k: Nat}

# Where to continue after a call: the position of the calling item, and its sequence start.
type Edge is Data:
  Edge{index: Nat, rpath: +List<Nat>, dot: Nat, k: Nat}

type Ret is Data:
  Ret{key: CKey, edge: Edge}

type Pop is Data:
  Pop{key: CKey, j: Nat}

type GState is Data:
  GState{seen: +List<Desc>, todo: +List<Desc>, clusters: +List<CKey>, returns: +List<Ret>, pops: +List<Pop>, yields: +List<Spec.Bsr>}

# ---- Equality and membership ----

def natsEq(xs: +List<Nat>, ys: +List<Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Nat.is_eq(x, y), natsEq(xr, yr))
    case _ _:
      False{}

def targetEq(a: Target, b: Target) -> Bool:
  match a b:
    case TNt{x} TNt{y}:
      Nat.is_eq(x, y)
    case TBr{p, xs} TBr{q, ys}:
      Bool.and(Nat.is_eq(p, q), natsEq(xs, ys))
    case _ _:
      False{}

def keyEq(a: CKey, b: CKey) -> Bool:
  match a b:
    case CKey{t1, k1} CKey{t2, k2}:
      Bool.and(targetEq(t1, t2), Nat.is_eq(k1, k2))

def edgeEq(a: Edge, b: Edge) -> Bool:
  match a b:
    case Edge{p1, r1, d1, k1} Edge{p2, r2, d2, k2}:
      Bool.and(Nat.is_eq(p1, p2), Bool.and(natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Nat.is_eq(k1, k2))))

def descEq(a: Desc, b: Desc) -> Bool:
  match a b:
    case Desc{p1, r1, d1, k1, i1} Desc{p2, r2, d2, k2, i2}:
      Bool.and(Nat.is_eq(p1, p2), Bool.and(natsEq(r1, r2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2)))))

def descIn(+x: Desc, xs: +List<Desc>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(descEq(x, y), descIn(x, rest))

def keyIn(+x: CKey, xs: +List<CKey>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(keyEq(x, y), keyIn(x, rest))

def retIn(+key: CKey, +edge: Edge, xs: +List<Ret>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{Ret{k2, e2}, rest}:
      Bool.or(Bool.and(keyEq(key, k2), edgeEq(edge, e2)), retIn(key, edge, rest))

def popIn(+key: CKey, +j: Nat, xs: +List<Pop>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{Pop{k2, j2}, rest}:
      Bool.or(Bool.and(keyEq(key, k2), Nat.is_eq(j, j2)), popIn(key, j, rest))

# ---- The grammar at a position ----

def reverseOnto(xs: +List<Nat>, +acc: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      reverseOnto(rest, x <> acc)

def nthItem(items: +List<Spec.Item>, n: Nat) -> Maybe<&2, Spec.Item>:
  match items n:
    case Nil{} _:
      None{}
    case Con{x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+m:
      nthItem(rest, m)

def bracketAlt(item: Maybe<&2, Spec.Item>, a: Nat) -> +List<Spec.Item>:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      Spec.altOf(alts, a)
    case _:
      []

# The sequence at a position: the right side, or an alternative of a bracket in it.
# The path is innermost first: alternative a of the bracket at item m of the outer
# sequence.
def seqAt(+grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>) -> +List<Spec.Item>:
  match rpath:
    case Con{a, Con{m, outer}}:
      bracketAlt(nthItem(seqAt(grammar, index, outer), m), a)
    case _:
      Spec.rhsOf(grammar, index)

def lhsOf(+grammar: +List<Spec.Production>, index: Nat) -> Nat:
  match grammar index:
    case Nil{} _:
      0n
    case Con{Spec.Production{lhs, rhs}, rest} 0n:
      lhs
    case Con{p, rest} 1n+n:
      lhsOf(rest, n)

# The step for the slot at (index, rpath, dot), as the specification writes it.
def stepAt(+index: Nat, +rpath: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Spec.Bsr:
  Spec.Bsr{Spec.Slot{index, reverseOnto(rpath, [dot])}, i, k, j}

# ---- Adding to the state ----

def descPick(known: Bool, +d: Desc, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, rs, ps, ys}:
      GState{d <> seen, d <> todo, cs, rs, ps, ys}

def withDesc(+d: Desc, s: GState) -> GState:
  match s:
    case GState{+seen, todo, cs, rs, ps, ys}:
      descPick(descIn(d, seen), d, GState{seen, todo, cs, rs, ps, ys})

def yieldPick(known: Bool, +y: Spec.Bsr, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, rs, ps, ys}:
      GState{seen, todo, cs, rs, ps, y <> ys}

def withYield(+y: Spec.Bsr, s: GState) -> GState:
  match s:
    case GState{seen, todo, cs, rs, ps, +ys}:
      yieldPick(Spec.bsrMember(y, ys), y, GState{seen, todo, cs, rs, ps, ys})

def withDescs(ds: +List<Desc>, s: GState) -> GState:
  match ds:
    case Nil{}:
      s
    case Con{+d, rest}:
      withDescs(rest, withDesc(d, s))

# Continue the caller of `edge` after its callee, which started at kc, ended at j.
def resume(+edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match edge:
    case Edge{+index, +rpath, +dot, +k}:
      withYield(stepAt(index, rpath, 1n+dot, k, kc, j), withDesc(Desc{index, rpath, 1n+dot, k, j}, s))

def resumeIf(hit: Bool, +edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match hit:
    case True{}:
      resume(edge, kc, j, s)
    case False{}:
      s

# Resume every caller of `key` at j.
def resumeAll(rets: +List<Ret>, +key: CKey, +kc: Nat, +j: Nat, s: GState) -> GState:
  match rets:
    case Nil{}:
      s
    case Con{Ret{+k2, +e2}, rest}:
      resumeAll(rest, key, kc, j, resumeIf(keyEq(key, k2), e2, kc, j, s))

# Resume one new caller at every place `key` has already ended.
def resumePops(pops: +List<Pop>, +key: CKey, +edge: Edge, +kc: Nat, s: GState) -> GState:
  match pops:
    case Nil{}:
      s
    case Con{Pop{+k2, +j}, rest}:
      resumePops(rest, key, edge, kc, resumeIf(keyEq(key, k2), edge, kc, j, s))

def callPick(known: Bool, known2: Bool, +key: CKey, +kc: Nat, +edge: Edge, +seeds: +List<Desc>, s: GState) -> GState:
  match known known2 s:
    case False{} _ GState{seen, todo, cs, rs, ps, ys}:
      withDescs(seeds, GState{seen, todo, key <> cs, Ret{key, edge} <> rs, ps, ys})
    case True{} True{} _:
      s
    case True{} False{} GState{seen, todo, cs, rs, +ps, ys}:
      resumePops(ps, key, edge, kc, GState{seen, todo, cs, Ret{key, edge} <> rs, ps, ys})

# Enter `target` at i, for the caller `edge`; `seeds` start its alternatives.
def call(+target: Target, +i: Nat, +edge: Edge, +seeds: +List<Desc>, s: GState) -> GState:
  match s:
    case GState{seen, todo, +cs, +rs, ps, ys}:
      +key = {CKey{target, i} : CKey}
      callPick(keyIn(key, cs), retIn(key, edge, rs), key, i, edge, seeds, GState{seen, todo, cs, rs, ps, ys})

def leavePick(known: Bool, +key: CKey, +kc: Nat, +j: Nat, +again: +List<Desc>, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, +rs, ps, ys}:
      withDescs(again, resumeAll(rs, key, kc, j, GState{seen, todo, cs, rs, Pop{key, j} <> ps, ys}))

# Leave the cluster `key`, which started at kc, at j; `again` re-enters a closure.
def leave(+key: CKey, +kc: Nat, +j: Nat, +again: +List<Desc>, s: GState) -> GState:
  match s:
    case GState{seen, todo, cs, rs, +ps, ys}:
      leavePick(popIn(key, j, ps), key, kc, j, again, GState{seen, todo, cs, rs, ps, ys})

# ---- One descriptor ----

def keepDesc(keep: Bool, +d: Desc, ds: +List<Desc>) -> +List<Desc>:
  match keep:
    case True{}:
      d <> ds
    case False{}:
      ds

def productionsOf(grammar: +List<Spec.Production>, +id: Nat, +index: Nat, +i: Nat) -> +List<Desc>:
  match grammar:
    case Nil{}:
      []
    case Con{Spec.Production{lhs, rhs}, rest}:
      keepDesc(Nat.is_eq(lhs, id), Desc{index, [], 0n, i, i}, productionsOf(rest, id, 1n+index, i))

# Start every alternative of the bracket at (index, rpath), counting down from n.
def alternatives(n: Nat, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat) -> +List<Desc>:
  match n:
    case 0n:
      []
    case 1n+(+a):
      Desc{index, a <> rpath, 0n, k, i} <> alternatives(a, index, rpath, k, i)

def tokenIs(token: Maybe<&2, Nat>, +t: Nat) -> Bool:
  match token:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, t)

def matchToken(ok: Bool, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match ok:
    case True{}:
      withYield(stepAt(index, rpath, 1n+dot, k, i, 1n+i), withDesc(Desc{index, rpath, 1n+dot, k, 1n+i}, s))
    case False{}:
      s

def isSkippable(kind: Spec.Bracket) -> Bool:
  match kind:
    case Spec.Optional{}:
      True{}
    case Spec.Closure{}:
      True{}
    case _:
      False{}

def isLoop(kind: Spec.Bracket) -> Bool:
  match kind:
    case Spec.Closure{}:
      True{}
    case Spec.Positive{}:
      True{}
    case _:
      False{}

def skipIf(skip: Bool, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match skip:
    case True{}:
      withYield(stepAt(index, rpath, 1n+dot, k, i, i), withDesc(Desc{index, rpath, 1n+dot, k, i}, s))
    case False{}:
      s

# The ε step of an empty sequence.
def emptyIf(dot: Nat, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat, s: GState) -> GState:
  match dot:
    case 0n:
      withYield(stepAt(index, rpath, 0n, k, i, i), s)
    case 1n+d:
      s

def againPick(loop: Bool, +n: Nat, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat) -> +List<Desc>:
  match loop:
    case True{}:
      alternatives(n, index, rpath, k, i)
    case False{}:
      []

# A closure starts its body again where the last round ended, in the same cluster.
def againOf(item: Maybe<&2, Spec.Item>, +index: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat) -> +List<Desc>:
  match item:
    case Some{Spec.Brack{+kind, +alts}}:
      againPick(isLoop(kind), List.length(&2, +List<Spec.Item>, alts), index, rpath, k, i)
    case _:
      []

# The end of a sequence: leave the production, or the bracket alternative.
def finish(+grammar: +List<Spec.Production>, +index: Nat, rpath: +List<Nat>, +k: Nat, +i: Nat, s: GState) -> GState:
  match rpath:
    case Con{a, Con{+m, +outer}}:
      leave(CKey{TBr{index, m <> outer}, k}, k, i, againOf(nthItem(seqAt(grammar, index, outer), m), index, m <> outer, k, i), s)
    case _:
      leave(CKey{TNt{lhsOf(grammar, index)}, k}, k, i, [], s)

def stepItem(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      matchToken(tokenIs(List.get(&2, Nat, input, i), t), index, rpath, dot, k, i, s)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      call(TNt{x}, i, Edge{index, rpath, dot, k}, productionsOf(grammar, x, 0n, i), s)
    case Some{Spec.Brack{+kind, +alts}}:
      skipIf(isSkippable(kind), index, rpath, dot, k, i,
        call(TBr{index, dot <> rpath}, i, Edge{index, rpath, dot, k}, alternatives(List.length(&2, +List<Spec.Item>, alts), index, dot <> rpath, i, i), s))
    case Some{Spec.Eps{}}:
      skipIf(True{}, index, rpath, dot, k, i, s)
    case None{}:
      finish(grammar, index, rpath, k, i, emptyIf(dot, index, rpath, k, i, s))

def step(d: Desc, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: GState) -> GState:
  match d:
    case Desc{+index, +rpath, +dot, +k, +i}:
      stepItem(nthItem(seqAt(grammar, index, rpath), dot), grammar, input, index, rpath, dot, k, i, s)

# ---- The loop ----

type GRun is Data:
  GDone{state: GState}
  OutOfFuel{state: GState}

def run(fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: GState) -> GRun:
  match fuel s:
    case 0n _:
      OutOfFuel{s}
    case 1n+f GState{seen, Nil{}, cs, rs, ps, ys}:
      GDone{GState{seen, [], cs, rs, ps, ys}}
    case 1n+f GState{seen, Con{d, rest}, cs, rs, ps, ys}:
      run(f, grammar, input, step(d, grammar, input, GState{seen, rest, cs, rs, ps, ys}))

# Parse the input from the start symbol: its cluster at 0, and its productions.
def parse(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> GRun:
  run(fuel, grammar, input, withDescs(productionsOf(grammar, start, 0n, 0n), GState{[], [], [CKey{TNt{start}, 0n}], [], [], []}))

def yieldsOf(r: GRun) -> +List<Spec.Bsr>:
  match r:
    case GDone{GState{seen, todo, cs, rs, ps, ys}}:
      ys
    case OutOfFuel{state}:
      []

# Accepted when the start symbol ended at the end of the input.
def accepts(r: GRun, +start: Nat, +n: Nat) -> Bool:
  match r:
    case GDone{GState{seen, todo, cs, rs, ps, ys}}:
      popIn(CKey{TNt{start}, 0n}, n, ps)
    case OutOfFuel{state}:
      False{}
