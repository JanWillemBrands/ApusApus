import Base
import ./CORE.bend as Core

# A GLL PARSER FOR THE CORE (reference engine, not verified: CHECK.bend checks its results).
#
# A descriptor Desc{index, dot, k, i}: in production `index`, whose node started at k, the
# items before `dot` have read up to i. A cluster CKey{x, i} is nonterminal x called at i;
# its return edges say which slots to continue, its pops where it has ended. Return edges
# are added without looking for an existing one: a call happens only while a descriptor is
# processed, its edge is fixed by that descriptor, and no descriptor is processed twice
# (Afroozeh and Izmaylova 2015; proven for today's engine, documentation/drafts/AFROOZEH.bend).

type Desc is Data:
  Desc{index: Nat, dot: Nat, k: Nat, i: Nat}

type CKey is Data:
  CKey{x: Nat, i: Nat}

# Where to continue after a call: the calling slot (before the nonterminal at `dot`), and
# where the caller's node started.
type Edge is Data:
  Edge{index: Nat, dot: Nat, k: Nat}

type Ret is Data:
  Ret{key: CKey, edge: Edge}

type Pop is Data:
  Pop{key: CKey, j: Nat}

type GState is Data:
  GState{seen: +List<Desc>, todo: +List<Desc>, clusters: +List<CKey>, returns: +List<Ret>, pops: +List<Pop>, steps: +List<Core.Bsr>}

# ======== EQUALITY AND MEMBERSHIP ========

def descEq(a: Desc, b: Desc) -> Bool:
  match a b:
    case Desc{q1, d1, k1, i1} Desc{q2, d2, k2, i2}:
      Bool.and(Nat.is_eq(q1, q2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(i1, i2))))

def keyEq(a: CKey, b: CKey) -> Bool:
  match a b:
    case CKey{x1, i1} CKey{x2, i2}:
      Bool.and(Nat.is_eq(x1, x2), Nat.is_eq(i1, i2))

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

def popIn(+key: CKey, +j: Nat, xs: +List<Pop>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{Pop{k2, j2}, rest}:
      Bool.or(Bool.and(keyEq(key, k2), Nat.is_eq(j, j2)), popIn(key, j, rest))

# ======== THE GRAMMAR ========

def nthSym(items: +List<Core.Sym>, n: Nat) -> Maybe<&2, Core.Sym>:
  match items n:
    case Nil{} _:
      None{}
    case Con{+x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+m:
      nthSym(rest, m)

def lhsOf(+grammar: +List<Core.Production>, index: Nat) -> Nat:
  match grammar index:
    case Nil{} _:
      0n
    case Con{Core.Production{+lhs, rhs}, rest} 0n:
      lhs
    case Con{p, rest} 1n+n:
      lhsOf(rest, n)

def keepDesc(keep: Bool, +d: Desc, ds: +List<Desc>) -> +List<Desc>:
  match keep:
    case True{}:
      d <> ds
    case False{}:
      ds

# Prediction (Scott's predict sets): NoPred starts every production; Allowed starts
# production `index` only when the next token is in its set (None: the end of the input).
type Pred is Data:
  NoPred{}
  Allowed{sets: +List<+List<Maybe<&2, Nat>>>}

def tokEq(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{+x} Some{+y}:
      Nat.is_eq(x, y)
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}

def tokIn(+t: Maybe<&2, Nat>, xs: +List<Maybe<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(tokEq(t, y), tokIn(t, rest))

def setAt(sets: +List<+List<Maybe<&2, Nat>>>, n: Nat) -> +List<Maybe<&2, Nat>>:
  match sets n:
    case Nil{} _:
      []
    case Con{+x, rest} 0n:
      x
    case Con{x, +rest} 1n+(+m):
      setAt(rest, m)

def admits(pred: Pred, +index: Nat, +tok: Maybe<&2, Nat>) -> Bool:
  match pred:
    case NoPred{}:
      True{}
    case Allowed{+sets}:
      tokIn(tok, setAt(sets, index))

# The descriptors that start nonterminal x's productions at i, where the next token is tok.
def productionsOf(grammar: +List<Core.Production>, +pred: Pred, +tok: Maybe<&2, Nat>, +x: Nat, +index: Nat, +i: Nat) -> +List<Desc>:
  match grammar:
    case Nil{}:
      []
    case Con{Core.Production{lhs, rhs}, rest}:
      keepDesc(Bool.and(admits(pred, index, tok), Nat.is_eq(lhs, x)), Desc{index, 0n, i, i}, productionsOf(rest, pred, tok, x, 1n+index, i))

# The need of the nonterminal before the slot after `dot` items of production `index`.
def needOf(item: Maybe<&2, Core.Sym>) -> Core.Need:
  match item:
    case Some{Core.Nonterminal{x, +need}}:
      need
    case _:
      Core.Anything{}

def needAt(+grammar: +List<Core.Production>, +index: Nat, +dot: Nat) -> Core.Need:
  needOf(nthSym(Core.rhsOf(grammar, index), dot))

# Does a callee that started at kc and ended at j keep the occurrence's need?
def needHolds(need: Core.Need, +kc: Nat, +j: Nat) -> Bool:
  match need:
    case Core.Anything{}:
      True{}
    case Core.Something{}:
      Bool.not(Nat.is_eq(kc, j))
    case Core.Nothing{}:
      Nat.is_eq(kc, j)

# ======== THE RULES ========

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

def stepPick(known: Bool, +y: Core.Bsr, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, rs, ps, ys}:
      GState{seen, todo, cs, rs, ps, y <> ys}

def withStep(+y: Core.Bsr, s: GState) -> GState:
  match s:
    case GState{seen, todo, cs, rs, ps, +ys}:
      stepPick(Core.member(y, ys), y, GState{seen, todo, cs, rs, ps, ys})

def withDescs(ds: +List<Desc>, s: GState) -> GState:
  match ds:
    case Nil{}:
      s
    case Con{+d, rest}:
      withDescs(rest, withDesc(d, s))

def resumePick(ok: Bool, +index: Nat, +dot: Nat, +k: Nat, +kc: Nat, +j: Nat, s: GState) -> GState:
  match ok:
    case True{}:
      withStep(Core.Bsr{index, 1n+dot, k, kc, j}, withDesc(Desc{index, 1n+dot, k, j}, s))
    case False{}:
      s

# Continue the caller of `edge` after its callee, which started at kc and ended at j, when
# that keeps the occurrence's need.
def resume(+grammar: +List<Core.Production>, +edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match edge:
    case Edge{+index, +dot, +k}:
      resumePick(needHolds(needAt(grammar, index, dot), kc, j), index, dot, k, kc, j, s)

def resumeIf(hit: Bool, +grammar: +List<Core.Production>, +edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match hit:
    case True{}:
      resume(grammar, edge, kc, j, s)
    case False{}:
      s

# Resume every caller of `key` at j.
def resumeAll(rets: +List<Ret>, +grammar: +List<Core.Production>, +key: CKey, +j: Nat, s: GState) -> GState:
  match rets key:
    case Nil{} _:
      s
    case Con{Ret{+k2, +e2}, rest} CKey{+x, +kc}:
      resumeAll(rest, grammar, key, j, resumeIf(keyEq(key, k2), grammar, e2, kc, j, s))

# Resume one new caller at every place `key` has already ended.
def resumePops(pops: +List<Pop>, +grammar: +List<Core.Production>, +key: CKey, +edge: Edge, s: GState) -> GState:
  match pops key:
    case Nil{} _:
      s
    case Con{Pop{+k2, +j}, rest} CKey{+x, +kc}:
      resumePops(rest, grammar, key, edge, resumeIf(keyEq(key, k2), grammar, edge, kc, j, s))

def callPick(known: Bool, +grammar: +List<Core.Production>, +key: CKey, +edge: Edge, +seeds: +List<Desc>, s: GState) -> GState:
  match known s:
    case False{} GState{seen, todo, cs, rs, ps, ys}:
      withDescs(seeds, GState{seen, todo, key <> cs, Ret{key, edge} <> rs, ps, ys})
    case True{} GState{seen, todo, cs, rs, +ps, ys}:
      resumePops(ps, grammar, key, edge, GState{seen, todo, cs, Ret{key, edge} <> rs, ps, ys})

# Call x at i for the caller `edge`.
def call(+pred: Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +x: Nat, +i: Nat, +edge: Edge, s: GState) -> GState:
  match s:
    case GState{seen, todo, +cs, rs, ps, ys}:
      +key = {CKey{x, i} : CKey}
      callPick(keyIn(key, cs), grammar, key, edge, productionsOf(grammar, pred, Core.tokAt(input, i), x, 0n, i), GState{seen, todo, cs, rs, ps, ys})

def leavePick(known: Bool, +grammar: +List<Core.Production>, +key: CKey, +j: Nat, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, +rs, ps, ys}:
      resumeAll(rs, grammar, key, j, GState{seen, todo, cs, rs, Pop{key, j} <> ps, ys})

# Leave the cluster `key` at j.
def leave(+grammar: +List<Core.Production>, +key: CKey, +j: Nat, s: GState) -> GState:
  match s:
    case GState{seen, todo, cs, rs, +ps, ys}:
      leavePick(popIn(key, j, ps), grammar, key, j, GState{seen, todo, cs, rs, ps, ys})

def matchToken(ok: Bool, +index: Nat, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match ok:
    case True{}:
      withStep(Core.Bsr{index, 1n+dot, k, i, 1n+i}, withDesc(Desc{index, 1n+dot, k, 1n+i}, s))
    case False{}:
      s

# The one step of an empty right side.
def emptyIf(dot: Nat, +index: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match dot:
    case 0n:
      withStep(Core.Bsr{index, 0n, k, i, i}, s)
    case 1n+d:
      s

def stepItem(item: Maybe<&2, Core.Sym>, +pred: Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, +index: Nat, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match item:
    case Some{Core.Terminal{+t}}:
      matchToken(Core.tokIs(Core.tokAt(input, i), t), index, dot, k, i, s)
    case Some{Core.Nonterminal{+x, need}}:
      call(pred, grammar, input, x, i, Edge{index, dot, k}, s)
    case None{}:
      leave(grammar, CKey{lhsOf(grammar, index), k}, i, emptyIf(dot, index, k, i, s))

def step(d: Desc, +pred: Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, s: GState) -> GState:
  match d:
    case Desc{+index, +dot, +k, +i}:
      stepItem(nthSym(Core.rhsOf(grammar, index), dot), pred, grammar, input, index, dot, k, i, s)

# ======== THE LOOP ========

type GRun is Data:
  GDone{state: GState}
  OutOfFuel{state: GState}

def run(fuel: Nat, +pred: Pred, +grammar: +List<Core.Production>, +input: +List<Nat>, s: GState) -> GRun:
  match fuel s:
    case 0n _:
      OutOfFuel{s}
    case 1n+f GState{seen, Nil{}, cs, rs, ps, ys}:
      GDone{GState{seen, [], cs, rs, ps, ys}}
    case 1n+f GState{seen, Con{d, rest}, cs, rs, ps, ys}:
      run(f, pred, grammar, input, step(d, pred, grammar, input, GState{seen, rest, cs, rs, ps, ys}))

# Parse the input from the start symbol: its cluster at 0, and its productions.
def parseWith(fuel: Nat, +pred: Pred, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> GRun:
  run(fuel, pred, grammar, input, withDescs(productionsOf(grammar, pred, Core.tokAt(input, 0n), start, 0n, 0n), GState{[], [], [CKey{start, 0n}], [], [], []}))

def parse(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> GRun:
  parseWith(fuel, NoPred{}, grammar, start, input)
