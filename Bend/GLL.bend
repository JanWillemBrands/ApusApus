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

# ---- Prediction (Scott's predict sets) ----
#
# A lookahead set: some token kinds, and whether the end of the input may come next.
# `any` is the set of everything, the safe answer when nesting runs out of fuel.
type LSet is Data:
  LSet{any: Bool, toks: +List<Nat>, end: Bool}

# Per nonterminal, by id: can it derive nothing, which tokens can start it, and which
# can follow it. Computed and checked in FIRST.bend.
type Tables is Data:
  Tables{nul: +List<Bool>, fst: +List<LSet>, fol: +List<LSet>}

# Plain GLL, or GLL that starts a descriptor only where its predict set admits the token.
type Pred is Data:
  NoPred{}
  Predict{tables: Tables}

# What a sequence or a bracket's alternatives can do: derive nothing, and start with.
type Info is Data:
  Info{nul: Bool, first: LSet}

type Mode is Data:
  MItems{}
  MAlts{}

def natIn(+x: Nat, xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(x, y), natIn(x, rest))

def natAddPick(here: Bool, +x: Nat, ys: +List<Nat>) -> +List<Nat>:
  match here:
    case True{}:
      ys
    case False{}:
      x <> ys

def natsUnion(xs: +List<Nat>, +ys: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{+x, rest}:
      +zs = natsUnion(rest, ys)
      natAddPick(natIn(x, zs), x, zs)

def emptyLS() -> LSet:
  LSet{False{}, [], False{}}

def lsUnion(a: LSet, b: LSet) -> LSet:
  match a b:
    case LSet{a1, t1, e1} LSet{a2, +t2, e2}:
      LSet{Bool.or(a1, a2), natsUnion(t1, t2), Bool.or(e1, e2)}

def lsIf(b: Bool, s: LSet) -> LSet:
  match b:
    case True{}:
      s
    case False{}:
      emptyLS()

# Does the set admit the next token (None: the end of the input)?
def lsHas(token: Maybe<&2, Nat>, s: LSet) -> Bool:
  match token s:
    case None{} LSet{any, toks, end}:
      Bool.or(any, end)
    case Some{+t} LSet{any, toks, end}:
      Bool.or(any, natIn(t, toks))

def boolAt(bs: +List<Bool>, x: Nat) -> Bool:
  match bs x:
    case Nil{} _:
      False{}
    case Con{b, rest} 0n:
      b
    case Con{b, rest} 1n+y:
      boolAt(rest, y)

def lsAt(ls: +List<LSet>, x: Nat) -> LSet:
  match ls x:
    case Nil{} _:
      emptyLS()
    case Con{l, rest} 0n:
      l
    case Con{l, rest} 1n+y:
      lsAt(rest, y)

def nulTab(t: Tables) -> +List<Bool>:
  match t:
    case Tables{nul, fst, fol}:
      nul

def fstTab(t: Tables) -> +List<LSet>:
  match t:
    case Tables{nul, fst, fol}:
      fst

def folTab(t: Tables) -> +List<LSet>:
  match t:
    case Tables{nul, fst, fol}:
      fol

def isRepeat(kind: Spec.Bracket) -> Bool:
  match kind:
    case Spec.Closure{}:
      True{}
    case Spec.Positive{}:
      True{}
    case _:
      False{}

def canSkip(kind: Spec.Bracket) -> Bool:
  match kind:
    case Spec.Optional{}:
      True{}
    case Spec.Closure{}:
      True{}
    case _:
      False{}

# An item followed by a sequence.
def infoCons(head: Info, rest: Info) -> Info:
  match head rest:
    case Info{True{}, f1} Info{n2, f2}:
      Info{n2, lsUnion(f1, f2)}
    case Info{False{}, f1} Info{n2, f2}:
      Info{False{}, f1}

# One alternative more.
def infoOr(a: Info, b: Info) -> Info:
  match a b:
    case Info{n1, f1} Info{n2, f2}:
      Info{Bool.or(n1, n2), lsUnion(f1, f2)}

def infoBracket(kind: Spec.Bracket, a: Info) -> Info:
  match a:
    case Info{n, f}:
      Info{Bool.or(canSkip(kind), n), f}

# One def for sequences (MItems) and a bracket's alternatives (MAlts), since Bend has no
# mutual recursion. `fuel` counts nesting; when it runs out the answer is everything,
# which is safe for prediction.
def infoOf(fuel: Nat, mode: Mode, items: +List<Spec.Item>, alts: +List<+List<Spec.Item>>, +t: Tables) -> Info:
  match fuel mode items alts:
    case 0n _ _ _:
      Info{True{}, LSet{True{}, [], True{}}}
    case 1n+(+f) MItems{} Nil{} _:
      Info{True{}, emptyLS()}
    case 1n+(+f) MItems{} Con{Spec.Eps{}, rest} _:
      infoOf(1n+f, MItems{}, rest, alts, t)
    case 1n+(+f) MItems{} Con{Spec.Sym{Spec.Terminal{k}}, rest} _:
      Info{False{}, LSet{False{}, [k], False{}}}
    case 1n+(+f) MItems{} Con{Spec.Sym{Spec.Nonterminal{+x}}, rest} _:
      infoCons(Info{boolAt(nulTab(t), x), lsAt(fstTab(t), x)}, infoOf(1n+f, MItems{}, rest, alts, t))
    case 1n+(+f) MItems{} Con{Spec.Brack{kind, inner}, rest} _:
      infoCons(infoBracket(kind, infoOf(f, MAlts{}, [], inner, t)), infoOf(1n+f, MItems{}, rest, alts, t))
    case 1n+(+f) MAlts{} _ Nil{}:
      Info{False{}, emptyLS()}
    case 1n+(+f) MAlts{} _ Con{alt, rest}:
      infoOr(infoOf(f, MItems{}, alt, [], t), infoOf(1n+f, MAlts{}, items, rest, t))

def nestFuel() -> Nat:
  64n

def infoItems(items: +List<Spec.Item>, +t: Tables) -> Info:
  infoOf(nestFuel(), MItems{}, items, [], t)

def infoAlts(alts: +List<+List<Spec.Item>>, +t: Tables) -> Info:
  infoOf(nestFuel(), MAlts{}, [], alts, t)

def firstOf(i: Info) -> LSet:
  match i:
    case Info{n, f}:
      f

def nulOf(i: Info) -> Bool:
  match i:
    case Info{n, f}:
      n

def dropFrom(n: Nat, items: +List<Spec.Item>) -> +List<Spec.Item>:
  match n items:
    case 0n _:
      items
    case 1n+m Nil{}:
      []
    case 1n+m Con{x, rest}:
      dropFrom(m, rest)

def loopFirst(item: Maybe<&2, Spec.Item>, +t: Tables) -> LSet:
  match item:
    case Some{Spec.Brack{kind, +alts}}:
      lsIf(isRepeat(kind), firstOf(infoAlts(alts, t)))
    case _:
      emptyLS()

def restOr(+i: Info, after: LSet) -> LSet:
  lsUnion(firstOf(i), lsIf(nulOf(i), after))

# What may come after the end of the sequence at (index, rpath): for a production, its
# nonterminal's FOLLOW; for a bracket's alternative, another round of a loop, or what
# comes after the bracket in the sequence around it.
def contextAfter(+grammar: +List<Spec.Production>, +t: Tables, +index: Nat, rpath: +List<Nat>) -> LSet:
  match rpath:
    case Con{a, Con{+m, +outer}}:
      +outerSeq = seqAt(grammar, index, outer)
      +rest = infoItems(dropFrom(1n+m, outerSeq), t)
      lsUnion(loopFirst(nthItem(outerSeq, m), t), restOr(rest, contextAfter(grammar, t, index, outer)))
    case _:
      lsAt(folTab(t), lhsOf(grammar, index))

# The predict set of the slot after `dot` items of the sequence at (index, rpath).
def predictAt(+grammar: +List<Spec.Production>, +t: Tables, +index: Nat, +rpath: +List<Nat>, dot: Nat) -> LSet:
  restOr(infoItems(dropFrom(dot, seqAt(grammar, index, rpath)), t), contextAfter(grammar, t, index, rpath))

# Must a round of the bracket at this item read something (the bracket rule, SPEC.bend's
# `roundsOk`)? Rounds of [ ] and { } always do; so do the rounds of < > after the first,
# that is, those that do not start where the loop starts (k, the loop's start; i, the
# round's).
def roundReads(item: Maybe<&2, Spec.Item>, +k: Nat, +i: Nat) -> Bool:
  match item:
    case Some{Spec.Brack{Spec.Optional{}, alts}}:
      True{}
    case Some{Spec.Brack{Spec.Closure{}, alts}}:
      True{}
    case Some{Spec.Brack{Spec.Positive{}, alts}}:
      Bool.not(Nat.is_eq(k, i))
    case Some{Spec.Brack{Spec.Group{}, alts}}:
      False{}
    case Some{Spec.Sym{s}}:
      False{}
    case Some{Spec.Eps{}}:
      False{}
    case None{}:
      False{}

def roundPick(reads: Bool, +grammar: +List<Spec.Production>, +t: Tables, +index: Nat, +rpath: +List<Nat>) -> LSet:
  match reads:
    case True{}:
      firstOf(infoItems(seqAt(grammar, index, rpath), t))
    case False{}:
      predictAt(grammar, t, index, rpath, 0n)

# The predict set of a descriptor: at the start of a round that must read something,
# FIRST of the round alone (an empty round there is no tree, so it is not started);
# elsewhere the predict set of its slot.
def predictFor(+grammar: +List<Spec.Production>, +t: Tables, +index: Nat, dot: Nat, +rpath: +List<Nat>, +k: Nat, +i: Nat) -> LSet:
  match dot rpath:
    case 0n Con{+a, Con{+m, +outer}}:
      roundPick(roundReads(nthItem(seqAt(grammar, index, outer), m), k, i), grammar, t, index, a <> (m <> outer))
    case 0n Con{+a, Nil{}}:
      predictAt(grammar, t, index, [a], 0n)
    case 0n Nil{}:
      predictAt(grammar, t, index, [], 0n)
    case 1n+(+d) _:
      predictAt(grammar, t, index, rpath, 1n+d)

# May the descriptor be started? Always without prediction.
def admits(pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, d: Desc) -> Bool:
  match pr d:
    case NoPred{} _:
      True{}
    case Predict{+t} Desc{+index, +rpath, +dot, +k, +i}:
      lsHas(List.get(&2, Nat, input, i), predictFor(grammar, t, index, dot, rpath, k, i))

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

def admitPick(ok: Bool, +d: Desc, s: GState) -> GState:
  match ok:
    case True{}:
      withDesc(d, s)
    case False{}:
      s

# A descriptor, if its predict set admits the token there.
def withDescP(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +d: Desc, s: GState) -> GState:
  admitPick(admits(pr, grammar, input, d), d, s)

def withDescsP(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, ds: +List<Desc>, s: GState) -> GState:
  match ds:
    case Nil{}:
      s
    case Con{+d, rest}:
      withDescsP(pr, grammar, input, rest, withDescP(pr, grammar, input, d, s))

def pairPick(ok: Bool, +d: Desc, +y: Spec.Bsr, s: GState) -> GState:
  match ok:
    case True{}:
      withYield(y, withDesc(d, s))
    case False{}:
      s

# A descriptor with the step that leads to it, both only if the descriptor is admitted.
def withPairP(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +d: Desc, +y: Spec.Bsr, s: GState) -> GState:
  pairPick(admits(pr, grammar, input, d), d, y, s)

# Continue the caller of `edge` after its callee, which started at kc, ended at j.
def resume(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match edge:
    case Edge{+index, +rpath, +dot, +k}:
      withPairP(pr, grammar, input, Desc{index, rpath, 1n+dot, k, j}, stepAt(index, rpath, 1n+dot, k, kc, j), s)

def resumeIf(hit: Bool, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +edge: Edge, +kc: Nat, +j: Nat, s: GState) -> GState:
  match hit:
    case True{}:
      resume(pr, grammar, input, edge, kc, j, s)
    case False{}:
      s

# Resume every caller of `key` at j.
def resumeAll(rets: +List<Ret>, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: CKey, +kc: Nat, +j: Nat, s: GState) -> GState:
  match rets:
    case Nil{}:
      s
    case Con{Ret{+k2, +e2}, rest}:
      resumeAll(rest, pr, grammar, input, key, kc, j, resumeIf(keyEq(key, k2), pr, grammar, input, e2, kc, j, s))

# Resume one new caller at every place `key` has already ended.
def resumePops(pops: +List<Pop>, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: CKey, +edge: Edge, +kc: Nat, s: GState) -> GState:
  match pops:
    case Nil{}:
      s
    case Con{Pop{+k2, +j}, rest}:
      resumePops(rest, pr, grammar, input, key, edge, kc, resumeIf(keyEq(key, k2), pr, grammar, input, edge, kc, j, s))

def callPick(known: Bool, known2: Bool, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: CKey, +kc: Nat, +edge: Edge, +seeds: +List<Desc>, s: GState) -> GState:
  match known known2 s:
    case False{} _ GState{seen, todo, cs, rs, ps, ys}:
      withDescsP(pr, grammar, input, seeds, GState{seen, todo, key <> cs, Ret{key, edge} <> rs, ps, ys})
    case True{} True{} _:
      s
    case True{} False{} GState{seen, todo, cs, rs, +ps, ys}:
      resumePops(ps, pr, grammar, input, key, edge, kc, GState{seen, todo, cs, Ret{key, edge} <> rs, ps, ys})

# Enter `target` at i, for the caller `edge`; `seeds` start its alternatives.
def call(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +target: Target, +i: Nat, +edge: Edge, +seeds: +List<Desc>, s: GState) -> GState:
  match s:
    case GState{seen, todo, +cs, +rs, ps, ys}:
      +key = {CKey{target, i} : CKey}
      callPick(keyIn(key, cs), retIn(key, edge, rs), pr, grammar, input, key, i, edge, seeds, GState{seen, todo, cs, rs, ps, ys})

def leavePick(known: Bool, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: CKey, +kc: Nat, +j: Nat, +again: +List<Desc>, s: GState) -> GState:
  match known s:
    case True{} _:
      s
    case False{} GState{seen, todo, cs, +rs, ps, ys}:
      withDescsP(pr, grammar, input, again, resumeAll(rs, pr, grammar, input, key, kc, j, GState{seen, todo, cs, rs, Pop{key, j} <> ps, ys}))

# Leave the cluster `key`, which started at kc, at j; `again` re-enters a closure.
def leave(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +key: CKey, +kc: Nat, +j: Nat, +again: +List<Desc>, s: GState) -> GState:
  match s:
    case GState{seen, todo, cs, rs, +ps, ys}:
      leavePick(popIn(key, j, ps), pr, grammar, input, key, kc, j, again, GState{seen, todo, cs, rs, ps, ys})

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

def matchToken(ok: Bool, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match ok:
    case True{}:
      withPairP(pr, grammar, input, Desc{index, rpath, 1n+dot, k, 1n+i}, stepAt(index, rpath, 1n+dot, k, i, 1n+i), s)
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

def skipIf(skip: Bool, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match skip:
    case True{}:
      withPairP(pr, grammar, input, Desc{index, rpath, 1n+dot, k, i}, stepAt(index, rpath, 1n+dot, k, i, i), s)
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
def finish(+pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, rpath: +List<Nat>, +k: Nat, +i: Nat, s: GState) -> GState:
  match rpath:
    case Con{a, Con{+m, +outer}}:
      leave(pr, grammar, input, CKey{TBr{index, m <> outer}, k}, k, i, againOf(nthItem(seqAt(grammar, index, outer), m), index, m <> outer, k, i), s)
    case _:
      leave(pr, grammar, input, CKey{TNt{lhsOf(grammar, index)}, k}, k, i, [], s)

def stepItem(item: Maybe<&2, Spec.Item>, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +k: Nat, +i: Nat, s: GState) -> GState:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      matchToken(tokenIs(List.get(&2, Nat, input, i), t), pr, grammar, input, index, rpath, dot, k, i, s)
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      call(pr, grammar, input, TNt{x}, i, Edge{index, rpath, dot, k}, productionsOf(grammar, x, 0n, i), s)
    case Some{Spec.Brack{+kind, +alts}}:
      skipIf(isSkippable(kind), pr, grammar, input, index, rpath, dot, k, i,
        call(pr, grammar, input, TBr{index, dot <> rpath}, i, Edge{index, rpath, dot, k}, alternatives(List.length(&2, +List<Spec.Item>, alts), index, dot <> rpath, i, i), s))
    case Some{Spec.Eps{}}:
      skipIf(True{}, pr, grammar, input, index, rpath, dot, k, i, s)
    case None{}:
      finish(pr, grammar, input, index, rpath, k, i, emptyIf(dot, index, rpath, k, i, s))

def step(d: Desc, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: GState) -> GState:
  match d:
    case Desc{+index, +rpath, +dot, +k, +i}:
      stepItem(nthItem(seqAt(grammar, index, rpath), dot), pr, grammar, input, index, rpath, dot, k, i, s)

# ---- The loop ----

type GRun is Data:
  GDone{state: GState}
  OutOfFuel{state: GState}

def run(fuel: Nat, +pr: Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, s: GState) -> GRun:
  match fuel s:
    case 0n _:
      OutOfFuel{s}
    case 1n+f GState{seen, Nil{}, cs, rs, ps, ys}:
      GDone{GState{seen, [], cs, rs, ps, ys}}
    case 1n+f GState{seen, Con{d, rest}, cs, rs, ps, ys}:
      run(f, pr, grammar, input, step(d, pr, grammar, input, GState{seen, rest, cs, rs, ps, ys}))

# Parse the input from the start symbol: its cluster at 0, and its productions.
def parseWith(fuel: Nat, +pr: Pred, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> GRun:
  run(fuel, pr, grammar, input, withDescsP(pr, grammar, input, productionsOf(grammar, start, 0n, 0n), GState{[], [], [CKey{TNt{start}, 0n}], [], [], []}))

def parse(fuel: Nat, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> GRun:
  parseWith(fuel, NoPred{}, grammar, start, input)

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
