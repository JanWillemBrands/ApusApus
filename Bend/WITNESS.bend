import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll

# WITNESS TREES (not trusted): parse trees built from the pruned steps, so that every kept
# step shows up in one of them. EXACT.bend checks each tree against CORE.bend's `reads`.
#
# A fact is one forest for a segment: the first `dot` children of a node of production q
# that started at ks and ends at `end`, with a flag saying whether the forest contains the
# target step. There is at most one fact per segment and flag, so the facts are finite and
# a cyclic grammar needs no special care; they are found as a least fixpoint over the kept
# steps. The empty prefix of a non-empty right side is a fact without being found; a node
# of an empty right side is found from its empty step, so every tree uses only kept steps.

type Fact is Data:
  Fact{q: Nat, ks: Nat, dot: Nat, end: Nat, flag: Bool, forest: +List<Core.Tree>}

# A forest found for a segment, with its flag.
type Opt is Data:
  Opt{flag: Bool, forest: +List<Core.Tree>}

def boolEq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def sameKey(+q: Nat, +ks: Nat, +dot: Nat, +end: Nat, f: Fact) -> Bool:
  match f:
    case Fact{q2, ks2, d2, e2, fl, fo}:
      Bool.and(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(dot, d2), Nat.is_eq(end, e2))))

def flagOf(f: Fact) -> Bool:
  match f:
    case Fact{q, ks, d, e, +fl, fo}:
      fl

def hasFact(+q: Nat, +ks: Nat, +dot: Nat, +end: Nat, +flag: Bool, facts: +List<Fact>) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Con{+f, rest}:
      Bool.or(Bool.and(sameKey(q, ks, dot, end, f), boolEq(flag, flagOf(f))), hasFact(q, ks, dot, end, flag, rest))

def optIf(b: Bool, +o: Opt, os: +List<Opt>) -> +List<Opt>:
  match b:
    case True{}:
      o <> os
    case False{}:
      os

def optOf(f: Fact) -> Opt:
  match f:
    case Fact{q, ks, d, e, +fl, +fo}:
      Opt{fl, fo}

# The facts of a segment, found ones only.
def foundAt(+q: Nat, +ks: Nat, +dot: Nat, +end: Nat, facts: +List<Fact>) -> +List<Opt>:
  match facts:
    case Nil{}:
      []
    case Con{+f, rest}:
      optIf(sameKey(q, ks, dot, end, f), optOf(f), foundAt(q, ks, dot, end, rest))

# The empty prefix of a non-empty right side: no children, at the node's start.
def startIf(atStart: Bool) -> +List<Opt>:
  match atStart:
    case True{}:
      [Opt{False{}, []}]
    case False{}:
      []

# At dot 0: a node of an empty right side is a fact found from its one step (the empty
# step must be in the set); any other node starts with the empty prefix.
def zeroOpts(empty: Bool, +q: Nat, +ks: Nat, +end: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match empty:
    case True{}:
      foundAt(q, ks, 0n, end, facts)
    case False{}:
      startIf(Nat.is_eq(ks, end))

def optsAt(+grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, dot: Nat, +end: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match dot:
    case 0n:
      zeroOpts(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), q, ks, end, facts)
    case 1n+(+d):
      foundAt(q, ks, 1n+d, end, facts)

# ---- One round of rules ----

def withTree(+tree: Core.Tree, +flag: Bool, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+f1, +fo}, rest}:
      Opt{Bool.or(f1, flag), List.append(&2, Core.Tree, fo, [tree])} <> withTree(tree, flag, rest)

def withTreeList(t: +List<Core.Tree>, +flag: Bool, +os: +List<Opt>) -> +List<Opt>:
  match t:
    case Con{+tree, Nil{}}:
      withTree(tree, flag, os)
    case _:
      []


# Every prefix forest followed by every item option.
def joinAll(+prefixes: +List<Opt>, items: +List<Opt>) -> +List<Opt>:
  match items:
    case Nil{}:
      []
    case Con{Opt{+f2, +t}, rest}:
      List.append(&2, Opt, withTreeList(t, f2, prefixes), joinAll(prefixes, rest))

# Items are single trees, carried as one-tree forests.
def nodeOpts(+q2: Nat, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+f, +fo}, rest}:
      Opt{f, [Core.Node{q2, fo}]} <> nodeOpts(q2, rest)

def prodPick(hit: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +index: Nat, +len: Nat, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match hit:
    case True{}:
      nodeOpts(index, optsAt(grammar, target, index, k, len, j, facts))
    case False{}:
      []


# A nonterminal x over k .. j: a node for each production of x with a whole forest there.
def prodOpts(prods: +List<Core.Production>, +grammar: +List<Core.Production>, +target: Core.Bsr, +index: Nat, +x: Nat, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match prods:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, +rhs}, rest}:
      List.append(&2, Opt, prodPick(Nat.is_eq(lhs, x), grammar, target, index, List.length(&2, Core.Sym, rhs), k, j, facts), prodOpts(rest, grammar, target, 1n+index, x, k, j, facts))

def leafIf(ok: Bool, +t: Nat) -> +List<Opt>:
  match ok:
    case True{}:
      [Opt{False{}, [Core.Leaf{t}]}]
    case False{}:
      []

def needIf(ok: Bool, os: +List<Opt>) -> +List<Opt>:
  match ok:
    case True{}:
      os
    case False{}:
      []

def itemOpts(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +k: Nat, +j: Nat, +facts: +List<Fact>) -> +List<Opt>:
  match item:
    case Some{Core.Terminal{+t}}:
      leafIf(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)), t)
    case Some{Core.Nonterminal{+x, +need}}:
      needIf(Gll.needHolds(need, k, j), prodOpts(grammar, grammar, target, 0n, x, k, j, facts))
    case None{}:
      []

def factsOf(+q: Nat, +ks: Nat, +dot: Nat, +end: Nat, os: +List<Opt>) -> +List<Fact>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+f, +fo}, rest}:
      Fact{q, ks, dot, end, f, fo} <> factsOf(q, ks, dot, end, rest)

def markIf(+here: Bool, os: +List<Opt>) -> +List<Opt>:
  match os:
    case Nil{}:
      []
    case Con{Opt{+f, +fo}, rest}:
      Opt{Bool.or(f, here), fo} <> markIf(here, rest)

# The empty step of an empty right side gives the whole node.
def zeroFacts(ok: Bool, +q: Nat, +ks: Nat, +j: Nat, +flag: Bool) -> +List<Fact>:
  match ok:
    case True{}:
      [Fact{q, ks, 0n, j, flag, []}]
    case False{}:
      []

# The facts one kept step gives: the node of an empty right side, or a prefix forest
# before it, then its item.
def stepFacts(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +facts: +List<Fact>, e: Core.Bsr) -> +List<Fact>:
  match e:
    case Core.Bsr{+q, 0n, +ks, +k, +j}:
      zeroFacts(Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Bool.and(Nat.is_eq(ks, k), Nat.is_eq(k, j))), q, ks, j, Core.bsrEq(Core.Bsr{q, 0n, ks, k, j}, target))
    case Core.Bsr{+q, 1n+(+d), +ks, +k, +j}:
      +prefixes = optsAt(grammar, target, q, ks, d, k, facts)
      +items = itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, facts)
      factsOf(q, ks, 1n+d, j, markIf(Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), joinAll(prefixes, items)))

def addPick(have: Bool, +f: Fact, +facts: +List<Fact>) -> +List<Fact>:
  match have:
    case True{}:
      facts
    case False{}:
      f <> facts


def addNew(new: +List<Fact>, +facts: +List<Fact>) -> +List<Fact>:
  match new:
    case Nil{}:
      facts
    case Con{Fact{+q, +ks, +d, +e, +f, +fo}, rest}:
      addNew(rest, addPick(hasFact(q, ks, d, e, f, facts), Fact{q, ks, d, e, f, fo}, facts))

def roundOf(steps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  match steps:
    case Nil{}:
      facts
    case Con{+e, rest}:
      roundOf(rest, grammar, input, target, addNew(stepFacts(grammar, input, target, facts, e), facts))

# Every fact the list makes is already there (by key and flag).
def factsIn(fs: +List<Fact>, +facts: +List<Fact>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{Fact{+q, +ks, +d, +e, +fl, fo}, rest}:
      Bool.and(hasFact(q, ks, d, e, fl, facts), factsIn(rest, facts))

# The facts are closed under the rules of the steps.
def closedW(ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<Fact>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(factsIn(stepFacts(grammar, input, target, F, e), F), closedW(rest, grammar, input, target, F))

# Rounds until the facts are closed (`done` says whether they are), at most `fuel` of them.
def grow(fuel: Nat, done: Bool, +steps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  match fuel:
    case 0n:
      facts
    case 1n+f:
      match done:
        case True{}:
          facts
        case False{}:
          +next = roundOf(steps, grammar, input, target, facts)
          grow(f, closedW(steps, grammar, input, target, next), steps, grammar, input, target, next)

def fixpoint(fuel: Nat, +steps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +facts: +List<Fact>) -> +List<Fact>:
  grow(fuel, closedW(steps, grammar, input, target, facts), steps, grammar, input, target, facts)

def flaggedPick(f: Bool, +fo: +List<Core.Tree>, +later: Maybe<&2, +List<Core.Tree>>) -> Maybe<&2, +List<Core.Tree>>:
  match f:
    case True{}:
      Some{fo}
    case False{}:
      later


# ---- One tree for a target step ----

def firstFlagged(os: +List<Opt>) -> Maybe<&2, +List<Core.Tree>>:
  match os:
    case Nil{}:
      None{}
    case Con{Opt{+f, +fo}, rest}:
      flaggedPick(f, fo, firstFlagged(rest))

def orElse(a: Maybe<&2, +List<Core.Tree>>, +b: Maybe<&2, +List<Core.Tree>>) -> Maybe<&2, +List<Core.Tree>>:
  match a:
    case Some{+x}:
      Some{x}
    case None{}:
      b

def rootPick(hit: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +index: Nat, +len: Nat, +n: Nat, +facts: +List<Fact>) -> Maybe<&2, +List<Core.Tree>>:
  match hit:
    case True{}:
      firstFlagged(nodeOpts(index, optsAt(grammar, target, index, 0n, len, n, facts)))
    case False{}:
      None{}


# A root forest (one node of the start symbol over the whole input) that contains the target.
def rootFor(prods: +List<Core.Production>, +grammar: +List<Core.Production>, +target: Core.Bsr, +index: Nat, +start: Nat, +n: Nat, +facts: +List<Fact>) -> Maybe<&2, +List<Core.Tree>>:
  match prods:
    case Nil{}:
      None{}
    case Con{Core.Production{+lhs, +rhs}, rest}:
      orElse(rootPick(Nat.is_eq(lhs, start), grammar, target, index, List.length(&2, Core.Sym, rhs), n, facts), rootFor(rest, grammar, target, 1n+index, start, n, facts))

def witnessFor(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +steps: +List<Core.Bsr>, +target: Core.Bsr) -> Maybe<&2, +List<Core.Tree>>:
  rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), fixpoint(fuel, steps, grammar, input, target, []))

# ---- Covering ----

def coveredBy(+e: Core.Bsr, ws: +List<Core.Tree>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+t, rest}:
      Bool.or(Core.member(e, Core.steps([t], 0n)), coveredBy(e, rest))

def addWitness(m: Maybe<&2, +List<Core.Tree>>, +ws: +List<Core.Tree>) -> +List<Core.Tree>:
  match m:
    case Some{Con{+t, Nil{}}}:
      t <> ws
    case _:
      ws

def coverPick(done: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +steps: +List<Core.Bsr>, +e: Core.Bsr, +ws: +List<Core.Tree>) -> +List<Core.Tree>:
  match done:
    case True{}:
      ws
    case False{}:
      addWitness(witnessFor(fuel, grammar, start, input, steps, e), ws)


def cover(todo: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +steps: +List<Core.Bsr>, +ws: +List<Core.Tree>) -> +List<Core.Tree>:
  match todo:
    case Nil{}:
      ws
    case Con{+e, rest}:
      cover(rest, fuel, grammar, start, input, steps, coverPick(coveredBy(e, ws), fuel, grammar, start, input, steps, e, ws))

# One tree per kept step that no earlier tree covers.
def witnesses(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +steps: +List<Core.Bsr>) -> +List<Core.Tree>:
  cover(steps, fuel, grammar, start, input, steps, [])
