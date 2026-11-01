import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer

# THE GUARD ORACLE (not trusted): phase 1 of SPEC.bend. It takes the exact set and
# removes the steps of nodes, picks and rounds that break a rule (lookahead, @left,
# @right). `guards_exact` in LAWS.bend says what it hands out: the parse trees that use
# only its steps are exactly the admissible trees.
#
# Each rule can be decided from one step of the node, because of how `walk` records a
# sequence of n items: the step of item d has slot [.., d] and positions (i, k, j), where
# i is where the sequence starts and k..j is what item d reads. So
#   - the last step, d = n, has the node's start i, and its last child's span k..j;
#   - the first step, d = 1, has the first child's span i..j;
#   - an empty sequence has one step, d = 0 = n, with its start i.
# Lookahead depends only on the choice and i, @left on the choice and k..j, and @right
# on the choice and i..j. Two trees that share a step share these values, so a step is
# removed for one tree exactly when it is removed for every tree that has it: removing it
# takes out the bad nodes, and only those.
#
# Every answer is checked. "N derives w" is only believed with a forest that SPEC.bend's
# `fits` and `leaves` accept; "N does not derive w" only when the checked parser, which
# misses no parse step (`gll_every_parse_step`), finds no tree. Anything else is Unknown,
# and an Unknown that matters makes the oracle hand out nothing.
#
# The oracle refuses rules on the alternatives of a loop: in a round, i is the loop's
# start, not the round's. Swift Apus builds { τ } as { ( τ ) }, so a rule written in a
# loop sits on the inner group's alternative, which is fine.

# ---- Three-valued answers ----

# Yes and No are checked answers; Unknown means the oracle cannot tell.
type Tri is Data:
  Yes{}
  No{}
  Unknown{}

# Some of them is Yes, when one is a checked Yes; No when all are checked No.
def orTri(a: Tri, b: Tri) -> Tri:
  match a b:
    case Yes{} _:
      Yes{}
    case No{} _:
      b
    case Unknown{} Yes{}:
      Yes{}
    case Unknown{} No{}:
      Unknown{}
    case Unknown{} Unknown{}:
      Unknown{}

def notTri(a: Tri) -> Tri:
  match a:
    case Yes{}:
      No{}
    case No{}:
      Yes{}
    case Unknown{}:
      Unknown{}

def andTri(a: Tri, b: Tri) -> Tri:
  notTri(orTri(notTri(a), notTri(b)))

# ---- Do the items derive these tokens? ----

def anyForestFor(fs: +List<+List<Spec.Tree>>, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +w: +List<Nat>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{+f, rest}:
      Bool.or(Bool.and(Spec.fits(f, grammar, items), Gll.natsEq(Spec.leaves(f), w)), anyForestFor(rest, grammar, items, w))

# Forests for the items over w, from an exact parse of w with the items as one extra
# production.
def forestsFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +ext: +List<Spec.Production>, +idx: Nat, +n: Nat, +w: +List<Nat>) -> +List<+List<Spec.Tree>>:
  match found:
    case Some{+set}:
      Prefer.nodeForests(Witness.solve(fuel, ext, w, set, [], Witness.TProdIf{True{}, idx, n, 0n, List.length(&2, Nat, w)}))
    case None{}:
      []

def yesIf(ok: Bool) -> Tri:
  match ok:
    case True{}:
      Yes{}
    case False{}:
      Unknown{}

def triOf(found: Maybe<&2, Bool>, +yes: Bool) -> Tri:
  match found:
    case Some{False{}}:
      No{}
    case Some{True{}}:
      yesIf(yes)
    case None{}:
      Unknown{}

# Yes with a forest that SPEC.bend accepts, No when the checked parser finds no tree.
def derivesW(+fuel: Nat, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +w: +List<Nat>) -> Tri:
  +ext = Prefer.extended(grammar, items)
  +fresh = Prefer.freshNt(grammar)
  +idx = List.length(&2, Spec.Production, grammar)
  +n = List.length(&2, Spec.Item, items)
  +yes = anyForestFor(forestsFrom(Exact.exactSteps(fuel, ext, fresh, w), fuel, ext, idx, n, w), grammar, items, w)
  triOf(Prefer.derivesHere(fuel, grammar, items, w, 0n, List.length(&2, Nat, w)), yes)

def derivesNt(+fuel: Nat, +grammar: +List<Spec.Production>, +x: Nat, +w: +List<Nat>) -> Tri:
  derivesW(fuel, grammar, [Spec.Sym{Spec.Nonterminal{x}}], w)

# Does x derive a prefix, of length below n, of the tokens from i on?
def aheadBelow(n: Nat, +fuel: Nat, +grammar: +List<Spec.Production>, +x: Nat, +input: +List<Nat>, +i: Nat) -> Tri:
  match n:
    case 0n:
      No{}
    case 1n+(+m):
      orTri(derivesNt(fuel, grammar, x, Prefer.tokensFrom(input, i, Nat.add(i, m))), aheadBelow(m, fuel, grammar, x, input, i))

# Does x derive some prefix of the tokens from i on?
def aheadAt(+fuel: Nat, +grammar: +List<Spec.Production>, +x: Nat, +input: +List<Nat>, +i: Nat) -> Tri:
  aheadBelow(1n+Nat.sub(List.length(&2, Nat, input), i), fuel, grammar, x, input, i)

# Is every nonterminal ahead? Is none?
def allAhead(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +i: Nat) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(aheadAt(fuel, grammar, x, input, i), allAhead(rest, fuel, grammar, input, i))

def noneAhead(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +i: Nat) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(aheadAt(fuel, grammar, x, input, i)), noneAhead(rest, fuel, grammar, input, i))

# Does none of the nonterminals derive w?
def noneDerive(xs: +List<Nat>, +fuel: Nat, +grammar: +List<Spec.Production>, +w: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(derivesNt(fuel, grammar, x, w)), noneDerive(rest, fuel, grammar, w))

# The edge child, which spells w, is allowed (SPEC.bend's EdgeOk).
def edgeOk(ids: +List<Nat>, +fuel: Nat, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +w: +List<Nat>) -> Tri:
  match ids:
    case Nil{}:
      notTri(derivesW(fuel, grammar, items, w))
    case Con{+x, +rest}:
      noneDerive(x <> rest, fuel, grammar, w)

# ---- The rules a step decides ----

# The answer, when this step decides the rule; Yes otherwise.
def lastOnly(here: Bool, t: Tri) -> Tri:
  match here:
    case True{}:
      t
    case False{}:
      Yes{}

# The step is item d of a sequence `items` of n items; i, k and j are its positions.
# Does the rule hold for the node? Yes when it does, No when it does not. A rule that
# this step does not decide is Yes here: another step of the node decides it.
def guardAt(g: Spec.Guard, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match g:
    case Spec.Ahead{+ids}:
      lastOnly(Nat.is_eq(d, n), allAhead(ids, fuel, grammar, input, i))
    case Spec.NotAhead{+ids}:
      lastOnly(Nat.is_eq(d, n), noneAhead(ids, fuel, grammar, input, i))
    case Spec.LeftAssoc{+ids}:
      lastOnly(Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)), edgeOk(ids, fuel, grammar, items, Prefer.tokensFrom(input, k, j)))
    case Spec.RightAssoc{+ids}:
      lastOnly(Bool.and(Nat.is_eq(d, 1n), Nat.is_lt(0n, n)), edgeOk(ids, fuel, grammar, items, Prefer.tokensFrom(input, i, j)))

def guardsAt(gs: +List<Spec.Guard>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +items: +List<Spec.Item>, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match gs:
    case Nil{}:
      Yes{}
    case Con{+g, rest}:
      andTri(guardAt(g, fuel, grammar, input, items, n, d, i, k, j), guardsAt(rest, fuel, grammar, input, items, n, d, i, k, j))

# A loop's alternatives may carry no rules: Yes when they don't, Unknown when they do.
def loopFree(kind: Spec.Bracket, gs: +List<Spec.Guard>) -> Tri:
  match kind:
    case Spec.Closure{}:
      yesIf(List.is_empty(&2, Spec.Guard, gs))
    case Spec.Positive{}:
      yesIf(List.is_empty(&2, Spec.Guard, gs))
    case Spec.Group{}:
      Yes{}
    case Spec.Optional{}:
      Yes{}

# The answer, unless the step is refused: a refusal wins over a No.
def unlessRefused(free: Tri, t: Tri) -> Tri:
  match free:
    case Yes{}:
      t
    case No{}:
      Unknown{}
    case Unknown{}:
      Unknown{}

# The step is item d of alternative a of the bracket `item`, at (index, bpath).
def altStep(item: Maybe<&2, Spec.Item>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +index: Nat, +bpath: +List<Nat>, +a: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match item:
    case Some{Spec.Brack{+kind, +alts}}:
      +gs = Spec.altGuards(gm, index, bpath, a)
      +items = Spec.altOf(alts, a)
      unlessRefused(loopFree(kind, gs), guardsAt(gs, fuel, grammar, input, items, List.length(&2, Spec.Item, items), d, i, k, j))
    case Some{Spec.Sym{s}}:
      Yes{}
    case Some{Spec.Eps{}}:
      Yes{}
    case None{}:
      Yes{}

# The step with reversed slot path `rev` in production `index`.
def stepAt(rev: +List<Nat>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +index: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match rev:
    case Nil{}:
      Yes{}
    case Con{+d, Nil{}}:
      +items = Spec.rhsOf(grammar, index)
      guardsAt(Spec.prodGuards(gm, index), fuel, grammar, input, items, List.length(&2, Spec.Item, items), d, i, k, j)
    case Con{d, Con{a, Nil{}}}:
      Yes{}
    case Con{+d, Con{+a, Con{+m, +outer}}}:
      altStep(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), fuel, grammar, gm, input, index, Gll.reverseOnto(m <> outer, []), a, d, i, k, j)

# Yes: the step keeps every rule it decides. No: it breaks one. Unknown: can't tell.
def stepTri(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, e: Spec.Bsr) -> Tri:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, +i, +k, +j}:
      stepAt(Gll.reverseOnto(path, []), fuel, grammar, gm, input, index, i, k, j)

# ---- The oracle ----

def isYes(t: Tri) -> Bool:
  match t:
    case Yes{}:
      True{}
    case No{}:
      False{}
    case Unknown{}:
      False{}

def isKnown(t: Tri) -> Bool:
  match t:
    case Yes{}:
      True{}
    case No{}:
      True{}
    case Unknown{}:
      False{}

# The steps whose rules hold.
def guardKept(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.keepPick(isYes(stepTri(fuel, grammar, gm, input, e)), e, guardKept(rest, fuel, grammar, gm, input))

# Was every step decided?
def allKnown(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(isKnown(stepTri(fuel, grammar, gm, input, e)), allKnown(rest, fuel, grammar, gm, input))

def guardFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      Prefer.preferPick(allKnown(set, fuel, grammar, gm, input), guardKept(set, fuel, grammar, gm, input))
    case None{}:
      None{}

# The exact set without the steps of nodes that break a rule, or nothing when a check
# fails.
def guardSteps(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  guardFrom(Exact.exactSteps(f, grammar, start, input), f, grammar, gm, input)
