import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./UNBEATEN.bend as Unb
import ./WITNESS.bend as Witness
import ./LEMMAS.bend as Lemma

# THE EXTENT ORACLE (not trusted): phase 3 of SPEC.bend, @longest and @shortest, on top
# of phases 1 and 2. It takes the preference oracle's set, the steps of the unbeaten
# trees, and keeps the steps that lie on a best reading of their sequence, where only a
# reading that phases 1 and 2 keep counts (`extent_exact` in LAWS.bend).
#
# A step can't decide this alone. Whether a sequence's reading is best depends on where
# the whole sequence ends, and only its last step has that end. So the oracle looks at
# every end e at which the set completes the sequence from the step's start i:
#   - the best length M of the marked item over (i, e) is the longest (shortest) one of
#     the readings the set has: chains of the sequence's own steps from i to e;
#   - the step is kept when, for some such e, such a chain through the step reads the
#     marked item with length M.
# That set can hold steps that stand on nothing (a rule that fails at a node leaves the
# step above it), and a chain through one is no reading. So the set is first pruned from
# below, as UNBEATEN.bend prunes its sub-parses.
#
# The readings are looked for in the set itself, not by parsing again: a reading that
# phases 1 and 2 keep where the sequence stands is one of an unbeaten tree (it takes the
# sequence's place in it), so its steps are in the set. A best length is only used with
# a certificate: a forest for the sequence, built from the set (WITNESS.bend), that fits
# the items, spells the tokens, reads the marked item with that length, and whose steps
# all are in the set. Without one the oracle hands out nothing.
#
# Kept steps could still be stitched into a reading that is not best: its steps each lie
# on some best reading, but over different ends. So the oracle checks its own answer: a
# kept step of the marked item that lies on any reading over (i, e) has the best length
# over (i, e). If one doesn't, it hands out nothing. (The check may refuse a grammar
# where no stitched reading is made of kept steps; refusing is always safe.)
#
# The oracle refuses a sequence with more than one marked item, and a mark on an item of a
# loop's own alternative (a round has one item, so its length is fixed anyway).

# ---- Items of a sequence ----

# Does the set have the step of item q of the sequence at (index, prefix) from i, over
# the tokens from a to b?

def triIf(ok: Bool) -> Guard.Tri:
  match ok:
    case True{}:
      Guard.Yes{}
    case False{}:
      Guard.No{}
def seg(+set: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +i: Nat, +q: Nat, +a: Nat, +b: Nat) -> Guard.Tri:
  triIf(Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, a, b), set))

# ---- The marked item of a sequence ----

type Marked is Data:
  NoMark{}
  OneMark{d: Nat, ext: Spec.Extent}
  ManyMarks{}

def addMark(acc: Marked, found: Maybe<&2, Spec.Extent>, +dot: Nat) -> Marked:
  match acc found:
    case NoMark{} Some{+e}:
      OneMark{dot, e}
    case NoMark{} None{}:
      NoMark{}
    case OneMark{+d, +e} None{}:
      OneMark{d, e}
    case OneMark{d, e} Some{e2}:
      ManyMarks{}
    case ManyMarks{} _:
      ManyMarks{}

# The marked item of the items from the dot on, in the sequence at (index, prefix).
def markedFrom(items: +List<Spec.Item>, +marks: +List<Spec.ExtentMark>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, acc: Marked) -> Marked:
  match items:
    case Nil{}:
      acc
    case Con{+it, rest}:
      markedFrom(rest, marks, index, prefix, 1n+dot, addMark(acc, Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), dot))

def stepOk(hasStep: Bool, +q: Nat, +from: Nat, +b: Nat, +p: Nat, +k: Nat, +j: Nat) -> Bool:
  match hasStep:
    case True{}:
      Bool.or(Bool.not(Nat.is_eq(q, p)), Bool.and(Nat.is_eq(from, k), Nat.is_eq(b, j)))
    case False{}:
      True{}

# ---- Readings of a sequence, found in the set ----

# Is the constraint kept by item q read from `from` to b? The marked item d must read len
# tokens; when hasStep, item p must read from k to j.
def okAt(+q: Nat, +from: Nat, +b: Nat, +d: Nat, +len: Nat, hasStep: Bool, +p: Nat, +k: Nat, +j: Nat) -> Bool:
  Bool.and(Bool.or(Bool.not(Nat.is_eq(q, d)), Nat.is_eq(Nat.sub(b, from), len)), stepOk(hasStep, q, from, b, p, k, j))

# Is there a reading of the items (item q first) over the tokens from `from` to e that
# keeps the constraint? The next item ends at from + m for some m below count. gas
# bounds the search; when it runs out the answer is Unknown.
def search(gas: Nat, +items: +List<Spec.Item>, count: Nat, +set: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +i: Nat, +q: Nat, +from: Nat, +e: Nat, +d: Nat, +len: Nat, +hasStep: Bool, +p: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  match gas items count:
    case 0n _ _:
      Guard.Unknown{}
    case 1n+(+g) Nil{} _:
      triIf(Nat.is_eq(from, e))
    case 1n+(+g) Con{+it, +rest} 0n:
      Guard.No{}
    case 1n+(+g) Con{+it, +rest} 1n+(+m):
      +b = Nat.add(from, m)
      +here = Guard.andTri(triIf(okAt(q, from, b, d, len, hasStep, p, k, j)), Guard.andTri(seg(set, index, prefix, i, q, from, b), search(g, rest, 1n+Nat.sub(e, b), set, index, prefix, i, 1n+q, b, e, d, len, hasStep, p, k, j)))
      Guard.orTri(here, search(g, it <> rest, m, set, index, prefix, i, q, from, e, d, len, hasStep, p, k, j))

# Enough gas for every boundary of every item.
def gasFor(+its: +List<Spec.Item>, +i: Nat, +e: Nat) -> Nat:
  Nat.mul(1n+List.length(&2, Spec.Item, its), 2n+Nat.sub(e, i))

# The sequence a step belongs to, and where to look: the set's own steps of the sequence
# at (index, prefix), whose reversed path is rpath, with items its.
type Seq is Data:
  Seq{fuel: Nat, grammar: +List<Spec.Production>, input: +List<Nat>, set: +List<Spec.Bsr>, index: Nat, rpath: +List<Nat>, prefix: +List<Nat>, its: +List<Spec.Item>}

def seqSet(w: Seq) -> +List<Spec.Bsr>:
  match w:
    case Seq{fuel, grammar, input, +set, index, rpath, prefix, its}:
      set

def seqIndex(w: Seq) -> Nat:
  match w:
    case Seq{fuel, grammar, input, set, +index, rpath, prefix, its}:
      index

def seqPrefix(w: Seq) -> +List<Nat>:
  match w:
    case Seq{fuel, grammar, input, set, index, rpath, +prefix, its}:
      prefix

def seqIts(w: Seq) -> +List<Spec.Item>:
  match w:
    case Seq{fuel, grammar, input, set, index, rpath, prefix, +its}:
      its

# Is there a reading over (i, e) whose marked item d reads len tokens (and, when hasStep,
# whose item p reads from k to j)?
def readsWith(+w: Seq, +d: Nat, +len: Nat, +hasStep: Bool, +p: Nat, +k: Nat, +j: Nat, +i: Nat, +e: Nat) -> Guard.Tri:
  match w:
    case Seq{fuel, grammar, input, +set, +index, rpath, +prefix, +its}:
      search(gasFor(its, i, e), its, 1n+Nat.sub(e, i), set, index, prefix, i, 0n, i, e, d, len, hasStep, p, k, j)

def lengthOk(+w: Seq, +d: Nat, +i: Nat, +len: Nat, +e: Nat) -> Guard.Tri:
  readsWith(w, d, len, False{}, 0n, 0n, 0n, i, e)

# ---- Certificates ----

# Does the forest read the items from `from` on with the constraint of `search`?
def consOk(f: +List<Spec.Tree>, +q: Nat, +from: Nat, +d: Nat, +len: Nat, +hasStep: Bool, +p: Nat, +k: Nat, +j: Nat) -> Bool:
  match f:
    case Nil{}:
      True{}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      Bool.and(okAt(q, from, b, d, len, hasStep, p, k, j), consOk(ts, 1n+q, b, d, len, hasStep, p, k, j))

# A reading over (i, e) whose marked item reads len tokens, all of whose steps are in
# the set.
def certOk(+grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +its: +List<Spec.Item>, +d: Nat, +i: Nat, +len: Nat, +e: Nat, +f: +List<Spec.Tree>) -> Bool:
  Bool.and(Bool.and(Spec.fits(f, grammar, its), Gll.natsEq(Spec.leaves(f), Prefer.tokensFrom(input, i, e))), Bool.and(consOk(f, 0n, i, d, len, False{}, 0n, 0n, 0n), Spec.allIn(Spec.walk(f, False{}, index, prefix, 0n, i, i), set)))

def anyCert(fs: +List<+List<Spec.Tree>>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +its: +List<Spec.Item>, +d: Nat, +i: Nat, +len: Nat, +e: Nat) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{+f, rest}:
      Bool.or(certOk(grammar, input, set, index, prefix, its, d, i, len, e, f), anyCert(rest, grammar, input, set, index, prefix, its, d, i, len, e))

# Some forest the set has for the sequence over (i, e) is such a reading.
def certified(+w: Seq, +d: Nat, +i: Nat, +len: Nat, +e: Nat) -> Bool:
  match w:
    case Seq{+fuel, +grammar, +input, +set, +index, +rpath, +prefix, +its}:
      +fs = Prefer.seqForests(Witness.solve(fuel, grammar, input, set, [], Witness.TSeq{Prune.Seg{index, rpath, i, List.length(&2, Spec.Item, its), e}}))
      anyCert(fs, grammar, input, set, index, prefix, its, d, i, len, e)

# ---- The best length over (i, e) ----

type Best is Data:
  Found{len: Nat}
  NoneFound{}
  Unsure{}

def foundIf(ok: Bool, +len: Nat) -> Best:
  match ok:
    case True{}:
      Found{len}
    case False{}:
      Unsure{}

# A length a reading has is found when a certificate shows it.
def bestOn(t: Guard.Tri, +w: Seq, +d: Nat, +i: Nat, +len: Nat, +e: Nat, next: Best) -> Best:
  match t:
    case Guard.Yes{}:
      foundIf(certified(w, d, i, len, e), len)
    case Guard.No{}:
      next
    case Guard.Unknown{}:
      Unsure{}

# The first length of the list that a reading has: lengths are tried best first.
def firstLength(lens: +List<Nat>, +w: Seq, +d: Nat, +i: Nat, +e: Nat) -> Best:
  match lens:
    case Nil{}:
      NoneFound{}
    case Con{+len, rest}:
      bestOn(lengthOk(w, d, i, len, e), w, d, i, len, e, firstLength(rest, w, d, i, e))

def downFrom(n: Nat) -> +List<Nat>:
  match n:
    case 0n:
      [0n]
    case 1n+(+m):
      (1n+m) <> downFrom(m)

def upTo(n: Nat, +from: Nat) -> +List<Nat>:
  match n:
    case 0n:
      [from]
    case 1n+m:
      from <> upTo(m, 1n+from)

def lengthsFor(e: Spec.Extent, +n: Nat) -> +List<Nat>:
  match e:
    case Spec.Longest{}:
      downFrom(n)
    case Spec.Shortest{}:
      upTo(n, 0n)

def bestLength(+ext: Spec.Extent, +w: Seq, +d: Nat, +i: Nat, +e: Nat) -> Best:
  firstLength(lengthsFor(ext, Nat.sub(e, i)), w, d, i, e)

# ---- Does a step lie on a best reading over (i, e)? ----

def onBest(b: Best, +w: Seq, +p: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +e: Nat) -> Guard.Tri:
  match b:
    case Found{+len}:
      readsWith(w, d, len, True{}, p, k, j, i, e)
    case NoneFound{}:
      Guard.No{}
    case Unsure{}:
      Guard.Unknown{}

def endIf(ok: Bool, +j: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{j}
    case False{}:
      None{}

# ---- Where the sequence ends ----

# Is e a step that ends the sequence at (index, endPath) from i? Then its j is an end.
def endsHere(+index: Nat, +endPath: +List<Nat>, +i: Nat, e: Spec.Bsr) -> Maybe<&2, Nat>:
  match e:
    case Spec.Bsr{Spec.Slot{p, path}, i2, k, +j}:
      endIf(Bool.and(Nat.is_eq(p, index), Bool.and(Spec.pathEq(path, endPath), Nat.is_eq(i2, i))), j)

def consEnd(found: Maybe<&2, Nat>, +rest: +List<Nat>) -> +List<Nat>:
  match found:
    case Some{+j}:
      j <> rest
    case None{}:
      rest

def endsOf(set: +List<Spec.Bsr>, +index: Nat, +endPath: +List<Nat>, +i: Nat) -> +List<Nat>:
  match set:
    case Nil{}:
      []
    case Con{+e, rest}:
      consEnd(endsHere(index, endPath, i, e), endsOf(rest, index, endPath, i))

# The ends of the sequence from i.
def endsFrom(+w: Seq, +i: Nat) -> +List<Nat>:
  endsOf(seqSet(w), seqIndex(w), List.append(&2, Nat, seqPrefix(w), [List.length(&2, Spec.Item, seqIts(w))]), i)

# Some end e of the list at which the step lies on a best reading.
def onSomeBest(es: +List<Nat>, +ext: Spec.Extent, +w: Seq, +p: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  match es:
    case Nil{}:
      Guard.No{}
    case Con{+e, rest}:
      Guard.orTri(onBest(bestLength(ext, w, d, i, e), w, p, d, i, k, j, e), onSomeBest(rest, ext, w, p, d, i, k, j))

def loopItem(item: Maybe<&2, Spec.Item>) -> Bool:
  match item:
    case Some{Spec.Brack{+kind, alts}}:
      Gll.isLoop(kind)
    case Some{Spec.Sym{s}}:
      False{}
    case Some{Spec.Eps{}}:
      False{}
    case None{}:
      False{}

# ---- The verdict on a step ----

# The sequence a step belongs to: its items, its prefix path, and whether it is a loop's
# own alternative.
def seqLoopy(rpath: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat) -> Bool:
  match rpath:
    case Con{a, Con{+m, +outer}}:
      loopItem(Gll.nthItem(Gll.seqAt(grammar, index, outer), m))
    case Con{a, Nil{}}:
      False{}
    case Nil{}:
      False{}

# An empty step (dot 0) has no item; it can't belong to a marked sequence's reading.
def stepIn(dot: Nat, t: Guard.Tri) -> Guard.Tri:
  match dot:
    case 0n:
      Guard.Yes{}
    case 1n+p:
      t

# Yes: keep the step; No: remove it; Unknown: can't tell (or refused).
def verdictFor(m: Marked, loopy: Bool, +w: Seq, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  match m loopy:
    case NoMark{} _:
      Guard.Yes{}
    case ManyMarks{} _:
      Guard.Unknown{}
    case OneMark{d, e} True{}:
      Guard.Unknown{}
    case OneMark{+d, +e} False{}:
      stepIn(dot, onSomeBest(endsFrom(w, i), e, w, Nat.sub(dot, 1n), d, i, k, j))

def seqOf(+set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>) -> Seq:
  Seq{fuel, grammar, input, set, index, rpath, Gll.reverseOnto(rpath, []), Gll.seqAt(grammar, index, rpath)}

def verdictAt(rev: +List<Nat>, +set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, +index: Nat, +i: Nat, +k: Nat, +j: Nat) -> Guard.Tri:
  match rev:
    case Nil{}:
      Guard.Yes{}
    case Con{+dot, +rpath}:
      +its = Gll.seqAt(grammar, index, rpath)
      +prefix = Gll.reverseOnto(rpath, [])
      verdictFor(markedFrom(its, marks, index, prefix, 0n, NoMark{}), seqLoopy(rpath, grammar, index), seqOf(set, fuel, grammar, input, index, rpath), dot, i, k, j)

def stepVerdict(+set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, e: Spec.Bsr) -> Guard.Tri:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, +i, +k, +j}:
      verdictAt(Gll.reverseOnto(path, []), set, fuel, grammar, marks, input, index, i, k, j)

# ---- The self-check: a kept marked step is best wherever it can stand ----

# Kept steps could be stitched into a reading that is not best: each lies on some best
# reading, but over different ends. So for every kept step of the marked item, and every
# end e the sequence reaches from the step's start, the oracle checks: if the step lies
# on any reading over (i, e), its length is the best length over (i, e). Then every
# reading made of kept steps is best.

def isNo(t: Guard.Tri) -> Bool:
  match t:
    case Guard.Yes{}:
      False{}
    case Guard.No{}:
      True{}
    case Guard.Unknown{}:
      False{}

def foundIs(b: Best, +len: Nat) -> Bool:
  match b:
    case Found{+x}:
      Nat.is_eq(x, len)
    case NoneFound{}:
      False{}
    case Unsure{}:
      False{}

# At end e: not on a reading over (i, e), or of the best length there.
def endOk(+ext: Spec.Extent, +w: Seq, +d: Nat, +i: Nat, +k: Nat, +j: Nat, +e: Nat) -> Bool:
  +len = Nat.sub(j, k)
  Bool.or(isNo(readsWith(w, d, len, True{}, d, k, j, i, e)), foundIs(bestLength(ext, w, d, i, e), len))

def endsOk(es: +List<Nat>, +ext: Spec.Extent, +w: Seq, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(endOk(ext, w, d, i, k, j, e), endsOk(rest, ext, w, d, i, k, j))

# The check for one step: only kept steps of the marked item are checked.
def checkFor(m: Marked, +kept: Bool, +w: Seq, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match m:
    case OneMark{+d, +e}:
      Bool.or(Bool.or(Bool.not(kept), Bool.not(Nat.is_eq(dot, 1n+d))), endsOk(endsFrom(w, i), e, w, d, i, k, j))
    case NoMark{}:
      True{}
    case ManyMarks{}:
      True{}

def checkAt(rev: +List<Nat>, +kept: Bool, +set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, +index: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match rev:
    case Nil{}:
      True{}
    case Con{+dot, +rpath}:
      +its = Gll.seqAt(grammar, index, rpath)
      +prefix = Gll.reverseOnto(rpath, [])
      checkFor(markedFrom(its, marks, index, prefix, 0n, NoMark{}), kept, seqOf(set, fuel, grammar, input, index, rpath), dot, i, k, j)

def checkStep(+set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, +k, +j}:
      checkAt(Gll.reverseOnto(path, []), Guard.isYes(stepVerdict(set, fuel, grammar, marks, input, Spec.Bsr{Spec.Slot{index, path}, i, k, j})), set, fuel, grammar, marks, input, index, i, k, j)

def allChecked(es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(checkStep(set, fuel, grammar, marks, input, e), allChecked(rest, set, fuel, grammar, marks, input))

# ---- The oracle ----

def extentKept(es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.keepPick(Guard.isYes(stepVerdict(set, fuel, grammar, marks, input, e)), e, extentKept(rest, set, fuel, grammar, marks, input))

def allKnown(es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(Guard.isKnown(stepVerdict(set, fuel, grammar, marks, input, e)), allKnown(rest, set, fuel, grammar, marks, input))

def extentFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      +ks = extentKept(set, set, fuel, grammar, marks, input)
      Prefer.preferPick(Bool.and(allKnown(set, set, fuel, grammar, marks, input), allChecked(set, set, fuel, grammar, marks, input)), ks)
    case None{}:
      None{}

# The preference oracle's set, pruned from below (UNBEATEN.bend: a step stays when the set
# has what it stands on; every tree of the set keeps its steps), without the steps that
# lie on no best reading; or nothing when a check fails.
def extentSteps(+fuel: Nat, +grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  extentFrom(Unb.prunedFrom(Unb.unbeatenSteps(f, grammar, guards, pmarks, start, input), grammar, input), f, grammar, marks, input)
