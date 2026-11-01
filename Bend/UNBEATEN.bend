import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./LEMMAS.bend as Lemma

# THE JOINED PREFERENCE ORACLE (not trusted): phase 2 on top of phase 1. It starts from
# the guard oracle's set, the steps of the admissible trees, and removes the steps that
# complete an outranked choice, where only an admissible rival outranks
# (`prefer_avoid_exact` in LAWS.bend).
#
# It is PREFER.bend's oracle with one change, in how a rival is looked for. PREFER.bend
# parses the tokens of the choice again, with the rival's items as one extra production.
# Here that parse's steps are moved back to where they stand in the input: shifted by
# the choice's start, and with the extra production's slots read as the rival's own
# (the production's, or the bracket alternative's). The guard oracle then judges them
# there, with the whole input to look ahead in, as it judges any step. A rival is found
# when a step that ends its sequence over all the tokens passes. A removal still needs
# PREFER.bend's certificate, now drawn from the guard oracle's set; so it is admissible.

# ---- Moving a sub-parse step back into the input ----

# The step's slot, as it stands in the input: the extra production (number lg) is the
# rival's sequence at (idx, pre); every other slot stays.
def placeSlot(fresh: Bool, +idx: Nat, +pre: +List<Nat>, +p: Nat, +path: +List<Nat>) -> Spec.Slot:
  match fresh:
    case True{}:
      Spec.Slot{idx, List.append(&2, Nat, pre, path)}
    case False{}:
      Spec.Slot{p, path}

def place(+lg: Nat, +idx: Nat, +pre: +List<Nat>, +i: Nat, e: Spec.Bsr) -> Spec.Bsr:
  match e:
    case Spec.Bsr{Spec.Slot{+p, +path}, +a, +k, +j}:
      Spec.Bsr{placeSlot(Nat.is_eq(p, lg), idx, pre, p, path), Nat.add(i, a), Nat.add(i, k), Nat.add(i, j)}

def placeAll(es: +List<Spec.Bsr>, +lg: Nat, +idx: Nat, +pre: +List<Nat>, +i: Nat) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      place(lg, idx, pre, i, e) <> placeAll(rest, lg, idx, pre, i)

# ---- Does a sibling derive the same tokens, admissibly? ----

# ---- Keeping only the steps that something kept supports ----
#
# Judging leaves dead wood: a step can pass while nothing below it does (its child has no
# admissible tree). So the judged steps are pruned from below. A step is supported by a
# set when the set has what the step stands on: the step before it in its sequence (or
# the sequence starts there), and something that ends its item over what the item reads.
# The pruned set is computed by a loop that is not trusted; `closedOver` checks that it
# holds every judged step it supports. Then every forest of judged steps survives.

# Is there a step with slot (idx, path) from i to j, at any pivot?
def stepIs(+idx: Nat, +path: +List<Nat>, +i: Nat, +j: Nat, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{p, q}, a, k, b}:
      Bool.and(Nat.is_eq(p, idx), Bool.and(Gll.natsEq(q, path), Bool.and(Nat.is_eq(a, i), Nat.is_eq(b, j))))

def hasStep(set: +List<Spec.Bsr>, +idx: Nat, +path: +List<Nat>, +i: Nat, +j: Nat) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{+e, rest}:
      Bool.or(stepIs(idx, path, i, j, e), hasStep(rest, idx, path, i, j))

# A production of x, below n, whose right side ends from k to j.
def endsProd(n: Nat, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +x: Nat, +k: Nat, +j: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+(+q):
      Bool.or(Bool.and(Spec.lhsIs(grammar, q, x), hasStep(set, q, [List.length(&2, Spec.Item, Spec.rhsOf(grammar, q))], k, j)), endsProd(q, set, grammar, x, k, j))

# An alternative, below n, of the bracket at (idx, path), that ends from k to j.
def endsAlt(n: Nat, +set: +List<Spec.Bsr>, +idx: Nat, +path: +List<Nat>, +alts: +List<+List<Spec.Item>>, +k: Nat, +j: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+(+a):
      Bool.or(hasStep(set, idx, List.append(&2, Nat, path, [a, List.length(&2, Spec.Item, Spec.altOf(alts, a))]), k, j), endsAlt(a, set, idx, path, alts, k, j))

def bracketEnds(+set: +List<Spec.Bsr>, +idx: Nat, +path: +List<Nat>, +alts: +List<+List<Spec.Item>>, +k: Nat, +j: Nat) -> Bool:
  endsAlt(List.length(&2, +List<Spec.Item>, alts), set, idx, path, alts, k, j)

# Is the first token t?
def headIs(ts: +List<Nat>, +t: Nat) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Nat.is_eq(h, t)

# Does the set have what item `item`, at path `path` in production idx, needs to read the
# tokens from k to j? A loop reads nothing with no rounds, or ends with a round; a
# round's sequence starts where the loop starts.
def itemOk(item: Maybe<&2, Spec.Item>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +idx: Nat, +path: +List<Nat>, +k: Nat, +j: Nat) -> Bool:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+t}}}:
      Bool.and(Nat.is_eq(j, 1n+k), headIs(Lemma.dropN(k, input), t))
    case Some{Spec.Sym{Spec.Nonterminal{+x}}}:
      endsProd(List.length(&2, Spec.Production, grammar), set, grammar, x, k, j)
    case Some{Spec.Brack{Spec.Group{}, +alts}}:
      bracketEnds(set, idx, path, alts, k, j)
    case Some{Spec.Brack{Spec.Optional{}, +alts}}:
      Bool.or(Nat.is_eq(k, j), bracketEnds(set, idx, path, alts, k, j))
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      Bool.or(Nat.is_eq(k, j), bracketEnds(set, idx, path, alts, k, j))
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      bracketEnds(set, idx, path, alts, k, j)
    case Some{Spec.Eps{}}:
      Nat.is_eq(k, j)
    case None{}:
      False{}

# A round of a loop that starts at k, after the loop's start i: an earlier round ended
# at k.
def loopBefore(item: Maybe<&2, Spec.Item>, +set: +List<Spec.Bsr>, +idx: Nat, +path: +List<Nat>, +i: Nat, +k: Nat) -> Bool:
  match item:
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      bracketEnds(set, idx, path, alts, i, k)
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      bracketEnds(set, idx, path, alts, i, k)
    case Some{Spec.Brack{Spec.Group{}, alts}}:
      False{}
    case Some{Spec.Brack{Spec.Optional{}, alts}}:
      False{}
    case Some{Spec.Sym{s}}:
      False{}
    case Some{Spec.Eps{}}:
      False{}
    case None{}:
      False{}

def roundBefore(rp: +List<Nat>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +idx: Nat, +i: Nat, +k: Nat) -> Bool:
  match rp:
    case Con{a, Con{+m, +outer}}:
      loopBefore(Gll.nthItem(Gll.seqAt(grammar, idx, outer), m), set, idx, Gll.reverseOnto(m <> outer, []), i, k)
    case Con{a, Nil{}}:
      False{}
    case Nil{}:
      False{}

# The sequence with reversed path rp, started at i, can have its first item at k.
def startOk(+rp: +List<Nat>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +idx: Nat, +i: Nat, +k: Nat) -> Bool:
  Bool.or(Nat.is_eq(k, i), roundBefore(rp, set, grammar, idx, i, k))

# The items before item d end at k.
def beforeOk(d: Nat, +rp: +List<Nat>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +idx: Nat, +i: Nat, +k: Nat) -> Bool:
  match d:
    case 0n:
      startOk(rp, set, grammar, idx, i, k)
    case 1n+(+e):
      hasStep(set, idx, Gll.reverseOnto(rp, [1n+e]), i, k)

def supAt(rev: +List<Nat>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +idx: Nat, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match rev:
    case Nil{}:
      False{}
    case Con{0n, +rp}:
      Bool.and(Nat.is_eq(k, j), startOk(rp, set, grammar, idx, i, k))
    case Con{1n+(+d), +rp}:
      Bool.and(beforeOk(d, rp, set, grammar, idx, i, k), itemOk(Gll.nthItem(Gll.seqAt(grammar, idx, rp), d), set, grammar, input, idx, Gll.reverseOnto(rp, [d]), k, j))

def supported(+set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+idx, path}, +i, +k, +j}:
      supAt(Gll.reverseOnto(path, []), set, grammar, input, idx, i, k, j)

# Does the set hold every step of es that it supports?
def closedOver(es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(Bool.or(Bool.not(supported(set, grammar, input, e)), Spec.bsrMember(e, set)), closedOver(rest, set, grammar, input))

# The loop (not trusted): the steps of es that the set supports, n times over.
def supportedOf(es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.keepPick(supported(set, grammar, input, e), e, supportedOf(rest, set, grammar, input))

def grow(n: Nat, +es: +List<Spec.Bsr>, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match n:
    case 0n:
      set
    case 1n+(+m):
      grow(m, es, supportedOf(es, set, grammar, input), grammar, input)

def prunedFrom(found: Maybe<&2, +List<Spec.Bsr>>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+es}:
      +ks = grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input)
      Prefer.preferPick(closedOver(es, ks, grammar, input), ks)
    case None{}:
      None{}

# The placed steps of the sub-parse, judged by the guard oracle: Some{the kept ones}, or
# None when a verdict is unknown.
def judged(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +placed: +List<Spec.Bsr>) -> Maybe<&2, +List<Spec.Bsr>>:
  Prefer.preferPick(Guard.allKnown(placed, fuel, grammar, gm, input), Guard.guardKept(placed, fuel, grammar, gm, input))

def endIn(found: Maybe<&2, +List<Spec.Bsr>>, +idx: Nat, +pre: +List<Nat>, +n: Nat, +i: Nat, +j: Nat) -> Maybe<&2, Bool>:
  match found:
    case Some{+set}:
      Some{hasStep(set, idx, List.append(&2, Nat, pre, [n]), i, j)}
    case None{}:
      None{}

def placedFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +input: +List<Nat>, +idx: Nat, +pre: +List<Nat>, +i: Nat) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      judged(fuel, grammar, gm, input, placeAll(set, List.length(&2, Spec.Production, grammar), idx, pre, i))
    case None{}:
      None{}

# Do the items of the sequence at (idx, pre) derive the tokens from i to j admissibly, in
# their place in the input? Some{False} is a proven no; None means fuel ran out, a
# verdict was unknown, or the pruning check failed.
def derivesAdm(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +items: +List<Spec.Item>, +idx: Nat, +pre: +List<Nat>, +input: +List<Nat>, +i: Nat, +j: Nat) -> Maybe<&2, Bool>:
  +w = Prefer.tokensFrom(input, i, j)
  +sub = Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), w)
  endIn(prunedFrom(placedFrom(sub, fuel, grammar, gm, input, idx, pre, i), grammar, input), idx, pre, List.length(&2, Spec.Item, items), i, j)

# ---- The verdict on a step ----

def derivesIf(cand: Bool, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +items: +List<Spec.Item>, +idx: Nat, +pre: +List<Nat>, +input: +List<Nat>, +i: Nat, +j: Nat) -> Maybe<&2, Bool>:
  match cand:
    case True{}:
      derivesAdm(fuel, grammar, gm, items, idx, pre, input, i, j)
    case False{}:
      Some{False{}}

# Productions below n, from the last one down.
def prodVerdict(n: Nat, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +x: Nat, +q: Nat, +i: Nat, +j: Nat) -> Prefer.Verdict:
  match n:
    case 0n:
      Prefer.Keep{}
    case 1n+(+m):
      Prefer.verdictIf(derivesIf(Prefer.prodCand(grammar, marks, x, q, m), fuel, grammar, gm, Spec.rhsOf(grammar, m), m, [], input, i, j), m, prodVerdict(m, fuel, grammar, gm, marks, input, x, q, i, j))

# Alternatives below n of the bracket at (index, path), from the last one down.
def altVerdict(n: Nat, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +alts: +List<+List<Spec.Item>>, +index: Nat, +path: +List<Nat>, +a: Nat, +i: Nat, +j: Nat) -> Prefer.Verdict:
  match n:
    case 0n:
      Prefer.Keep{}
    case 1n+(+m):
      Prefer.verdictIf(derivesIf(Prefer.altCand(marks, index, path, a, m), fuel, grammar, gm, Spec.altOf(alts, m), index, List.append(&2, Nat, path, [m]), input, i, j), m, altVerdict(m, fuel, grammar, gm, marks, input, alts, index, path, a, i, j))

def verdictFor(d: Prefer.Done, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +i: Nat, +j: Nat) -> Prefer.Verdict:
  match d:
    case Prefer.DoneProd{+q}:
      prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, gm, marks, input, Spec.lhsOf(grammar, q), q, i, j)
    case Prefer.DoneAlt{+index, +rb, +a, +alts}:
      altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, gm, marks, input, alts, index, Gll.reverseOnto(rb, []), a, i, j)
    case Prefer.NotDone{}:
      Prefer.Keep{}

def verdictOf(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, e: Spec.Bsr) -> Prefer.Verdict:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, k, +j}:
      verdictFor(Prefer.doneAt(Gll.reverseOnto(path, []), grammar, index), fuel, grammar, gm, marks, input, i, j)

# ---- The oracle ----

def stepOk(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +ks: +List<Spec.Bsr>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, +k, +j}:
      +d = Prefer.doneAt(Gll.reverseOnto(path, []), grammar, index)
      Bool.and(Prefer.groupedAt(Gll.reverseOnto(path, []), grammar, index), Prefer.verdictOk(verdictFor(d, fuel, grammar, gm, marks, input, i, j), fuel, grammar, marks, input, set, ks, d, i, j))

def allStepsOk(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +ks: +List<Spec.Bsr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(stepOk(fuel, grammar, gm, marks, input, set, ks, e), allStepsOk(rest, fuel, grammar, gm, marks, input, set, ks))

def kept(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.keepPick(Prefer.isKeep(verdictOf(fuel, grammar, gm, marks, input, e)), e, kept(rest, fuel, grammar, gm, marks, input))

def unbeatenFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      +f = fuel
      +ks = kept(set, f, grammar, gm, marks, input)
      Prefer.preferPick(allStepsOk(set, f, grammar, gm, marks, input, set, ks), ks)
    case None{}:
      None{}

# The guard oracle's set without the steps of outranked choices, or nothing when a check
# fails.
def unbeatenSteps(+fuel: Nat, +grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  unbeatenFrom(Guard.guardSteps(f, grammar, gm, start, input), f, grammar, gm, marks, input)
