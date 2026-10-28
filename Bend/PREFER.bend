import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./LEMMAS.bend as Lemma

# THE PREFERENCE ORACLE (not trusted): the exact set, without the steps that complete an
# outranked choice. `prefer_avoid_exact` in LAWS.bend says what it hands out: the parse
# trees that use only its steps are exactly the selected trees.
#
# A step completes a choice when its slot is the end of a production's right side, or of
# an alternative of a bracket. Its i and j are where the choice starts and ends, so the
# choice reads the input from i to j. The step is removed when a sibling of higher rank
# derives those tokens too. That is decided by parsing them again: the checked parser
# runs on the tokens from i to j, with the sibling's items as one extra production. If
# that parse finds no tree for the extra production, `gll_every_parse_step` says there is
# none, so nothing outranks the choice and the step stays.
#
# A removal is only handed out with a certificate that SPEC.bend's own definitions check:
# a forest for the sibling's items over the same tokens, and a set C of nonterminals
# containing every node that can be above the choice over the same tokens, such that the
# forest has no node of C over those tokens. That is the rival of SPEC.bend, which must
# not go round a cycle back to a node above it. C is grown from the choice's nonterminal
# by one rule: a step whose sequence starts at its own pivot (nothing before it in the
# sequence) and whose item is a nonterminal of C over the tokens puts the sequence's
# nonterminal in C. `closedFor` checks that the rule adds nothing new. On a grammar with
# a preference cycle no such certificate exists, and the oracle hands out nothing.
#
# A loop must be written { ( τ ) }, as Swift Apus builds it: then a round has one item, a
# group, and each round's choice is that group's. A loop written { τ } would compare
# rounds by where the loop starts, not where the round starts, so the oracle refuses it.

# ---- Which choice a step completes ----

# DoneProd: the step ends production q. DoneAlt: it ends alternative a of the bracket
# whose reversed item path is rb (m :: outer for item m of the sequence at outer), with
# alternatives alts. NotDone: it ends no choice.
type Done is Data:
  DoneProd{q: Nat}
  DoneAlt{index: Nat, rb: +List<Nat>, a: Nat, alts: +List<+List<Spec.Item>>}
  NotDone{}

def doneIf(ok: Bool, +d: Done) -> Done:
  match ok:
    case True{}:
      d
    case False{}:
      NotDone{}

def altDone(item: Maybe<&2, Spec.Item>, +index: Nat, +rb: +List<Nat>, +a: Nat, +d: Nat) -> Done:
  match item:
    case Some{Spec.Brack{kind, +alts}}:
      doneIf(Nat.is_eq(d, List.length(&2, Spec.Item, Spec.altOf(alts, a))), DoneAlt{index, rb, a, alts})
    case Some{Spec.Sym{s}}:
      NotDone{}
    case Some{Spec.Eps{}}:
      NotDone{}
    case None{}:
      NotDone{}

# The choice ended by the slot with reversed path `rev` in production `index`.
def doneAt(rev: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat) -> Done:
  match rev:
    case Nil{}:
      NotDone{}
    case Con{+d, Nil{}}:
      doneIf(Nat.is_eq(d, List.length(&2, Spec.Item, Spec.rhsOf(grammar, index))), DoneProd{index})
    case Con{d, Con{a, Nil{}}}:
      NotDone{}
    case Con{+d, Con{+a, Con{+m, +outer}}}:
      altDone(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), index, m <> outer, a, d)

def doneOf(+grammar: +List<Spec.Production>, e: Spec.Bsr) -> Done:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, i, k, j}:
      doneAt(Gll.reverseOnto(path, []), grammar, index)

# ---- Does a sibling derive the same tokens? ----

def maxLhs(prods: +List<Spec.Production>) -> Nat:
  match prods:
    case Nil{}:
      0n
    case Con{Spec.Production{+lhs, rhs}, rest}:
      Nat.max(lhs, maxLhs(rest))

# A nonterminal that no production of the grammar has.
def freshNt(+grammar: +List<Spec.Production>) -> Nat:
  1n+maxLhs(grammar)

# The grammar with one more production, fresh = items, numbered after the others.
def extended(+grammar: +List<Spec.Production>, +items: +List<Spec.Item>) -> +List<Spec.Production>:
  List.append(&2, Spec.Production, grammar, [Spec.Production{freshNt(grammar), items}])

# The tokens from k to j.
def tokensFrom(+input: +List<Nat>, +k: Nat, +j: Nat) -> +List<Nat>:
  Lemma.slice(input, k, Nat.sub(j, k))

# Is the step the end of production idx, with n items, over all of the len tokens?
def endsAll(+idx: Nat, +n: Nat, +len: Nat, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{p, path}, i, k, j}:
      Bool.and(Nat.is_eq(p, idx), Bool.and(Gll.natsEq(path, [n]), Bool.and(Nat.is_eq(i, 0n), Nat.is_eq(j, len))))

def anyEndsAll(set: +List<Spec.Bsr>, +idx: Nat, +n: Nat, +len: Nat) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{+e, rest}:
      Bool.or(endsAll(idx, n, len, e), anyEndsAll(rest, idx, n, len))

def derivedIn(found: Maybe<&2, +List<Spec.Bsr>>, +idx: Nat, +n: Nat, +len: Nat) -> Maybe<&2, Bool>:
  match found:
    case Some{+set}:
      Some{anyEndsAll(set, idx, n, len)}
    case None{}:
      None{}

# Do the items derive the tokens from k to j? Some{False} is a proven no; None means the
# parser ran out of fuel.
def derivesHere(+fuel: Nat, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +input: +List<Nat>, +k: Nat, +j: Nat) -> Maybe<&2, Bool>:
  +w = tokensFrom(input, k, j)
  derivedIn(Check.checkedSteps(fuel, extended(grammar, items), freshNt(grammar), w), List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, w))

# ---- The verdict on a step ----

# Keep: no sibling of higher rank derives the tokens. Remove{who}: sibling `who` (a
# production, or an alternative number) does. Unsure: the oracle cannot tell.
type Verdict is Data:
  Keep{}
  Remove{who: Nat}
  Unsure{}

def derivesIf(cand: Bool, +fuel: Nat, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +input: +List<Nat>, +k: Nat, +j: Nat) -> Maybe<&2, Bool>:
  match cand:
    case True{}:
      derivesHere(fuel, grammar, items, input, k, j)
    case False{}:
      Some{False{}}

def verdictIf(found: Maybe<&2, Bool>, +who: Nat, +next: Verdict) -> Verdict:
  match found:
    case Some{True{}}:
      Remove{who}
    case Some{False{}}:
      next
    case None{}:
      Unsure{}

# Is production m a rival candidate of production q of x: a production of x of higher rank?
def prodCand(+grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +x: Nat, +q: Nat, +m: Nat) -> Bool:
  Bool.and(Spec.lhsIs(grammar, m, x), Spec.outranks(Spec.prodRank(marks, m), Spec.prodRank(marks, q)))

# Productions below n, from the last one down.
def prodVerdict(n: Nat, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +x: Nat, +q: Nat, +k: Nat, +j: Nat) -> Verdict:
  match n:
    case 0n:
      Keep{}
    case 1n+(+m):
      verdictIf(derivesIf(prodCand(grammar, marks, x, q, m), fuel, grammar, Spec.rhsOf(grammar, m), input, k, j), m, prodVerdict(m, fuel, grammar, marks, input, x, q, k, j))

def altCand(+marks: +List<Spec.Mark>, +index: Nat, +path: +List<Nat>, +a: Nat, +m: Nat) -> Bool:
  Spec.outranks(Spec.altRank(marks, index, path, m), Spec.altRank(marks, index, path, a))

# Alternatives below n of the bracket at (index, path), from the last one down.
def altVerdict(n: Nat, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +alts: +List<+List<Spec.Item>>, +index: Nat, +path: +List<Nat>, +a: Nat, +k: Nat, +j: Nat) -> Verdict:
  match n:
    case 0n:
      Keep{}
    case 1n+(+m):
      verdictIf(derivesIf(altCand(marks, index, path, a, m), fuel, grammar, Spec.altOf(alts, m), input, k, j), m, altVerdict(m, fuel, grammar, marks, input, alts, index, path, a, k, j))

def verdictFor(d: Done, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +i: Nat, +j: Nat) -> Verdict:
  match d:
    case DoneProd{+q}:
      prodVerdict(List.length(&2, Spec.Production, grammar), fuel, grammar, marks, input, Spec.lhsOf(grammar, q), q, i, j)
    case DoneAlt{+index, +rb, +a, +alts}:
      altVerdict(List.length(&2, +List<Spec.Item>, alts), fuel, grammar, marks, input, alts, index, Gll.reverseOnto(rb, []), a, i, j)
    case NotDone{}:
      Keep{}

def verdictOf(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, e: Spec.Bsr) -> Verdict:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, k, +j}:
      verdictFor(doneAt(Gll.reverseOnto(path, []), grammar, index), fuel, grammar, marks, input, i, j)

def isKeep(v: Verdict) -> Bool:
  match v:
    case Keep{}:
      True{}
    case Remove{who}:
      False{}
    case Unsure{}:
      False{}

# ---- The nonterminals that can be above a choice ----

def natIn(+x: Nat, xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(x, y), natIn(x, rest))

def ntIn(item: Maybe<&2, Spec.Item>, +c: +List<Nat>) -> Bool:
  match item:
    case Some{Spec.Sym{Spec.Nonterminal{+y}}}:
      natIn(y, c)
    case Some{Spec.Sym{Spec.Terminal{t}}}:
      False{}
    case Some{Spec.Brack{kind, alts}}:
      False{}
    case Some{Spec.Eps{}}:
      False{}
    case None{}:
      False{}

# The item just before the slot with reversed path `rev`.
def itemBefore(rev: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat) -> Maybe<&2, Spec.Item>:
  match rev:
    case Con{1n+(+d), +rp}:
      Gll.nthItem(Gll.seqAt(grammar, index, rp), d)
    case Con{0n, rp}:
      None{}
    case Nil{}:
      None{}

# Does the step say that the sequence of its slot starts with a nonterminal of c over
# the tokens w, with nothing before it?
def triggers(+grammar: +List<Spec.Production>, +input: +List<Nat>, +c: +List<Nat>, +w: +List<Nat>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, +k, +j}:
      Bool.and(Nat.is_eq(i, k), Bool.and(Gll.natsEq(tokensFrom(input, k, j), w), ntIn(itemBefore(Gll.reverseOnto(path, []), grammar, index), c)))

def ownerOf(+grammar: +List<Spec.Production>, e: Spec.Bsr) -> Nat:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, i, k, j}:
      Spec.lhsOf(grammar, index)

def ruleOk(+grammar: +List<Spec.Production>, +input: +List<Nat>, +c: +List<Nat>, +w: +List<Nat>, +e: Spec.Bsr) -> Bool:
  Bool.or(Bool.not(triggers(grammar, input, c, w, e)), natIn(ownerOf(grammar, e), c))

# Does the rule add nothing new to c?
def closedFor(set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +c: +List<Nat>, +w: +List<Nat>) -> Bool:
  match set:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(ruleOk(grammar, input, c, w, e), closedFor(rest, grammar, input, c, w))

def addIf(add: Bool, +x: Nat, +c: +List<Nat>) -> +List<Nat>:
  match add:
    case True{}:
      x <> c
    case False{}:
      c

def growOnce(set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +c: +List<Nat>, +w: +List<Nat>) -> +List<Nat>:
  match set:
    case Nil{}:
      c
    case Con{+e, rest}:
      +c2 = growOnce(rest, grammar, input, c, w)
      addIf(Bool.not(ruleOk(grammar, input, c2, w, e)), ownerOf(grammar, e), c2)

def grow(n: Nat, +set: +List<Spec.Bsr>, +grammar: +List<Spec.Production>, +input: +List<Nat>, +c: +List<Nat>, +w: +List<Nat>) -> +List<Nat>:
  match n:
    case 0n:
      c
    case 1n+(+m):
      grow(m, set, grammar, input, growOnce(set, grammar, input, c, w), w)

# ---- Certificates ----

def forestOk(+grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +c: +List<Nat>, +w: +List<Nat>, +f: +List<Spec.Tree>) -> Bool:
  Bool.and(Spec.fits(f, grammar, items), Bool.and(Gll.natsEq(Spec.leaves(f), w), Bool.not(Spec.revisits(grammar, f, c, w))))

def anyForestOk(fs: +List<+List<Spec.Tree>>, +grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +c: +List<Nat>, +w: +List<Nat>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{+f, rest}:
      Bool.or(forestOk(grammar, items, c, w, f), anyForestOk(rest, grammar, items, c, w))

def nodeForests(cands: +List<Witness.Cand>) -> +List<+List<Spec.Tree>>:
  match cands:
    case Nil{}:
      []
    case Con{Witness.Cand{Con{Spec.Node{idx, +cs}, Nil{}}, st}, rest}:
      cs <> nodeForests(rest)
    case Con{c, rest}:
      nodeForests(rest)

def seqForests(cands: +List<Witness.Cand>) -> +List<+List<Spec.Tree>>:
  match cands:
    case Nil{}:
      []
    case Con{Witness.Cand{+cs, st}, rest}:
      cs <> seqForests(rest)

# The rival's items, and forests for them over the tokens from i to j, built from the
# exact set.
def rivalItems(d: Done, +grammar: +List<Spec.Production>, +who: Nat) -> +List<Spec.Item>:
  match d:
    case DoneProd{q}:
      Spec.rhsOf(grammar, who)
    case DoneAlt{index, rb, a, +alts}:
      Spec.altOf(alts, who)
    case NotDone{}:
      []

def rivalForests(d: Done, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +who: Nat, +i: Nat, +j: Nat) -> +List<+List<Spec.Tree>>:
  match d:
    case DoneProd{q}:
      nodeForests(Witness.solve(fuel, grammar, input, set, [], Witness.TProdIf{True{}, who, List.length(&2, Spec.Item, Spec.rhsOf(grammar, who)), i, j}))
    case DoneAlt{+index, +rb, a, +alts}:
      seqForests(Witness.solve(fuel, grammar, input, set, [], Witness.TSeq{Prune.Seg{index, who <> rb, i, List.length(&2, Spec.Item, Spec.altOf(alts, who)), j}}))
    case NotDone{}:
      []

# The nonterminal of the choice: the production's, or that of the production holding
# the bracket.
def choiceNt(d: Done, +grammar: +List<Spec.Production>) -> Nat:
  match d:
    case DoneProd{+q}:
      Spec.lhsOf(grammar, q)
    case DoneAlt{+index, rb, a, alts}:
      Spec.lhsOf(grammar, index)
    case NotDone{}:
      0n

def certOk(+fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +d: Done, +who: Nat, +i: Nat, +j: Nat) -> Bool:
  +w = tokensFrom(input, i, j)
  +c = grow(List.length(&2, Spec.Production, grammar), set, grammar, input, [choiceNt(d, grammar)], w)
  Bool.and(Bool.and(natIn(choiceNt(d, grammar), c), closedFor(set, grammar, input, c, w)), anyForestOk(rivalForests(d, fuel, grammar, input, set, who, i, j), grammar, rivalItems(d, grammar, who), c, w))

def verdictOk(v: Verdict, +fuel: Nat, +grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +d: Done, +i: Nat, +j: Nat) -> Bool:
  match v:
    case Keep{}:
      True{}
    case Remove{+who}:
      certOk(fuel, grammar, input, set, d, who, i, j)
    case Unsure{}:
      False{}

# ---- Loops written { ( τ ) } ----

def oneGroup(alts: +List<+List<Spec.Item>>) -> Bool:
  match alts:
    case Con{Con{Spec.Brack{Spec.Group{}, galts}, Nil{}}, Nil{}}:
      True{}
    case _:
      False{}

def loopOk(item: Maybe<&2, Spec.Item>) -> Bool:
  match item:
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      oneGroup(alts)
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      oneGroup(alts)
    case Some{Spec.Brack{Spec.Group{}, alts}}:
      True{}
    case Some{Spec.Brack{Spec.Optional{}, alts}}:
      True{}
    case Some{Spec.Sym{s}}:
      True{}
    case Some{Spec.Eps{}}:
      True{}
    case None{}:
      True{}

# Is the bracket around the sequence of the step's slot, when it is a loop, written
# { ( τ ) }?
def groupedAt(rev: +List<Nat>, +grammar: +List<Spec.Production>, +index: Nat) -> Bool:
  match rev:
    case Con{d, Con{a, Con{+m, +outer}}}:
      loopOk(Gll.nthItem(Gll.seqAt(grammar, index, outer), m))
    case Con{d, Con{a, Nil{}}}:
      True{}
    case Con{d, Nil{}}:
      True{}
    case Nil{}:
      True{}

def grouped(+grammar: +List<Spec.Production>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, path}, i, k, j}:
      groupedAt(Gll.reverseOnto(path, []), grammar, index)

# ---- The oracle ----

def stepOk(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +set: +List<Spec.Bsr>, e: Spec.Bsr) -> Bool:
  match e:
    case Spec.Bsr{Spec.Slot{+index, +path}, +i, +k, +j}:
      +d = doneAt(Gll.reverseOnto(path, []), grammar, index)
      Bool.and(groupedAt(Gll.reverseOnto(path, []), grammar, index), verdictOk(verdictFor(d, fuel, grammar, marks, input, i, j), fuel, grammar, input, set, d, i, j))

def allStepsOk(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(stepOk(fuel, grammar, marks, input, set, e), allStepsOk(rest, fuel, grammar, marks, input, set))

def kept(es: +List<Spec.Bsr>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> +List<Spec.Bsr>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      Prune.keepPick(isKeep(verdictOf(fuel, grammar, marks, input, e)), e, kept(rest, fuel, grammar, marks, input))

def preferPick(ok: Bool, +set: +List<Spec.Bsr>) -> Maybe<&2, +List<Spec.Bsr>>:
  match ok:
    case True{}:
      Some{set}
    case False{}:
      None{}

def preferFrom(found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      +f = fuel
      preferPick(allStepsOk(set, f, grammar, marks, input, set), kept(set, f, grammar, marks, input))
    case None{}:
      None{}

# The exact set without the steps of outranked choices, or nothing when a check fails.
def preferSteps(+fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  +f = fuel
  preferFrom(Exact.exactSteps(f, grammar, start, input), f, grammar, marks, input)
