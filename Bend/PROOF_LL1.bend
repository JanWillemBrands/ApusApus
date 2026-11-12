import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./FIRST.bend as First
import ./LL1.bend as LL1
import ./LEMMAS.bend as Lemma
import ./PROOF_SETS.bend as Sets
import ./PROOF_TABLES.bend as Tab
import ./PROOF_ADMIT.bend as Adm
import ./PROOF_PRED.bend as Pr
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R

# LL(1) BY THE TABLES IS LL(1). The tables contain the exact sets: FIRST and nullable by
# PROOF_TABLES, FOLLOW by the walk below (wherever a parse tree ends a sequence, the token
# there is in the tables' context for it). So two choices that share a token exactly also
# share it by the tables, and the check would have reported them.

# ======== SEQUENCES: SPEC.bend's forward prefixes and the engine's reversed paths ========

law item_at_eq:
  for items: +List<Spec.Item>
  for +m: Nat
  {Spec.itemAt(items, m) == Gll.nthItem(items, m) : Maybe<&2, Spec.Item>}

def item_at_eq(items, m):
  match items m:
    case Nil{} _:
      {==}
    case Con{x, rest} 0n:
      {==}
    case Con{x, +rest} 1n+(+n):
      item_at_eq(rest, n)

law alternative_eq:
  for item: Maybe<&2, Spec.Item>
  for +a: Nat
  {Spec.bracketAlternative(item, a) == Gll.bracketAlt(item, a) : +List<Spec.Item>}

def alternative_eq(item, a):
  match item:
    case Some{Spec.Brack{kind, alts}}:
      {==}
    case Some{Spec.Sym{s}}:
      {==}
    case Some{Spec.Eps{}}:
      {==}
    case None{}:
      {==}

law items_from_eq:
  for n: Nat
  for items: +List<Spec.Item>
  {Spec.itemsFrom(n, items) == Gll.dropFrom(n, items) : +List<Spec.Item>}

def items_from_eq(n, items):
  match n items:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+(+m) Con{x, +rest}:
      items_from_eq(m, rest)

# A prefix made of whole (item, alternative) pairs.
def evenLength(xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, Nil{}}:
      False{}
    case Con{x, Con{y, rest}}:
      evenLength(rest)

law even_snoc:
  for xs: +List<Nat>
  for +m: Nat
  for +a: Nat
  {evenLength(List.append(&2, Nat, xs, [m, a])) == evenLength(xs) : Bool}

def even_snoc(xs, m, a):
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{x, Con{y, +rest}}:
      even_snoc(rest, m, a)

# One pair more at the end of a prefix: one level deeper.
law sequence_snoc:
  for p: +List<Nat>
  for +m: Nat
  for +a: Nat
  for items: +List<Spec.Item>
  for even: {evenLength(p) == True{} : Bool}
  {Spec.sequenceIn(List.append(&2, Nat, p, [m, a]), items) == Spec.bracketAlternative(Spec.itemAt(Spec.sequenceIn(p, items), m), a) : +List<Spec.Item>}

def sequence_snoc(p, m, a, items, even):
  match p:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      Empty.absurd({Spec.sequenceIn(List.append(&2, Nat, [x], [m, a]), items) == Spec.bracketAlternative(Spec.itemAt(Spec.sequenceIn([x], items), m), a) : +List<Spec.Item>}, Lemma.false_is_not_true(even))
    case Con{+x, Con{+y, +rest}}:
      sequence_snoc(rest, m, a, Spec.bracketAlternative(Spec.itemAt(items, x), y), even)

# Going one level deeper keeps SPEC's sequence and the engine's equal.
law deeper_eq:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +m: Nat
  for +a: Nat
  for even: {evenLength(prefix) == True{} : Bool}
  for same: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  {Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [m, a])) == Gll.seqAt(grammar, index, a <> (m <> rpath)) : +List<Spec.Item>}

def deeper_eq(grammar, index, prefix, rpath, m, a, even, same):
  +inner = Spec.sequenceAt(grammar, index, prefix)
  +s1 = sequence_snoc(prefix, m, a, Spec.rhsOf(grammar, index), even)
  +s2 = Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Spec.bracketAlternative(Spec.itemAt(v, m), a), inner, Gll.seqAt(grammar, index, rpath), same)
  +s3 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Spec.bracketAlternative(v, a), Spec.itemAt(Gll.seqAt(grammar, index, rpath), m), Gll.nthItem(Gll.seqAt(grammar, index, rpath), m), item_at_eq(Gll.seqAt(grammar, index, rpath), m))
  +s4 = alternative_eq(Gll.nthItem(Gll.seqAt(grammar, index, rpath), m), a)
  Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [m, a])), Spec.bracketAlternative(Spec.itemAt(inner, m), a), Gll.seqAt(grammar, index, a <> (m <> rpath)), s1,
    Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(inner, m), a), Spec.bracketAlternative(Spec.itemAt(Gll.seqAt(grammar, index, rpath), m), a), Gll.seqAt(grammar, index, a <> (m <> rpath)), s2,
      Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(Gll.seqAt(grammar, index, rpath), m), a), Spec.bracketAlternative(Gll.nthItem(Gll.seqAt(grammar, index, rpath), m), a), Gll.seqAt(grammar, index, a <> (m <> rpath)), s3, s4)))

# ======== SMALL FACTS FOR THE WALK ========

law reverse_twice:
  for a: +List<Nat>
  for +acc: +List<Nat>
  {Gll.reverseOnto(Gll.reverseOnto(a, acc), []) == Gll.reverseOnto(acc, a) : +List<Nat>}

def reverse_twice(a, acc):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      reverse_twice(rest, x <> acc)

# Two paths with the same reading order are the same path.
law reverse_injective:
  for +a: +List<Nat>
  for +b: +List<Nat>
  for e: {Gll.reverseOnto(a, []) == Gll.reverseOnto(b, []) : +List<Nat>}
  {a == b : +List<Nat>}

def reverse_injective(a, b, e):
  Equal.trans(+List<Nat>, a, Gll.reverseOnto(Gll.reverseOnto(a, []), []), b, Equal.sym(+List<Nat>, Gll.reverseOnto(Gll.reverseOnto(a, []), []), a, reverse_twice(a, [])),
    Equal.trans(+List<Nat>, Gll.reverseOnto(Gll.reverseOnto(a, []), []), Gll.reverseOnto(Gll.reverseOnto(b, []), []), b,
      Equal.cong(+List<Nat>, +List<Nat>, v => Gll.reverseOnto(v, []), Gll.reverseOnto(a, []), Gll.reverseOnto(b, []), e), reverse_twice(b, [])))

def lastOr(xs: +List<Nat>, d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{x, Nil{}}:
      x
    case Con{x, Con{y, rest}}:
      lastOr(y <> rest, d)

def initOf(xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      []
    case Con{x, Nil{}}:
      []
    case Con{x, Con{+y, +rest}}:
      x <> initOf(y <> rest)

law last_snoc:
  for p: +List<Nat>
  for +x: Nat
  for +d: Nat
  {lastOr(List.append(&2, Nat, p, [x]), d) == x : Nat}

def last_snoc(p, x, d):
  match p:
    case Nil{}:
      {==}
    case Con{y, Nil{}}:
      {==}
    case Con{y, Con{+z, +rest}}:
      last_snoc(z <> rest, x, d)

law init_snoc:
  for p: +List<Nat>
  for +x: Nat
  {initOf(List.append(&2, Nat, p, [x])) == p : +List<Nat>}

def init_snoc(p, x):
  match p:
    case Nil{}:
      {==}
    case Con{+y, Nil{}}:
      {==}
    case Con{+y, Con{+z, +rest}}:
      Equal.cong(+List<Nat>, +List<Nat>, v => y <> v, initOf(List.append(&2, Nat, z <> rest, [x])), z <> rest, init_snoc(z <> rest, x))

def bsrIndex(b: Spec.Bsr) -> Nat:
  match b:
    case Spec.Bsr{Spec.Slot{p, path}, i, k, j}:
      p

def bsrPath(b: Spec.Bsr) -> +List<Nat>:
  match b:
    case Spec.Bsr{Spec.Slot{p, path}, i, k, j}:
      path

def bsrEnd(b: Spec.Bsr) -> Nat:
  match b:
    case Spec.Bsr{Spec.Slot{p, path}, i, k, j}:
      j

# Membership in a joined list: in one of the parts.
law member_split:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, List.append(&2, Spec.Bsr, xs, ys)) == True{} : Bool}
  Either<{Spec.bsrMember(e, xs) == True{} : Bool}, {Spec.bsrMember(e, ys) == True{} : Bool}>

law member_split_rest:
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for c: Either<{Spec.bsrMember(e, rest) == True{} : Bool}, {Spec.bsrMember(e, ys) == True{} : Bool}>
  Either<{Spec.bsrMember(e, x <> rest) == True{} : Bool}, {Spec.bsrMember(e, ys) == True{} : Bool}>

def member_split_rest(e, x, rest, ys, c):
  match c:
    case Inl{inRest}:
      Inl{R.bsr_member_cons(e, x, rest, inRest)}
    case Inr{inYs}:
      Inr{inYs}

law member_split_pick:
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for c: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, List.append(&2, Spec.Bsr, rest, ys)) == True{} : Bool}>
  for later: {Spec.bsrMember(e, List.append(&2, Spec.Bsr, rest, ys)) == True{} : Bool} -> Either<{Spec.bsrMember(e, rest) == True{} : Bool}, {Spec.bsrMember(e, ys) == True{} : Bool}>
  Either<{Spec.bsrMember(e, x <> rest) == True{} : Bool}, {Spec.bsrMember(e, ys) == True{} : Bool}>

def member_split_pick(e, x, rest, ys, c, later):
  match c:
    case Inl{same}:
      +h = R.bsr_member_head(x, rest)
      Inl{Equal.trans(Bool, Spec.bsrMember(e, x <> rest), Spec.bsrMember(x, x <> rest), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, x <> rest), e, x, same), h)}
    case Inr{there}:
      member_split_rest(e, x, rest, ys, later(there))

def member_split(xs, ys, e, m):
  match xs:
    case Nil{}:
      Inr{m}
    case Con{+x, +rest}:
      member_split_pick(e, x, rest, ys, G.ebnf_member_cases(e, x, List.append(&2, Spec.Bsr, rest, ys), m),
        there => member_split(rest, ys, e, there))

# The items from the end of a sequence on: none.
law drop_all:
  for xs: +List<Spec.Item>
  {Gll.dropFrom(List.length(&2, Spec.Item, xs), xs) == [] : +List<Spec.Item>}

def drop_all(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      drop_all(rest)

# A forest that fits no items is empty.
law fits_none:
  for ts: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for fit: {Spec.fits(ts, grammar, []) == True{} : Bool}
  {ts == [] : +List<Spec.Tree>}

def fits_none(ts, grammar, fit):
  match ts:
    case Nil{}:
      {==}
    case Con{Spec.Leaf{k}, rest}:
      Empty.absurd({Spec.Leaf{k} <> rest == [] : +List<Spec.Tree>}, Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, c}, rest}:
      Empty.absurd({Spec.Node{q, c} <> rest == [] : +List<Spec.Tree>}, Lemma.false_is_not_true(fit))
    case Con{Spec.Pick{a, c}, rest}:
      Empty.absurd({Spec.Pick{a, c} <> rest == [] : +List<Spec.Tree>}, Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, rest}:
      Empty.absurd({Spec.Skip{} <> rest == [] : +List<Spec.Tree>}, Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{rs}, rest}:
      Empty.absurd({Spec.Loop{rs} <> rest == [] : +List<Spec.Tree>}, Lemma.false_is_not_true(fit))

# ======== THE WALK: WHERE A SEQUENCE ENDS IN A PARSE TREE, THE NEXT TOKEN FITS ========

def headOf(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      x

def tailOf(xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      []
    case Con{x, +rest}:
      rest

# What the walk concludes: the token at j0 is in the tables' context of the sequence.
def Fits(+grammar: +List<Spec.Production>, +t: Gll.Tables, +input: +List<Nat>, +index0: Nat, +rpath1: +List<Nat>, +j0: Nat) -> Data:
  {Gll.lsHas(List.get(&2, Nat, input, j0), Gll.contextAfter(grammar, t, index0, rpath1)) == True{} : Bool}

# What the walk needs. In a sequence: the forest fits the items from the dot on and ends at
# fin; the token at fin may come after the sequence; the FOLLOW check holds for it; and
# SPEC's sequence at the prefix is the engine's at the path. In the rounds of a loop at
# rpath = m <> outer: the forest is rounds of the loop's body and ends at fin, where what
# comes may come after the loop; the FOLLOW check holds around the loop; and seqPrefix is
# the prefix of the sequence around the loop.
def Ready(rounds: Bool, +grammar: +List<Spec.Production>, +t: Gll.Tables, +input: +List<Nat>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +seqPrefix: +List<Nat>, +dot: Nat, +k: Nat, +ff: Nat, +fin: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat} & {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool} & {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool} & {evenLength(prefix) == True{} : Bool} & {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Nat.add(k, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat} & {Pr.afterOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool} & {Pr.foLoop(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool} & {prefix == List.append(&2, Nat, seqPrefix, [headOf(rpath)]) : +List<Nat>} & {evenLength(seqPrefix) == True{} : Bool} & {Spec.sequenceAt(grammar, index, seqPrefix) == Gll.seqAt(grammar, index, tailOf(rpath)) : +List<Spec.Item>}

law either_case:
  for -A: Type
  for -B: Type
  for -C: Type
  for c: Either<A, B>
  for left: A -> C
  for right: B -> C
  C

def either_case(A, B, C, c, left, right):
  match c:
    case Inl{a}:
      left(a)
    case Inr{b}:
      right(b)

# The target is the step of a sequence's end, at slot 1 + dot of the walk's sequence, read
# up to e: then it is the last item, e is the sequence's end fin, and the context there is
# the one the walk carries.
law end_hit:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +fin: Nat
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +same: {Spec.at(index0, prefix0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0)), i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, e) : Spec.Bsr}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +finTs: {Nat.add(e, List.length(&2, Nat, Spec.leaves(ts))) == fin : Nat}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  Fits(grammar, t, input, index0, rpath1, j0)

def end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, e, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq):
  +len0 = List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0))
  +target = Spec.at(index0, prefix0, len0, i0, k0, j0)
  +here = Spec.at(index, prefix, 1n+dot, i, k, e)
  +eIndex = Equal.cong(Spec.Bsr, Nat, v => bsrIndex(v), target, here, same)
  +ePath = Equal.cong(Spec.Bsr, +List<Nat>, v => bsrPath(v), target, here, same)
  +eEnd = Equal.cong(Spec.Bsr, Nat, v => bsrEnd(v), target, here, same)
  +ePrefix = Equal.trans(+List<Nat>, prefix0, initOf(List.append(&2, Nat, prefix0, [len0])), prefix, Equal.sym(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), prefix0, init_snoc(prefix0, len0)),
    Equal.trans(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), initOf(List.append(&2, Nat, prefix, [1n+dot])), prefix, Equal.cong(+List<Nat>, +List<Nat>, v => initOf(v), List.append(&2, Nat, prefix0, [len0]), List.append(&2, Nat, prefix, [1n+dot]), ePath), init_snoc(prefix, 1n+dot)))
  +eLen = Equal.trans(Nat, len0, lastOr(List.append(&2, Nat, prefix0, [len0]), 0n), 1n+dot, Equal.sym(Nat, lastOr(List.append(&2, Nat, prefix0, [len0]), 0n), len0, last_snoc(prefix0, len0, 0n)),
    Equal.trans(Nat, lastOr(List.append(&2, Nat, prefix0, [len0]), 0n), lastOr(List.append(&2, Nat, prefix, [1n+dot]), 0n), 1n+dot, Equal.cong(+List<Nat>, Nat, v => lastOr(v, 0n), List.append(&2, Nat, prefix0, [len0]), List.append(&2, Nat, prefix, [1n+dot]), ePath), last_snoc(prefix, 1n+dot, 0n)))
  +seq = Gll.seqAt(grammar, index, rpath)
  +lenSeq = Equal.trans(Nat, len0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), List.length(&2, Spec.Item, seq),
    Equal.trans(Nat, len0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix0)), List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)),
      Equal.cong(Nat, Nat, v => List.length(&2, Spec.Item, Spec.sequenceAt(grammar, v, prefix0)), index0, index, eIndex),
      Equal.cong(+List<Nat>, Nat, v => List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, v)), prefix0, prefix, ePrefix)),
    Equal.cong(+List<Spec.Item>, Nat, v => List.length(&2, Spec.Item, v), Spec.sequenceAt(grammar, index, prefix), seq, seqEq))
  +dotLen = Equal.trans(Nat, 1n+dot, len0, List.length(&2, Spec.Item, seq), Equal.sym(Nat, len0, 1n+dot, eLen), lenSeq)
  +restNil = Equal.trans(+List<Spec.Item>, rest, G.dropItems(1n+dot, seq), [], Equal.sym(+List<Spec.Item>, G.dropItems(1n+dot, seq), rest, restEq),
    Equal.trans(+List<Spec.Item>, G.dropItems(1n+dot, seq), Gll.dropFrom(List.length(&2, Spec.Item, seq), seq), [], Equal.cong(Nat, +List<Spec.Item>, v => Gll.dropFrom(v, seq), 1n+dot, List.length(&2, Spec.Item, seq), dotLen), drop_all(seq)))
  +fitNil = Equal.trans(Bool, Spec.fits(ts, grammar, []), Spec.fits(ts, grammar, rest), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ts, grammar, v), [], rest, Equal.sym(+List<Spec.Item>, rest, [], restNil)), fitTs)
  +tsNil = fits_none(ts, grammar, fitNil)
  +eFin = Equal.trans(Nat, e, Nat.add(e, List.length(&2, Nat, Spec.leaves(ts))), fin,
    Equal.trans(Nat, e, Nat.add(e, 0n), Nat.add(e, List.length(&2, Nat, Spec.leaves(ts))), Equal.sym(Nat, Nat.add(e, 0n), e, Lemma.add_zero_right(e)),
      Equal.cong(+List<Spec.Tree>, Nat, v => Nat.add(e, List.length(&2, Nat, Spec.leaves(v))), [], ts, Equal.sym(+List<Spec.Tree>, ts, [], tsNil))), finTs)
  +j0Fin = Equal.trans(Nat, j0, e, fin, eEnd, eFin)
  +rSame = reverse_injective(rpath1, rpath, Equal.trans(+List<Nat>, Gll.reverseOnto(rpath1, []), prefix0, Gll.reverseOnto(rpath, []), rEq, Equal.trans(+List<Nat>, prefix0, prefix, Gll.reverseOnto(rpath, []), ePrefix, pEq)))
  +c1 = Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, j0), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), True{},
    Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.contextAfter(grammar, t, index0, rpath1)), j0, fin, j0Fin),
    Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), True{},
      Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, v, rpath1)), index0, index, eIndex),
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)), True{},
        Equal.cong(+List<Nat>, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, v)), rpath1, rpath, rSame), ctxF)))
  c1

# A step of the walk that is the target, ending at fin: the token at fin is in the context.
law at_fits:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +fin: Nat
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +same: {Spec.at(index0, prefix0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0)), i0, k0, j0) == Spec.at(index, prefix, d, i, k, e) : Spec.Bsr}
  for +eFin: {e == fin : Nat}
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  Fits(grammar, t, input, index0, rpath1, j0)

def at_fits(grammar, t, input, index, rpath, prefix, d, i, k, e, fin, index0, prefix0, i0, k0, j0, rpath1, same, eFin, pEq, ctxF, rEq):
  +len0 = List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0))
  +target = Spec.at(index0, prefix0, len0, i0, k0, j0)
  +here = Spec.at(index, prefix, d, i, k, e)
  +eIndex = Equal.cong(Spec.Bsr, Nat, v => bsrIndex(v), target, here, same)
  +ePath = Equal.cong(Spec.Bsr, +List<Nat>, v => bsrPath(v), target, here, same)
  +eEnd = Equal.cong(Spec.Bsr, Nat, v => bsrEnd(v), target, here, same)
  +ePrefix = Equal.trans(+List<Nat>, prefix0, initOf(List.append(&2, Nat, prefix0, [len0])), prefix, Equal.sym(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), prefix0, init_snoc(prefix0, len0)),
    Equal.trans(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), initOf(List.append(&2, Nat, prefix, [d])), prefix, Equal.cong(+List<Nat>, +List<Nat>, v => initOf(v), List.append(&2, Nat, prefix0, [len0]), List.append(&2, Nat, prefix, [d]), ePath), init_snoc(prefix, d)))
  +j0Fin = Equal.trans(Nat, j0, e, fin, eEnd, eFin)
  +rSame = reverse_injective(rpath1, rpath, Equal.trans(+List<Nat>, Gll.reverseOnto(rpath1, []), prefix0, Gll.reverseOnto(rpath, []), rEq, Equal.trans(+List<Nat>, prefix0, prefix, Gll.reverseOnto(rpath, []), ePrefix, pEq)))
  Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, j0), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), True{},
    Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.contextAfter(grammar, t, index0, rpath1)), j0, fin, j0Fin),
    Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), True{},
      Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, v, rpath1)), index0, index, eIndex),
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)), True{},
        Equal.cong(+List<Nat>, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, v)), rpath1, rpath, rSame), ctxF)))

# ======== THE FOLLOW WALK ========
#
# Walk a parse tree as SPEC.bend's `walk` does, with the invariants of PROOF_PRED in
# prediction mode. Wherever the walk lists the end step of a sequence (the target), the token
# there is in the tables' context for that sequence.

def target(+grammar: +List<Spec.Production>, +index0: Nat, +prefix0: +List<Nat>, +i0: Nat, +k0: Nat, +j0: Nat) -> Spec.Bsr:
  Spec.at(index0, prefix0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0)), i0, k0, j0)

def FollowIH(+grammar: +List<Spec.Production>, +t: Gll.Tables, +input: +List<Nat>, +forest: +List<Spec.Tree>, +index0: Nat, +prefix0: +List<Nat>, +i0: Nat, +k0: Nat, +j0: Nat, +rpath1: +List<Nat>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @seqPrefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @ff: Nat -> @fin: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> G.Spells(forest, input, k) -> Ready(rounds, grammar, t, input, forest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts) ->
    {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(forest, rounds, index, prefix, dot, i, k)) == True{} : Bool} -> Fits(grammar, t, input, index0, rpath1, j0)

# ---- The end of a sequence: only dot 0 has a step there ----

law empty_follow:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +fin: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.emptyStep(dot, index, prefix, i, k)) == True{} : Bool}
  Fits(grammar, t, input, index0, rpath1, j0)

def empty_follow(dot, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, i, k, fin, pEq, finEq, ctxF, hit):
  match dot:
    case 0n:

      either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 0n, i, k, k) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), []) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 0n, i, k, k), [], hit),
        same => at_fits(grammar, t, input, index, rpath, prefix, 0n, i, k, k, fin, index0, prefix0, i0, k0, j0, rpath1, same, Equal.trans(Nat, k, Nat.add(k, 0n), fin, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finEq), pEq, ctxF, rEq),
        none => Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), none)))
    case 1n+d:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))

# ---- A token ----

law leaf_follow:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +tok: Nat
  for +ts: +List<Spec.Tree>
  for +term: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Leaf{tok} <> ts))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +sp: G.Spells(Spec.Leaf{tok} <> ts, input, k)
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Leaf{tok} <> ts, grammar, Spec.Sym{Spec.Terminal{term}} <> rest) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Leaf{tok} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def leaf_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, tok, ts, term, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, restEq, fit, hit, ihTs):
  +fitTs = Lemma.and_true_right_side(Nat.is_eq(tok, term), Spec.fits(ts, grammar, rest), fit)
  +lts = Spec.leaves(ts)
  +finTs = Equal.trans(Nat, Nat.add(1n+k, List.length(&2, Nat, lts)), Nat.add(k, 1n+List.length(&2, Nat, lts)), fin, Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, lts)), 1n+Nat.add(k, List.length(&2, Nat, lts)), Lemma.add_succ_right(k, List.length(&2, Nat, lts))), finEq)

  either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, 1n+k) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), hit),
    same => end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, 1n+k, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq),
    there => ihTs(False{}, index, rpath, prefix, seqPrefix, 1n+dot, i, 1n+k, ff, fin, rest, Spec.Group{}, [], pEq, G.leaf_rest(input, k, tok, lts, sp), (restEq, (fitTs, (finTs, (ctxF, (foF, (even, seqEq)))))), there))
# ---- A nonterminal ----

law node_follow:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def node_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, q, ch, ts, x, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, fit, hit, ihCh, ihTs):
  +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
  +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
  +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  +fitTs = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit)
  +lch = Spec.leaves(ch)
  +lts = Spec.leaves(ts)
  +e1 = Nat.add(k, List.length(&2, Nat, lch))
  +finTs = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), fin, G.end_split(k, lch, lts), finEq)
  +spTs = G.spells_second(input, k, lch, lts, sp)
  +spCh = G.spells_first(input, k, lch, lts, sp)
  +fitDrop = Equal.trans(Bool, Spec.fits(ts, grammar, G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(ts, grammar, rest), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ts, grammar, v), G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)), rest, restEq), fitTs)
  +ctxCh = Pr.ctx_node(Gll.Predict{t}, grammar, start, input, index, rpath, dot, ff, x, q, ts, e1, fin, po, foF, itemEq, lhsOk, fitDrop, spTs, finTs, ctxF)
  +foCh = Pr.fo_node(Gll.Predict{t}, grammar, start, q, x, po, lhsOk)
  either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, e1) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1))) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 1n+dot, i, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)), hit),
    same => end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, e1, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq),
    there => 
      either_case({Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ch, False{}, q, [], 0n, k, k)) == True{} : Bool}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), member_split(Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1), target(grammar, index0, prefix0, i0, k0, j0), there),
        inA => ihCh(False{}, q, [], [], [], 0n, k, k, Gll.nestFuel(), e1, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, spCh, ({==}, (fitCh, ({==}, (ctxCh, (foCh, ({==}, {==})))))), inA),
        inB => ihTs(False{}, index, rpath, prefix, seqPrefix, 1n+dot, i, e1, ff, fin, rest, Spec.Group{}, [], pEq, spTs, (restEq, (fitTs, (finTs, (ctxF, (foF, (even, seqEq)))))), inB)))

# ---- A ( ) or [ ] that matched ----

law pick_follow:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +isA: {Spec.isAlt(balts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def pick_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, ts, bkind, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, isA, fitCh, fitTs, hit, ihCh, ihTs):
  +lch = Spec.leaves(ch)
  +lts = Spec.leaves(ts)
  +e1 = Nat.add(k, List.length(&2, Nat, lch))
  +finTs = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), fin, G.end_split(k, lch, lts), finEq)
  +spTs = G.spells_second(input, k, lch, lts, sp)
  +spCh = G.spells_first(input, k, lch, lts, sp)
  +fitDrop = Equal.trans(Bool, Spec.fits(ts, grammar, G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(ts, grammar, rest), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ts, grammar, v), G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)), rest, restEq), fitTs)
  +ctxCh = Pr.ctx_pick(Gll.Predict{t}, grammar, start, input, index, rpath, dot, a, ts, e1, fin, po, fitDrop, spTs, finTs, ctxF)
  +foCh = Pr.fo_pick(Gll.Predict{t}, ff, grammar, index, rpath, dot, bkind, balts, a, foF, itemEq, isA)
  +altEq = G.alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq)
  +evenCh = Equal.trans(Bool, evenLength(List.append(&2, Nat, prefix, [dot, a])), evenLength(prefix), True{}, even_snoc(prefix, dot, a), even)
  +seqCh = deeper_eq(grammar, index, prefix, rpath, dot, a, even, seqEq)
  either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, e1) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1))) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 1n+dot, i, k, e1), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)), hit),
    same => end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, e1, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq),
    there => 
      either_case({Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)) == True{} : Bool}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), member_split(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1), target(grammar, index0, prefix0, i0, k0, j0), there),
        inA => ihCh(False{}, index, a <> (dot <> rpath), List.append(&2, Nat, prefix, [dot, a]), [], 0n, k, k, Adm.pred2(ff), e1, Spec.altOf(balts, a), Spec.Group{}, [], G.prefix_ext(rpath, prefix, [dot, a], pEq), spCh, (altEq, (fitCh, ({==}, (ctxCh, (foCh, (evenCh, seqCh)))))), inA),
        inB => ihTs(False{}, index, rpath, prefix, seqPrefix, 1n+dot, i, e1, ff, fin, rest, Spec.Group{}, [], pEq, spTs, (restEq, (fitTs, (finTs, (ctxF, (foF, (even, seqEq)))))), inB)))

# ---- A skipped [ ] or an empty item ----

law skip_follow:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Skip{} <> ts))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +sp: G.Spells(Spec.Skip{} <> ts, input, k)
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def skip_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, ts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, restEq, fitTs, hit, ihTs):
  +finTs = finEq
  either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, k) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), hit),
    same => end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, k, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq),
    there => ihTs(False{}, index, rpath, prefix, seqPrefix, 1n+dot, i, k, ff, fin, rest, Spec.Group{}, [], pEq, sp, (restEq, (fitTs, (finTs, (ctxF, (foF, (even, seqEq)))))), there))

# ---- A loop ----

law loop_follow:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +sp: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihRs: FollowIH(grammar, t, input, rs, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def loop_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, rs, ts, bkind, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, loopOk, fitRs, fitTs, hit, ihRs, ihTs):
  +lch = Spec.leaves(rs)
  +lts = Spec.leaves(ts)
  +e1 = Nat.add(k, List.length(&2, Nat, lch))
  +finTs = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), fin, G.end_split(k, lch, lts), finEq)
  +spTs = G.spells_second(input, k, lch, lts, sp)
  +spCh = G.spells_first(input, k, lch, lts, sp)
  +fitDrop = Equal.trans(Bool, Spec.fits(ts, grammar, G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath))), Spec.fits(ts, grammar, rest), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ts, grammar, v), G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)), rest, restEq), fitTs)
  +afterRs = Pr.after_loop(Gll.Predict{t}, grammar, start, input, index, rpath, dot, ts, e1, fin, po, fitDrop, spTs, finTs, ctxF)
  either_case({target(grammar, index0, prefix0, i0, k0, j0) == Spec.at(index, prefix, 1n+dot, i, k, e1) : Spec.Bsr}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1))) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_member_cases(target(grammar, index0, prefix0, i0, k0, j0), Spec.at(index, prefix, 1n+dot, i, k, e1), List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)), hit),
    same => end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, e1, ts, rest, fin, index0, prefix0, i0, k0, j0, rpath1, same, restEq, fitTs, finTs, seqEq, pEq, ctxF, rEq),
    there => 
      either_case({Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)) == True{} : Bool}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), member_split(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1), target(grammar, index0, prefix0, i0, k0, j0), there),
        inA => ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), prefix, 0n, k, k, ff, e1, [], bkind, balts, G.prefix_ext(rpath, prefix, [dot], pEq), spCh, (itemEq, (loopOk, (fitRs, ({==}, (afterRs, (foF, ({==}, (even, seqEq)))))))), inA),
        inB => ihTs(False{}, index, rpath, prefix, seqPrefix, 1n+dot, i, e1, ff, fin, rest, Spec.Group{}, [], pEq, spTs, (restEq, (fitTs, (finTs, (ctxF, (foF, (even, seqEq)))))), inB)))
# ---- A round of a loop ----

law round_follow:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest))) == fin : Nat}
  for +after: {Pr.afterOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foL: {Pr.foLoop(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +preEq: {prefix == List.append(&2, Nat, seqPrefix, [headOf(rpath)]) : +List<Nat>}
  for +evenS: {evenLength(seqPrefix) == True{} : Bool}
  for +seqEqS: {Spec.sequenceAt(grammar, index, seqPrefix) == Gll.seqAt(grammar, index, tailOf(rpath)) : +List<Spec.Item>}
  for +itemEq: {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihRest: FollowIH(grammar, t, input, rest, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def round_follow(rpath, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, rest, kind, alts, pEq, sp, finEq, after, foL, preEq, evenS, seqEqS, itemEq, loopOk, isA, fitCh, fitRest, hit, ihCh, ihRest):
  match rpath:
    case Nil{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      +remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
      +lch = Spec.leaves(ch)
      +lrest = Spec.leaves(rest)
      +e1 = Nat.add(k, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, k, lch, lrest, sp)
      +spRest = G.spells_second(input, k, lch, lrest, sp)
      +finRest = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrest)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), fin, G.end_split(k, lch, lrest), finEq)
      +ctxCh = Pr.ctx_round(Gll.Predict{t}, grammar, start, input, index, m <> outer, a, kind, alts, rest, e1, fin, po, itemEq, loopOk, after, fitRest, spRest, finRest)
      +foCh = Pr.fo_round(Gll.Predict{t}, ff, grammar, index, m <> outer, kind, alts, a, foL, itemEq, isA)
      +longer = List.append(&2, Nat, seqPrefix, [m, a])
      +eqP = Equal.trans(+List<Nat>, List.append(&2, Nat, prefix, [a]), List.append(&2, Nat, List.append(&2, Nat, seqPrefix, [m]), [a]), longer,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [a]), prefix, List.append(&2, Nat, seqPrefix, [m]), preEq),
        G.nat_append_assoc(seqPrefix, [m], [a]))
      +evenCh = Equal.trans(Bool, evenLength(List.append(&2, Nat, prefix, [a])), evenLength(longer), True{}, Equal.cong(+List<Nat>, Bool, v => evenLength(v), List.append(&2, Nat, prefix, [a]), longer, eqP),
        Equal.trans(Bool, evenLength(longer), evenLength(seqPrefix), True{}, even_snoc(seqPrefix, m, a), evenS))
      +seqCh = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [a])), Spec.sequenceAt(grammar, index, longer), Gll.seqAt(grammar, index, a <> (m <> outer)),
        Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), List.append(&2, Nat, prefix, [a]), longer, eqP),
        deeper_eq(grammar, index, seqPrefix, outer, m, a, evenS, seqEqS))
      either_case({Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k)) == True{} : Bool}, {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(rest, True{}, index, prefix, 0n, i, e1)) == True{} : Bool}, Fits(grammar, t, input, index0, rpath1, j0), member_split(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, i, k), Spec.walk(rest, True{}, index, prefix, 0n, i, e1), target(grammar, index0, prefix0, i0, k0, j0), hit),
        inA => ihCh(False{}, index, a <> (m <> outer), List.append(&2, Nat, prefix, [a]), [], 0n, i, k, Adm.pred2(ff), e1, Spec.altOf(alts, a), Spec.Group{}, [], G.prefix_ext(m <> outer, prefix, [a], pEq), spCh, (remCh, (fitCh, ({==}, (ctxCh, (foCh, (evenCh, seqCh)))))), inA),
        inB => ihRest(True{}, index, m <> outer, prefix, seqPrefix, 0n, i, e1, ff, fin, [], kind, alts, pEq, spRest, (itemEq, (loopOk, (fitRest, (finRest, (after, (foL, (preEq, (evenS, seqEqS)))))))), inB))
law leaf_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +tok: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Leaf{tok} <> ts, input, k)
  for ready: Ready(False{}, grammar, t, input, Spec.Leaf{tok} <> ts, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Leaf{tok} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def leaf_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, tok, ts, pEq, sp, ready, hit, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{term}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{tok} <> ts, grammar, Spec.Sym{Spec.Terminal{term}} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{term}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{term}}, rest, rem)
          leaf_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, tok, ts, term, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, restEq, fit, hit, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))

law node_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Node{q, ch} <> ts, input, k)
  for ready: Ready(False{}, grammar, t, input, Spec.Node{q, ch} <> ts, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def node_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, q, ch, ts, pEq, sp, ready, hit, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          node_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, q, ch, ts, x, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, fit, hit, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))

law pick_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> ts, input, k)
  for ready: Ready(False{}, grammar, t, input, Spec.Pick{a, ch} <> ts, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def pick_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, ts, pEq, sp, ready, hit, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +hP = Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, rest), fit)
          pick_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, ts, Spec.Group{}, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(hP, Spec.fits(ts, grammar, rest), fit), hit, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +hP = Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, rest), fit)
          +altOk = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          pick_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, ts, Spec.Optional{}, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), altOk), Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(hP, Spec.fits(ts, grammar, rest), fit), hit, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))

law skip_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Skip{} <> ts, input, k)
  for ready: Ready(False{}, grammar, t, input, Spec.Skip{} <> ts, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def skip_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, ts, pEq, sp, ready, hit, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          skip_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, ts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, restEq, fit, hit, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          skip_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, ts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, restEq, fit, hit, ihTs)

law loop_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Loop{rs} <> ts, input, k)
  for ready: Ready(False{}, grammar, t, input, Spec.Loop{rs} <> ts, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihRs: FollowIH(grammar, t, input, rs, index0, prefix0, i0, k0, j0, rpath1)
  for ihTs: FollowIH(grammar, t, input, ts, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def loop_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, rs, ts, pEq, sp, ready, hit, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+term}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Closure{}, rs)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          loop_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, rs, ts, Spec.Closure{}, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, {==}, Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), both), Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), hit, ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Positive{}, rs)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          loop_follow(grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, rs, ts, Spec.Positive{}, balts, rest, pEq, finEq, ctxF, foF, even, seqEq, sp, itemEq, restEq, {==}, Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), both), Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), hit, ihRs, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), Lemma.false_is_not_true(fit0))

law round_disp:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for ready: Ready(True{}, grammar, t, input, Spec.Pick{a, ch} <> rest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, [], kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k)) == True{} : Bool}
  for ihCh: FollowIH(grammar, t, input, ch, index0, prefix0, i0, k0, j0, rpath1)
  for ihRest: FollowIH(grammar, t, input, rest, index0, prefix0, i0, k0, j0, rpath1)
  Fits(grammar, t, input, index0, rpath1, j0)

def round_disp(rpath, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, rest, pEq, sp, ready, hit, ihCh, ihRest):
  match ready:
    case (itemEq, (loopOk, (fit0, (finEq, (after, (foL, (preEq, (evenS, seqEqS)))))))):
      +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +R = Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}))
      +hOk = Lemma.and_true_left(h, R, fit)
      round_follow(rpath, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, rest, kind, alts, pEq, sp, finEq, after, foL, preEq, evenS, seqEqS, itemEq, loopOk,
        Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(h, R, fit), hit, ihCh, ihRest)

# Wherever the walk of a parse tree lists the end step of a sequence, the token where it
# ends is in the tables' context for that sequence.
law follow_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for ready: Ready(rounds, grammar, t, input, forest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
  for +hit: {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(forest, rounds, index, prefix, dot, i, k)) == True{} : Bool}
  Fits(grammar, t, input, index0, rpath1, j0)

def follow_walk(forest, rounds, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, items, kind, alts, pEq, sp, ready, hit):
  match forest rounds:
    case Nil{} False{}:
      match ready:
        case (rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq)))))):
          empty_follow(dot, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, i, k, fin, pEq, finEq, ctxF, hit)
    case Nil{} True{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))
    case Con{Spec.Leaf{+tok}, +ts} False{}:
      leaf_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, tok, ts, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ts, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      node_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, q, ch, ts, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ch, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)), (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ts, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      pick_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, ts, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ch, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)), (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ts, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Skip{}, +ts} False{}:
      skip_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, ts, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ts, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      loop_disp(items, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, rs, ts, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(rs, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)), (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ts, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      round_disp(rpath, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, index, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, rest, pEq, sp, ready, hit, (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(ch, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)), (ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(rest, ri, grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx)))
    case Con{Spec.Leaf{tok}, rest} True{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))
    case Con{Spec.Node{q, ch}, rest} True{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))
    case Con{Spec.Skip{}, rest} True{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))
    case Con{Spec.Loop{rs}, rest} True{}:
      Empty.absurd(Fits(grammar, t, input, index0, rpath1, j0), G.ebnf_not_in_empty(target(grammar, index0, prefix0, i0, k0, j0), hit))

# ======== EXACT SETS ARE IN THE TABLES ========

law follow_at_tree:
  for tree: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for +input: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for +hit: {Spec.bsrMember(Spec.at(index, prefix, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index, prefix)), i, k, j), Spec.steps(tree, 0n)) == True{} : Bool}
  for +nextEq: {List.get(&2, Nat, input, j) == next : Maybe<&2, Nat>}
  {Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}

def follow_at_tree(tree, grammar, start, t, po, index, prefix, rpath, rEq, next, input, i, k, j, fitting, spelled, hit, nextEq):
      match tree:
        case Spec.Leaf{kind}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Node{+q, +ch}:
          +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, True{}, fitting)
          +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +lch = Spec.leaves(ch)
          +spCh = G.root_spells(input, q, ch, spelled)
          +sameL = Equal.trans(+List<Nat>, lch, List.append(&2, Nat, lch, []), input, Equal.sym(+List<Nat>, List.append(&2, Nat, lch, []), lch, Lemma.append_nil_right(lch)), spelled)
          +finCh = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), lch, input, sameL)
          +ctxCh = Pr.root_ctx(Gll.Predict{t}, grammar, start, input, q, po, lhsOk)
          +foCh = Pr.fo_node(Gll.Predict{t}, grammar, start, q, start, po, lhsOk)
          +got = follow_walk(ch, False{}, grammar, start, t, po, input, index, prefix, i, k, j, rpath, rEq, q, [], [], [], 0n, 0n, 0n, Gll.nestFuel(), List.length(&2, Nat, input), Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, spCh, ({==}, (fitCh, (finCh, (ctxCh, (foCh, ({==}, {==})))))), hit)
          Equal.trans(Bool, Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)), Gll.lsHas(List.get(&2, Nat, input, j), Gll.contextAfter(grammar, t, index, rpath)), True{},
            Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.contextAfter(grammar, t, index, rpath)), next, List.get(&2, Nat, input, j), Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, input, j), next, nextEq)), got)
        case Spec.Pick{a, ch}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Skip{}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
        case Spec.Loop{rs}:
          Empty.absurd({Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}, Lemma.false_is_not_true(fitting))

# FOLLOW from parse trees: the token is in the tables' context for the sequence.
law follow_at_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for fol: Spec.FollowAt(grammar, start, index, prefix, next)
  {Gll.lsHas(next, Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}

def follow_at_sound(grammar, start, t, po, index, prefix, rpath, rEq, next, fol):
  match fol:
    case (input, (tree, (i, (k, (j, (fitting, (spelled, (hit, nextEq)))))))):
      follow_at_tree(tree, grammar, start, t, po, index, prefix, rpath, rEq, next, input, i, k, j, fitting, spelled, hit, nextEq)

# FIRST from derivations: the token is in the tables' FIRST of the items.
law first_of_sound:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +items: +List<Spec.Item>
  for next: Maybe<&2, Nat>
  for f: Spec.FirstOf(grammar, items, next)
  {Gll.lsHas(next, Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}

def first_of_sound(grammar, t, pc, items, next, f):
  match next:
    case None{}:
      Empty.absurd({Gll.lsHas(None{}, Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}, f)
    case Some{+token}:
      match f:
        case (rest, (forest, (fit, lv))):
          Tab.first_sound(forest, Gll.nestFuel(), items, grammar, t, pc, fit, token, rest, lv)

law predicts_by:
  for viaFirst: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for by: Spec.PredictsBy(viaFirst, grammar, start, items, index, prefix, next)
  {Gll.lsHas(next, Gll.restOr(Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath))) == True{} : Bool}

def predicts_by(viaFirst, grammar, start, t, po, items, index, prefix, rpath, rEq, next, by):
  match viaFirst:
    case True{}:
      Sets.rest_or_first(next, Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath),
        first_of_sound(grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), items, next, by))
    case False{}:
      match by:
        case ((forest, (fit, empty)), fol):
          Sets.rest_or_after(next, Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath),
            Tab.nul_sound(forest, Gll.nestFuel(), items, grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), fit, empty),
            follow_at_sound(grammar, start, t, po, index, prefix, rpath, rEq, next, fol))

# PREDICT: the token is in the tables' set for the items followed by the sequence's end.
law predicts_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +items: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +rpath: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath, []) == prefix : +List<Nat>}
  for +next: Maybe<&2, Nat>
  for p: Spec.Predicts(grammar, start, items, index, prefix, next)
  {Gll.lsHas(next, Gll.restOr(Gll.infoItems(items, t), Gll.contextAfter(grammar, t, index, rpath))) == True{} : Bool}

def predicts_sound(grammar, start, t, po, items, index, prefix, rpath, rEq, next, p):
  match p:
    case (viaFirst, by):
      predicts_by(viaFirst, grammar, start, t, po, items, index, prefix, rpath, rEq, next, by)


# ======== EVERY CHOICE POINT IS CHECKED ========

# ---- Lists of conflicts that are not empty ----

law nonempty_left:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, xs) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}

def nonempty_left(xs, ys, h):
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, ys) == False{} : Bool}, Lemma.true_is_not_false(h))
    case Con{x, rest}:
      {==}

law nonempty_right:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, ys) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}

def nonempty_right(xs, ys, h):
  match xs:
    case Nil{}:
      h
    case Con{x, rest}:
      {==}

law meet_pick_true:
  for meet: Bool
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +rest: +List<LL1.Conflict>
  for e: {meet == True{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.meetPick(meet, point, first, second, rest)) == False{} : Bool}

def meet_pick_true(meet, point, first, second, rest, e):
  match meet:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, rest) == False{} : Bool}, Lemma.false_is_not_true(e))

law meet_pick_rest:
  for meet: Bool
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +rest: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, rest) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.meetPick(meet, point, first, second, rest)) == False{} : Bool}

def meet_pick_rest(meet, point, first, second, rest, h):
  match meet:
    case True{}:
      {==}
    case False{}:
      h

# ---- Two sets that admit the same token meet ----

law in_nonempty:
  for +x: Nat
  for xs: +List<Nat>
  for h: {Gll.natIn(x, xs) == True{} : Bool}
  {Bool.not(List.is_empty(&2, Nat, xs)) == True{} : Bool}

def in_nonempty(x, xs, h):
  match xs:
    case Nil{}:
      Empty.absurd({Bool.not(List.is_empty(&2, Nat, [])) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{y, rest}:
      {==}

law has_nonempty:
  for next: Maybe<&2, Nat>
  for s: Gll.LSet
  for h: {Gll.lsHas(next, s) == True{} : Bool}
  {LL1.lsNonEmpty(s) == True{} : Bool}

def has_nonempty(next, s, h):
  match next s:
    case None{} Gll.LSet{+any, +tokens, +end}:
      either_case({any == True{} : Bool}, {end == True{} : Bool}, {LL1.lsNonEmpty(Gll.LSet{any, tokens, end}) == True{} : Bool}, Lemma.or_true_cases(any, end, h),
        ea => Lemma.or_true_left_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), ea),
        ee => Lemma.or_true_right_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), Lemma.or_true_left_intro(end, Bool.not(List.is_empty(&2, Nat, tokens)), ee)))
    case Some{+tok} Gll.LSet{+any, +tokens, +end}:
      either_case({any == True{} : Bool}, {Gll.natIn(tok, tokens) == True{} : Bool}, {LL1.lsNonEmpty(Gll.LSet{any, tokens, end}) == True{} : Bool}, Lemma.or_true_cases(any, Gll.natIn(tok, tokens), h),
        ea => Lemma.or_true_left_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), ea),
        et => Lemma.or_true_right_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), Lemma.or_true_right_intro(end, Bool.not(List.is_empty(&2, Nat, tokens)), in_nonempty(tok, tokens, et))))

law tokens_meet:
  for +tok: Nat
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for hx: {Gll.natIn(tok, xs) == True{} : Bool}
  for +hy: {Gll.natIn(tok, ys) == True{} : Bool}
  {LL1.tokensMeet(xs, ys) == True{} : Bool}

def tokens_meet(tok, xs, ys, hx, hy):
  match xs:
    case Nil{}:
      Empty.absurd({LL1.tokensMeet([], ys) == True{} : Bool}, Lemma.false_is_not_true(hx))
    case Con{+x, +rest}:
      either_case({Nat.is_eq(tok, x) == True{} : Bool}, {Gll.natIn(tok, rest) == True{} : Bool}, {LL1.tokensMeet(x <> rest, ys) == True{} : Bool}, Lemma.or_true_cases(Nat.is_eq(tok, x), Gll.natIn(tok, rest), hx),
        here => Lemma.or_true_left_intro(Gll.natIn(x, ys), LL1.tokensMeet(rest, ys),
          Equal.trans(Bool, Gll.natIn(x, ys), Gll.natIn(tok, ys), True{}, Equal.cong(Nat, Bool, v => Gll.natIn(v, ys), x, tok, Equal.sym(Nat, tok, x, Lemma.nat_eq_sound(tok, x, here))), hy)),
        later => Lemma.or_true_right_intro(Gll.natIn(x, ys), LL1.tokensMeet(rest, ys), tokens_meet(tok, rest, ys, later, hy)))

law meet_of_has:
  for next: Maybe<&2, Nat>
  for a: Gll.LSet
  for b: Gll.LSet
  for +ha: {Gll.lsHas(next, a) == True{} : Bool}
  for +hb: {Gll.lsHas(next, b) == True{} : Bool}
  {LL1.lsMeet(a, b) == True{} : Bool}

def meet_of_has(next, a, b, ha, hb):
  match next a b:
    case None{} Gll.LSet{+a1, +t1, +e1} Gll.LSet{+a2, +t2, +e2}:
      +sa = {Gll.LSet{a1, t1, e1} : Gll.LSet}
      +sb = {Gll.LSet{a2, t2, e2} : Gll.LSet}
      +m1 = Bool.and(a1, LL1.lsNonEmpty(sb))
      +m2 = Bool.and(a2, LL1.lsNonEmpty(sa))
      +m3 = Bool.and(e1, e2)
      +m4 = LL1.tokensMeet(t1, t2)
      either_case({a1 == True{} : Bool}, {e1 == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a1, e1, ha),
        any1 => Lemma.or_true_left_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.and_true_intro(a1, LL1.lsNonEmpty(sb), any1, has_nonempty(None{}, sb, hb))),
        end1 => either_case({a2 == True{} : Bool}, {e2 == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a2, e2, hb),
          any2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_left_intro(m2, Bool.or(m3, m4), Lemma.and_true_intro(a2, LL1.lsNonEmpty(sa), any2, has_nonempty(None{}, sa, ha)))),
          end2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_right_intro(m2, Bool.or(m3, m4), Lemma.or_true_left_intro(m3, m4, Lemma.and_true_intro(e1, e2, end1, end2))))))
    case Some{+tok} Gll.LSet{+a1, +t1, +e1} Gll.LSet{+a2, +t2, +e2}:
      +sa = {Gll.LSet{a1, t1, e1} : Gll.LSet}
      +sb = {Gll.LSet{a2, t2, e2} : Gll.LSet}
      +m1 = Bool.and(a1, LL1.lsNonEmpty(sb))
      +m2 = Bool.and(a2, LL1.lsNonEmpty(sa))
      +m3 = Bool.and(e1, e2)
      +m4 = LL1.tokensMeet(t1, t2)
      either_case({a1 == True{} : Bool}, {Gll.natIn(tok, t1) == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a1, Gll.natIn(tok, t1), ha),
        any1 => Lemma.or_true_left_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.and_true_intro(a1, LL1.lsNonEmpty(sb), any1, has_nonempty(Some{tok}, sb, hb))),
        in1 => either_case({a2 == True{} : Bool}, {Gll.natIn(tok, t2) == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a2, Gll.natIn(tok, t2), hb),
          any2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_left_intro(m2, Bool.or(m3, m4), Lemma.and_true_intro(a2, LL1.lsNonEmpty(sa), any2, has_nonempty(Some{tok}, sa, ha)))),
          in2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_right_intro(m2, Bool.or(m3, m4), Lemma.or_true_right_intro(m3, m4, tokens_meet(tok, t1, t2, in1, in2))))))

# ---- A choice in a list, with a set that admits the token ----

def HasAt(+c: Nat, +next: Maybe<&2, Nat>, xs: +List<LL1.Predicted>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{LL1.Predicted{c2, s2}, rest}:
      Either<({c == c2 : Nat} & {Gll.lsHas(next, s2) == True{} : Bool}), HasAt(c, next, rest)>

law has_append_left:
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for xs: +List<LL1.Predicted>
  for +ys: +List<LL1.Predicted>
  for h: HasAt(c, next, xs)
  HasAt(c, next, List.append(&2, LL1.Predicted, xs, ys))

def has_append_left(c, next, xs, ys, h):
  match xs:
    case Nil{}:
      Empty.absurd(HasAt(c, next, ys), h)
    case Con{LL1.Predicted{+c2, +s2}, +rest}:
      match h:
        case Inl{here}:
          Inl{here}
        case Inr{later}:
          Inr{has_append_left(c, next, rest, ys, later)}

law has_append_right:
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for xs: +List<LL1.Predicted>
  for +ys: +List<LL1.Predicted>
  for h: HasAt(c, next, ys)
  HasAt(c, next, List.append(&2, LL1.Predicted, xs, ys))

def has_append_right(c, next, xs, ys, h):
  match xs:
    case Nil{}:
      h
    case Con{LL1.Predicted{+c2, +s2}, +rest}:
      Inr{has_append_right(c, next, rest, ys, h)}

# One choice against the choices after it.
law with_hit:
  for +point: Spec.ChoicePoint
  for +c: Nat
  for +s: Gll.LSet
  for rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for +c2: Nat
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  for h: HasAt(c2, next, rest)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsWith(point, LL1.Predicted{c, s}, rest)) == False{} : Bool}

def with_hit(point, c, s, rest, next, c2, hs, h):
  match rest:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsWith(point, LL1.Predicted{c, s}, [])) == False{} : Bool}, h)
    case Con{LL1.Predicted{+c3, +s3}, +r}:
      match h:
        case Inl{here}:
          match here:
            case (eq, hs3):
              meet_pick_true(LL1.lsMeet(s, s3), point, c, c3, LL1.conflictsWith(point, LL1.Predicted{c, s}, r), meet_of_has(next, s, s3, hs, hs3))
        case Inr{later}:
          meet_pick_rest(LL1.lsMeet(s, s3), point, c, c3, LL1.conflictsWith(point, LL1.Predicted{c, s}, r), with_hit(point, c, s, r, next, c2, hs, later))

# Two different choices in the list, both admitting the token: a conflict.
law among_hit:
  for +point: Spec.ChoicePoint
  for xs: +List<LL1.Predicted>
  for +c1: Nat
  for +c2: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(c1, c2) == False{} : Bool}
  for h1: HasAt(c1, next, xs)
  for h2: HasAt(c2, next, xs)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, xs)) == False{} : Bool}

def among_hit(point, xs, c1, c2, next, neq, h1, h2):
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, [])) == False{} : Bool}, h1)
    case Con{LL1.Predicted{+c, +s}, +rest}:
      match h1:
        case Inl{here1}:
          match here1:
            case (e1, hs1):
              match h2:
                case Inl{here2}:
                  match here2:
                    case (e2, hs2):
                      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, LL1.Predicted{c, s} <> rest)) == False{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Nat.is_eq(c1, c2), True{}, Equal.sym(Bool, Nat.is_eq(c1, c2), False{}, neq),
                        Lemma.nat_eq_of_eq(c1, c2, Equal.trans(Nat, c1, c, c2, e1, Equal.sym(Nat, c2, c, e2))))))
                case Inr{later2}:
                  nonempty_left(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), with_hit(point, c, s, rest, next, c2, hs1, later2))
        case Inr{later1}:
          match h2:
            case Inl{here2}:
              match here2:
                case (e2, hs2):
                  nonempty_left(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), with_hit(point, c, s, rest, next, c1, hs2, later1))
            case Inr{later2}:
              nonempty_right(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), among_hit(point, rest, c1, c2, next, neq, later1, later2))

# ---- Nonterminals ----

law lt_succ_self:
  for x: Nat
  {Nat.is_lt(x, 1n+x) == True{} : Bool}

def lt_succ_self(x):
  match x:
    case 0n:
      {==}
    case 1n+y:
      lt_succ_self(y)

law lt_max_left:
  for x: Nat
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(x, a) == True{} : Bool}
  {Nat.is_lt(x, Nat.max(a, b)) == True{} : Bool}

def lt_max_left(x, a, b, h):
  match x a b:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(x, Nat.max(0n, b)) == True{} : Bool}, Lemma.lt_zero_false(x, h))
    case 0n 1n+c 0n:
      {==}
    case 0n 1n+c 1n+d:
      {==}
    case 1n+y 1n+c 0n:
      h
    case 1n+y 1n+c 1n+d:
      lt_max_left(y, c, d, h)

law lt_max_right:
  for x: Nat
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(x, b) == True{} : Bool}
  {Nat.is_lt(x, Nat.max(a, b)) == True{} : Bool}

def lt_max_right(x, a, b, h):
  match x a b:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(x, Nat.max(a, 0n)) == True{} : Bool}, Lemma.lt_zero_false(x, h))
    case 0n 0n 1n+d:
      {==}
    case 0n 1n+c 1n+d:
      {==}
    case 1n+y 0n 1n+d:
      h
    case 1n+y 1n+c 1n+d:
      lt_max_right(y, c, d, h)

# A nonterminal with an alternate is counted by ntCount.
law lhs_below:
  for grammar: +List<Spec.Production>
  for q: Nat
  for +x: Nat
  for e: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {Nat.is_lt(x, First.ntCount(grammar)) == True{} : Bool}

def lhs_below(grammar, q, x, e):
  match grammar q:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(x, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, rhs}, +rest} 0n:
      +same = Lemma.nat_eq_sound(lhs, x, e)
      lt_max_left(x, 1n+lhs, First.ntCount(rest),
        Equal.trans(Bool, Nat.is_lt(x, 1n+lhs), Nat.is_lt(x, 1n+x), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(x, 1n+v), lhs, x, same), lt_succ_self(x)))
    case Con{Spec.Production{+lhs, rhs}, +rest} 1n+(+p):
      lt_max_right(x, 1n+lhs, First.ntCount(rest), lhs_below(rest, p, x, e))

# An alternate of a nonterminal that predicts the token: it is the nonterminal's, and the
# token is in the tables' predict set of its first slot.
law nt_alternate:
  for isOwn: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +q: Nat
  for +next: Maybe<&2, Nat>
  for cp: Spec.ChoicePredicts(grammar, start, Spec.nonterminalAlternate(isOwn, grammar, q), next)
  {isOwn == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, q, [], 0n)) == True{} : Bool}

def nt_alternate(isOwn, grammar, start, t, po, q, next, cp):
  match isOwn:
    case True{}:
      ({==}, predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, cp))
    case False{}:
      Empty.absurd(({False{} == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, q, [], 0n)) == True{} : Bool}), cp)

law pick_head:
  for own: Bool
  for +c: Nat
  for +i0: Nat
  for +s: Gll.LSet
  for +rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for e: {own == True{} : Bool}
  for +same: {c == i0 : Nat}
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  HasAt(c, next, LL1.alternatePick(own, LL1.Predicted{i0, s}, rest))

def pick_head(own, c, i0, s, rest, next, e, same, hs):
  match own:
    case True{}:
      Inl{(same, hs)}
    case False{}:
      Empty.absurd(HasAt(c, next, rest), Lemma.false_is_not_true(e))

law pick_tail:
  for own: Bool
  for +c: Nat
  for +choice: LL1.Predicted
  for +rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for h: HasAt(c, next, rest)
  HasAt(c, next, LL1.alternatePick(own, choice, rest))

def pick_tail(own, c, choice, rest, next, h):
  match own choice:
    case True{} LL1.Predicted{c2, s2}:
      Inr{h}
    case False{} _:
      h

# The alternate numbered c (production q of the list, counted from i0) is in the list.
law alternate_in:
  for prods: +List<Spec.Production>
  for q: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x: Nat
  for +i0: Nat
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for +e: {c == Nat.add(q, i0) : Nat}
  for own: {Spec.lhsIs(prods, q, x) == True{} : Bool}
  for +hs: {Gll.lsHas(next, Gll.predictAt(grammar, t, c, [], 0n)) == True{} : Bool}
  HasAt(c, next, LL1.alternatesOf(prods, grammar, t, x, i0))

def alternate_in(prods, q, grammar, t, x, i0, c, next, e, own, hs):
  match prods q:
    case Nil{} _:
      Empty.absurd(HasAt(c, next, []), Lemma.false_is_not_true(own))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      pick_head(Nat.is_eq(lhs, x), c, i0, Gll.predictAt(grammar, t, i0, [], 0n), LL1.alternatesOf(rest, grammar, t, x, 1n+i0), next, own, e,
        Equal.trans(Bool, Gll.lsHas(next, Gll.predictAt(grammar, t, i0, [], 0n)), Gll.lsHas(next, Gll.predictAt(grammar, t, c, [], 0n)), True{},
          Equal.cong(Nat, Bool, v => Gll.lsHas(next, Gll.predictAt(grammar, t, v, [], 0n)), i0, c, Equal.sym(Nat, c, i0, e)), hs))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+p):
      pick_tail(Nat.is_eq(lhs, x), c, LL1.Predicted{i0, Gll.predictAt(grammar, t, i0, [], 0n)}, LL1.alternatesOf(rest, grammar, t, x, 1n+i0), next,
        alternate_in(rest, p, grammar, t, x, 1n+i0, c, next, Equal.trans(Nat, c, 1n+Nat.add(p, i0), Nat.add(p, 1n+i0), e, Equal.sym(Nat, Nat.add(p, 1n+i0), 1n+Nat.add(p, i0), Lemma.add_succ_right(p, i0))), own, hs))

# The nonterminals x0 .. x0+n-1 are all checked.
law nt_cover:
  for n: Nat
  for d: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x0: Nat
  for +x: Nat
  for +e: {x == Nat.add(d, x0) : Nat}
  for lt: {Nat.is_lt(d, n) == True{} : Bool}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n))) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.nonterminalConflicts(n, grammar, t, x0)) == False{} : Bool}

def nt_cover(n, d, grammar, t, x0, x, e, lt, ne):
  match n d:
    case 0n _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.nonterminalConflicts(0n, grammar, t, x0)) == False{} : Bool}, Lemma.lt_zero_false(d, lt))
    case 1n+m 0n:
      +here = LL1.conflictsAmong(Spec.NonterminalAt{x0}, LL1.alternatesOf(grammar, grammar, t, x0, 0n))
      nonempty_left(here, LL1.nonterminalConflicts(m, grammar, t, 1n+x0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n))), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{v}, LL1.alternatesOf(grammar, grammar, t, v, 0n))), x0, x, Equal.sym(Nat, x, x0, e)), ne))
    case 1n+(+m) 1n+(+d2):
      nonempty_right(LL1.conflictsAmong(Spec.NonterminalAt{x0}, LL1.alternatesOf(grammar, grammar, t, x0, 0n)), LL1.nonterminalConflicts(m, grammar, t, 1n+x0),
        nt_cover(m, d2, grammar, t, 1n+x0, x, Equal.trans(Nat, x, 1n+Nat.add(d2, x0), Nat.add(d2, 1n+x0), e, Equal.sym(Nat, Nat.add(d2, 1n+x0), 1n+Nat.add(d2, x0), Lemma.add_succ_right(d2, x0))), lt, ne))

law nonterminal_hits:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x: Nat
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for p1: {Spec.lhsIs(grammar, first, x) == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, first, [], 0n)) == True{} : Bool}
  for p2: {Spec.lhsIs(grammar, second, x) == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, second, [], 0n)) == True{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def nonterminal_hits(grammar, t, x, first, second, next, neq, p1, p2):
  match p1:
    case (own0, hs1):
      match p2:
        case (own2, hs2):
          +own1 = {own0 : {Spec.lhsIs(grammar, first, x) == True{} : Bool}}
          h1 = alternate_in(grammar, first, grammar, t, x, 0n, first, next, Equal.sym(Nat, Nat.add(first, 0n), first, Lemma.add_zero_right(first)), own1, hs1)
          h2 = alternate_in(grammar, second, grammar, t, x, 0n, second, next, Equal.sym(Nat, Nat.add(second, 0n), second, Lemma.add_zero_right(second)), own2, hs2)
          nonempty_left(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
            nt_cover(First.ntCount(grammar), x, grammar, t, 0n, x, Equal.sym(Nat, Nat.add(x, 0n), x, Lemma.add_zero_right(x)), lhs_below(grammar, first, x, own1),
              among_hit(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n), first, second, next, neq, h1, h2)))

# Two alternates of a nonterminal that predict the same token: the check reports it.
law nonterminal_point:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +x: Nat
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.NonterminalAt{x}, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.NonterminalAt{x}, second), next)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def nonterminal_point(grammar, start, t, po, x, first, second, next, neq, cp1, cp2):
  nonterminal_hits(grammar, t, x, first, second, next, neq,
    nt_alternate(Spec.lhsIs(grammar, first, x), grammar, start, t, po, first, next, cp1),
    nt_alternate(Spec.lhsIs(grammar, second, x), grammar, start, t, po, second, next, cp2))

# ---- Brackets: the choices ----

# The sequence named by a prefix, when it has an item at the dot, is the engine's sequence at
# the reversed path.
law seq_path:
  for p: +List<Nat>
  for +R0: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +dot: Nat
  for +x: Spec.Item
  for e: {Spec.itemAt(Spec.sequenceIn(p, Gll.seqAt(grammar, index, R0)), dot) == Some{x} : Maybe<&2, Spec.Item>}
  {Spec.sequenceIn(p, Gll.seqAt(grammar, index, R0)) == Gll.seqAt(grammar, index, Gll.reverseOnto(p, R0)) : +List<Spec.Item>}

def seq_path(p, R0, grammar, index, dot, x, e):
  match p:
    case Nil{}:
      {==}
    case Con{m, Nil{}}:
      Empty.absurd({Spec.sequenceIn([m], Gll.seqAt(grammar, index, R0)) == Gll.seqAt(grammar, index, Gll.reverseOnto([m], R0)) : +List<Spec.Item>},
        Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{x}, e)))
    case Con{+m, Con{+a, +rest}}:
      +S = Gll.seqAt(grammar, index, R0)
      +alt = Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.bracketAlt(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, a <> (m <> R0)),
        alternative_eq(Spec.itemAt(S, m), a), Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Spec.itemAt(S, m), Gll.nthItem(S, m), item_at_eq(S, m)))
      +inner = Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Spec.sequenceIn(rest, v), Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, a <> (m <> R0)), alt)
      +e2 = Equal.trans(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), dot), Spec.itemAt(Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), dot), Some{x},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Spec.itemAt(v, dot), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)),
          Equal.sym(+List<Spec.Item>, Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), inner)), e)
      Equal.trans(+List<Spec.Item>, Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, a <> (m <> R0))), Gll.seqAt(grammar, index, Gll.reverseOnto(rest, a <> (m <> R0))),
        inner, seq_path(rest, a <> (m <> R0), grammar, index, dot, x, e2))

# Alternate number c of a bracket, in the table's list of its alternates.
law alternates_in:
  for alts: +List<+List<Spec.Item>>
  for c2: Nat
  for +mayBeEmpty: Bool
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rpath: +List<Nat>
  for +a0: Nat
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for +e: {c == Nat.add(c2, a0) : Nat}
  for isA: {Nat.is_lt(c2, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +hs: {Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> rpath, Spec.altOf(alts, c2))) == True{} : Bool}
  HasAt(c, next, LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, rpath, a0))

def alternates_in(alts, c2, mayBeEmpty, grammar, t, index, rpath, a0, c, next, e, isA, hs):
  match alts c2:
    case Nil{} _:
      Empty.absurd(HasAt(c, next, []), Lemma.lt_zero_false(c2, isA))
    case Con{+alt, +rest} 0n:
      Inl{(e, Equal.trans(Bool, Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, a0 <> rpath, alt)), Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> rpath, alt)), True{},
        Equal.cong(Nat, Bool, v => Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, v <> rpath, alt)), a0, c, Equal.sym(Nat, c, a0, e)), hs))}
    case Con{+alt, +rest} 1n+(+d):
      Inr{alternates_in(rest, d, mayBeEmpty, grammar, t, index, rpath, 1n+a0, c, next, Equal.trans(Nat, c, 1n+Nat.add(d, a0), Nat.add(d, 1n+a0), e, Equal.sym(Nat, Nat.add(d, 1n+a0), 1n+Nat.add(d, a0), Lemma.add_succ_right(d, a0))), isA, hs)}

# An alternate that predicts the token: the token is in its table set.
law alt_set_has:
  for mayBeEmpty: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +c: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +next: Maybe<&2, Nat>
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for cp: Spec.predictsWhen(mayBeEmpty, grammar, start, Spec.altOf(alts, c), index, List.append(&2, Nat, p, [dot, c]), next)
  {Gll.lsHas(next, LL1.alternateSet(mayBeEmpty, grammar, t, index, c <> (dot <> R), Spec.altOf(alts, c))) == True{} : Bool}

def alt_set_has(mayBeEmpty, grammar, start, t, po, index, p, R, dot, c, kind, alts, next, rEq, itEq, cp):
  match mayBeEmpty:
    case True{}:
      +ctx = Gll.contextAfter(grammar, t, index, c <> (dot <> R))
      +rEq2 = Equal.trans(+List<Nat>, Gll.reverseOnto(R, [dot, c]), List.append(&2, Nat, Gll.reverseOnto(R, []), [dot, c]), List.append(&2, Nat, p, [dot, c]),
        G.rev_onto(R, [dot, c]), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [dot, c]), Gll.reverseOnto(R, []), p, rEq))
      Equal.trans(Bool, Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, R), dot), c), t), ctx)), Gll.lsHas(next, Gll.restOr(Gll.infoItems(Spec.altOf(alts, c), t), ctx)), True{},
        Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.bracketAlt(v, c), t), ctx)), Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Some{Spec.Brack{kind, alts}}, itEq),
        predicts_sound(grammar, start, t, po, Spec.altOf(alts, c), index, List.append(&2, Nat, p, [dot, c]), c <> (dot <> R), rEq2, next, cp))
    case False{}:
      first_of_sound(grammar, t, Lemma.and_true_left(First.prodsOk(grammar, grammar, t, 0n), Gll.lsHas(None{}, Gll.lsAt(Gll.folTab(t), start)), po), Spec.altOf(alts, c), next, cp)

law leave_pick_has:
  for leave: Bool
  for +c: Nat
  for +n: Nat
  for +s: Gll.LSet
  for +next: Maybe<&2, Nat>
  for e: {leave == True{} : Bool}
  for +same: {c == n : Nat}
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{n, s}))

def leave_pick_has(leave, c, n, s, next, e, same, hs):
  match leave:
    case True{}:
      Inl{(same, hs)}
    case False{}:
      Empty.absurd(HasAt(c, next, []), Lemma.false_is_not_true(e))

# Leaving the bracket, when it predicts the token: the token is in the table set for leaving.
law leave_has:
  for l: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +c: Nat
  for +alts: +List<+List<Spec.Item>>
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +next: Maybe<&2, Nat>
  for +lEq: {Bool.and(Nat.is_eq(c, List.length(&2, +List<Spec.Item>, alts)), leave) == l : Bool}
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +restEq: {rest == Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)) : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.leaveChoice(l, rest, index, p), next)
  HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)}))

def leave_has(l, grammar, start, t, po, c, alts, leave, rest, index, p, R, dot, next, lEq, rEq, restEq, cp):
  match l:
    case True{}:
      +n = List.length(&2, +List<Spec.Item>, alts)
      +ctx = Gll.contextAfter(grammar, t, index, R)
      +hs0 = predicts_sound(grammar, start, t, po, rest, index, p, R, rEq, next, cp)
      +hs = Equal.trans(Bool, Gll.lsHas(next, Gll.restOr(Gll.infoItems(Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), t), ctx)), Gll.lsHas(next, Gll.restOr(Gll.infoItems(rest, t), ctx)), True{},
        Equal.cong(+List<Spec.Item>, Bool, v => Gll.lsHas(next, Gll.restOr(Gll.infoItems(v, t), ctx)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), rest, Equal.sym(+List<Spec.Item>, rest, Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restEq)), hs0)
      leave_pick_has(leave, c, n, Gll.predictAt(grammar, t, index, R, 1n+dot), next, Lemma.and_true_right_side(Nat.is_eq(c, n), leave, lEq),
        Lemma.nat_eq_sound(c, n, Lemma.and_true_left(Nat.is_eq(c, n), leave, lEq)), hs)
    case False{}:
      Empty.absurd(HasAt(c, next, LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})), cp)

# A choice at a bracket that predicts the token: it is in the table's list of choices there.
law alt_choice:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +c: Nat
  for +index: Nat
  for +p: +List<Nat>
  for +R: +List<Nat>
  for +dot: Nat
  for +mayBeEmpty: Bool
  for +leave: Bool
  for +rest: +List<Spec.Item>
  for +next: Maybe<&2, Nat>
  for +bEq: {Spec.isAlt(alts, c) == b : Bool}
  for +rEq: {Gll.reverseOnto(R, []) == p : +List<Nat>}
  for +itEq: {Gll.nthItem(Gll.seqAt(grammar, index, R), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +restEq: {rest == Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)) : +List<Spec.Item>}
  for cp: Spec.ChoicePredicts(grammar, start, Spec.bracketAlternate(b, alts, c, index, p, dot, mayBeEmpty, leave, rest), next)
  HasAt(c, next, LL1.choicesWith(mayBeEmpty, leave, grammar, t, index, R, dot, alts))

def alt_choice(b, grammar, start, t, po, kind, alts, c, index, p, R, dot, mayBeEmpty, leave, rest, next, bEq, rEq, itEq, restEq, cp):
  match b:
    case True{}:
      +alternates = LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n)
      +leaving = LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})
      has_append_left(c, next, alternates, leaving,
        alternates_in(alts, c, mayBeEmpty, grammar, t, index, dot <> R, 0n, c, next, Equal.sym(Nat, Nat.add(c, 0n), c, Lemma.add_zero_right(c)), bEq,
          alt_set_has(mayBeEmpty, grammar, start, t, po, index, p, R, dot, c, kind, alts, next, rEq, itEq, cp)))
    case False{}:
      +alternates = LL1.bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> R, 0n)
      +leaving = LL1.leavePick(leave, LL1.Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, R, 1n+dot)})
      has_append_right(c, next, alternates, leaving,
        leave_has(Bool.and(Nat.is_eq(c, List.length(&2, +List<Spec.Item>, alts)), leave), grammar, start, t, po, c, alts, leave, rest, index, p, R, dot, next, {==}, rEq, restEq, cp))

# The checks the table check makes at one item: entering it and, for < >, after a round.
def localConflicts(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat) -> +List<LL1.Conflict>:
  match item:
    case Some{Spec.Brack{+kind, +inner}}:
      List.append(&2, LL1.Conflict, LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(rpath, []), dot}, LL1.enterChoices(kind, grammar, t, index, rpath, dot, inner)), LL1.afterRoundConflicts(kind, grammar, t, index, rpath, dot, inner))
    case Some{Spec.Sym{s}}:
      []
    case Some{Spec.Eps{}}:
      []
    case None{}:
      []

# Two choices entering a bracket that predict the same token: a conflict there.
law enter_local:
  for it: Maybe<&2, Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +p: +List<Nat>
  for +dot: Nat
  for +rest: +List<Spec.Item>
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for itS: {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == it : Maybe<&2, Spec.Item>}
  for +restS: {rest == Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)) : +List<Spec.Item>}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, False{}, first, index, p, dot, rest), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, False{}, second, index, p, dot, rest), next)
  {List.is_empty(&2, LL1.Conflict, localConflicts(it, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}

def enter_local(it, grammar, start, t, po, index, p, dot, rest, first, second, next, neq, itS, restS, cp1, cp2):
  match it:
    case None{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(None{}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Sym{sym}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Sym{sym}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Eps{}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Eps{}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Brack{Spec.Group{}, +alts}}:
      +R = Gll.reverseOnto(p, [])
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{Spec.Group{}, alts}} : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{Spec.Group{}, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Group{}, alts}},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), Spec.sequenceAt(grammar, index, p), Equal.sym(+List<Spec.Item>, Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Group{}, alts}}, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), item_at_eq(Spec.sequenceAt(grammar, index, p), dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, Spec.sequenceAt(grammar, index, p)),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, Spec.Group{}, alts, first, index, p, R, dot, True{}, False{}, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, Spec.Group{}, alts, second, index, p, R, dot, True{}, False{}, rest, next, {==}, rEq, itEq, restEq, cp2)
      nonempty_left(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Group{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Group{}, grammar, t, index, R, dot, alts), among_hit(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(True{}, False{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))
    case Some{Spec.Brack{Spec.Optional{}, +alts}}:
      +R = Gll.reverseOnto(p, [])
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{Spec.Optional{}, alts}} : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{Spec.Optional{}, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Optional{}, alts}},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), Spec.sequenceAt(grammar, index, p), Equal.sym(+List<Spec.Item>, Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Optional{}, alts}}, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), item_at_eq(Spec.sequenceAt(grammar, index, p), dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, Spec.sequenceAt(grammar, index, p)),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, Spec.Optional{}, alts, first, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, Spec.Optional{}, alts, second, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp2)
      nonempty_left(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Optional{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Optional{}, grammar, t, index, R, dot, alts), among_hit(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      +R = Gll.reverseOnto(p, [])
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{Spec.Closure{}, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Closure{}, alts}},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), Spec.sequenceAt(grammar, index, p), Equal.sym(+List<Spec.Item>, Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Closure{}, alts}}, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), item_at_eq(Spec.sequenceAt(grammar, index, p), dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, Spec.sequenceAt(grammar, index, p)),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, Spec.Closure{}, alts, first, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, Spec.Closure{}, alts, second, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp2)
      nonempty_left(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Closure{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Closure{}, grammar, t, index, R, dot, alts), among_hit(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      +R = Gll.reverseOnto(p, [])
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{Spec.Positive{}, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Positive{}, alts}},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), Spec.sequenceAt(grammar, index, p), Equal.sym(+List<Spec.Item>, Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Positive{}, alts}}, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), item_at_eq(Spec.sequenceAt(grammar, index, p), dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, Spec.sequenceAt(grammar, index, p)),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, Spec.Positive{}, alts, first, index, p, R, dot, True{}, False{}, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, Spec.Positive{}, alts, second, index, p, R, dot, True{}, False{}, rest, next, {==}, rEq, itEq, restEq, cp2)
      nonempty_left(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Positive{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Positive{}, grammar, t, index, R, dot, alts), among_hit(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(True{}, False{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))

# Two choices after a round of < > that predict the same token: a conflict there.
law after_local:
  for it: Maybe<&2, Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +p: +List<Nat>
  for +dot: Nat
  for +rest: +List<Spec.Item>
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for itS: {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == it : Maybe<&2, Spec.Item>}
  for +restS: {rest == Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)) : +List<Spec.Item>}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, True{}, first, index, p, dot, rest), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, True{}, second, index, p, dot, rest), next)
  {List.is_empty(&2, LL1.Conflict, localConflicts(it, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}

def after_local(it, grammar, start, t, po, index, p, dot, rest, first, second, next, neq, itS, restS, cp1, cp2):
  match it:
    case None{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(None{}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Sym{sym}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Sym{sym}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Eps{}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Eps{}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Brack{Spec.Group{}, +alts}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Brack{Spec.Group{}, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Brack{Spec.Optional{}, +alts}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Brack{Spec.Optional{}, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Brack{Spec.Closure{}, +alts}}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, localConflicts(Some{Spec.Brack{Spec.Closure{}, alts}}, grammar, t, index, Gll.reverseOnto(p, []), dot)) == False{} : Bool}, cp1)
    case Some{Spec.Brack{Spec.Positive{}, +alts}}:
      +R = Gll.reverseOnto(p, [])
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{Spec.Positive{}, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Positive{}, alts}},
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), Spec.sequenceAt(grammar, index, p), Equal.sym(+List<Spec.Item>, Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Some{Spec.Brack{Spec.Positive{}, alts}}, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, p), dot), Gll.nthItem(Spec.sequenceAt(grammar, index, p), dot), item_at_eq(Spec.sequenceAt(grammar, index, p), dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Spec.sequenceAt(grammar, index, p)), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, Spec.sequenceAt(grammar, index, p)),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), Spec.sequenceAt(grammar, index, p), Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, Spec.Positive{}, alts, first, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, Spec.Positive{}, alts, second, index, p, R, dot, False{}, True{}, rest, next, {==}, rEq, itEq, restEq, cp2)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(Spec.Positive{}, grammar, t, index, R, dot, alts)), LL1.afterRoundConflicts(Spec.Positive{}, grammar, t, index, R, dot, alts), among_hit(Spec.AfterRoundAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))

# ---- Brackets: the check visits every bracket ----

law nonempty_mid:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for +zs: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, List.append(&2, LL1.Conflict, ys, zs))) == False{} : Bool}

def nonempty_mid(xs, ys, zs, h):
  match xs:
    case Nil{}:
      nonempty_left(ys, zs, h)
    case Con{x, rest}:
      {==}

def altsOfItem(item: Maybe<&2, Spec.Item>) -> +List<+List<Spec.Item>>:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      alts
    case _:
      []

def isBrackItem(item: Maybe<&2, Spec.Item>) -> Bool:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      True{}
    case _:
      False{}

# The local checks at item j of a sequence are among the sequence's checks.
law local_reach:
  for items: +List<Spec.Item>
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +f: Nat
  for +d0: Nat
  for +D: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +eD: {D == Nat.add(j, d0) : Nat}
  for +ne: {List.is_empty(&2, LL1.Conflict, localConflicts(Gll.nthItem(items, j), grammar, t, index, R0, D)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, items, alts, grammar, t, index, R0, d0)) == False{} : Bool}

def local_reach(items, j, alts, f, d0, D, grammar, t, index, R0, eD, ne):
  match items j:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, [], alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Brack{+k, +inn}, +rest} 0n:
      +here = {Some{Spec.Brack{k, inn}} : Maybe<&2, Spec.Item>}
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, d0)), List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, D)), False{},
        Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, v)), d0, D, Equal.sym(Nat, D, d0, eD)), ne)
      nonempty_mid(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k, grammar, t, index, R0, d0, inn)), LL1.afterRoundConflicts(k, grammar, t, index, R0, d0, inn),
        List.append(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n), LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)), ne2)
    case Con{Spec.Sym{s}, rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Sym{s} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Eps{}, rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Brack{+k, +inn}, +rest} 1n+(+j2):
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)
      +afterC = LL1.afterRoundConflicts(k, grammar, t, index, R0, d0, inn)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k, grammar, t, index, R0, d0, inn)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_right(innerC, later,
          local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne))))
    case Con{Spec.Sym{+s}, +rest} 1n+(+j2):
      local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne)
    case Con{Spec.Eps{}, +rest} 1n+(+j2):
      local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne)

# The checks inside the bracket at item j of a sequence are among the sequence's checks.
law inner_reach:
  for items: +List<Spec.Item>
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +f: Nat
  for +d0: Nat
  for +D: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +k: Spec.Bracket
  for +inn: +List<+List<Spec.Item>>
  for +eD: {D == Nat.add(j, d0) : Nat}
  for +itEq: {Gll.nthItem(items, j) == Some{Spec.Brack{k, inn}} : Maybe<&2, Spec.Item>}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, D <> R0, 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, items, alts, grammar, t, index, R0, d0)) == False{} : Bool}

def inner_reach(items, j, alts, f, d0, D, grammar, t, index, R0, k, inn, eD, itEq, ne):
  match items j:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, [], alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Brack{+k2, +inn2}, +rest} 0n:
      +innEq = Equal.cong(Maybe<&2, Spec.Item>, +List<+List<Spec.Item>>, v => altsOfItem(v), Some{Spec.Brack{k2, inn2}}, Some{Spec.Brack{k, inn}}, itEq)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn2, grammar, t, index, d0 <> R0, 0n)
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, innerC), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)), False{},
        Equal.cong(+List<+List<Spec.Item>>, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], v, grammar, t, index, d0 <> R0, 0n)), inn2, inn, innEq),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, D <> R0, 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, v <> R0, 0n)), d0, D, Equal.sym(Nat, D, d0, eD)), ne))
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +afterC = LL1.afterRoundConflicts(k2, grammar, t, index, R0, d0, inn2)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k2, grammar, t, index, R0, d0, inn2)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_left(innerC, later, ne2)))
    case Con{Spec.Sym{+s}, +rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Sym{s} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackItem(v), Some{Spec.Sym{s}}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Eps{}, +rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackItem(v), Some{Spec.Eps{}}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Brack{+k2, +inn2}, +rest} 1n+(+j2):
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn2, grammar, t, index, d0 <> R0, 0n)
      +afterC = LL1.afterRoundConflicts(k2, grammar, t, index, R0, d0, inn2)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k2, grammar, t, index, R0, d0, inn2)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_right(innerC, later,
          inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne))))
    case Con{Spec.Sym{+s}, +rest} 1n+(+j2):
      inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne)
    case Con{Spec.Eps{}, +rest} 1n+(+j2):
      inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne)

# The checks in alternative c of a bracket are among the bracket's checks.
law alt_reach:
  for alts: +List<+List<Spec.Item>>
  for c: Nat
  for +f: Nat
  for +a0: Nat
  for +A: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +eA: {A == Nat.add(c, a0) : Nat}
  for isA: {Nat.is_lt(c, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, Spec.altOf(alts, c), [], grammar, t, index, A <> R0, 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, alts, grammar, t, index, R0, a0)) == False{} : Bool}

def alt_reach(alts, c, f, a0, A, items, grammar, t, index, R0, eA, isA, ne):
  match alts c:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, [], grammar, t, index, R0, a0)) == False{} : Bool}, Lemma.lt_zero_false(c, isA))
    case Con{+alt, +rest} 0n:
      +here = LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, a0 <> R0, 0n)
      nonempty_left(here, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, R0, 1n+a0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, A <> R0, 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, v <> R0, 0n)), a0, A, Equal.sym(Nat, A, a0, eA)), ne))
    case Con{+alt, +rest} 1n+(+c2):
      nonempty_right(LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, a0 <> R0, 0n), LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, R0, 1n+a0),
        alt_reach(rest, c2, f, 1n+a0, A, items, grammar, t, index, R0, Equal.trans(Nat, A, 1n+Nat.add(c2, a0), Nat.add(c2, 1n+a0), eA, Equal.sym(Nat, Nat.add(c2, 1n+a0), 1n+Nat.add(c2, a0), Lemma.add_succ_right(c2, a0))), isA, ne))

law seq_in_nil:
  for p: +List<Nat>
  {Spec.sequenceIn(p, []) == [] : +List<Spec.Item>}

def seq_in_nil(p):
  match p:
    case Nil{}:
      {==}
    case Con{m, Nil{}}:
      {==}
    case Con{m, Con{a, rest}}:
      seq_in_nil(rest)

law alt_out:
  for alts: +List<+List<Spec.Item>>
  for a: Nat
  for e: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == False{} : Bool}
  {Spec.altOf(alts, a) == [] : +List<Spec.Item>}

def alt_out(alts, a, e):
  match alts a:
    case Nil{} _:
      {==}
    case Con{alt, rest} 0n:
      Empty.absurd({alt == [] : +List<Spec.Item>}, Lemma.true_is_not_false(e))
    case Con{alt, rest} 1n+b:
      alt_out(rest, b, e)

def LocalAt(+rest: +List<Nat>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +R1: +List<Nat>, +dot: Nat) -> Data:
  {List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)) == False{} : Bool}

def LocateIH(+rest: +List<Nat>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +R1: +List<Nat>, +dot: Nat) -> Type:
  @fuel: Nat -> LocalAt(rest, grammar, t, index, R1, dot) -> {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(fuel, Gll.MItems{}, Gll.seqAt(grammar, index, R1), [], grammar, t, index, R1, 0n)) == False{} : Bool}

# A sequence named by no bracket's alternative has no checks to find.
law nowhere:
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R1: +List<Nat>
  for +dot: Nat
  for +goal: Bool
  for +nil: {Gll.seqAt(grammar, index, R1) == [] : +List<Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, R1, dot)
  {goal == False{} : Bool}

def nowhere(rest, grammar, t, index, R1, dot, goal, nil, ne):
  +nilIn = Equal.trans(+List<Spec.Item>, Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), Spec.sequenceIn(rest, []), [],
    Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Spec.sequenceIn(rest, v), Gll.seqAt(grammar, index, R1), [], nil), seq_in_nil(rest))
  Empty.absurd({goal == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), False{},
    Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), True{},
      Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(v, dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), [], nilIn)), ne)))

# One level down: the bracket at item m, alternative a, when a is an alternative of it.
law locate_alt:
  for b: Bool
  for f: Nat
  for +m: Nat
  for +a: Nat
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +k2: Spec.Bracket
  for +inn2: +List<+List<Spec.Item>>
  for +bEq: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, inn2)) == b : Bool}
  for +it2Eq: {Gll.nthItem(Gll.seqAt(grammar, index, R0), m) == Some{Spec.Brack{k2, inn2}} : Maybe<&2, Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, a <> (m <> R0), dot)
  for ih: LocateIH(rest, grammar, t, index, a <> (m <> R0), dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate_alt(b, f, m, a, rest, grammar, t, index, R0, dot, k2, inn2, bEq, it2Eq, ne, ih):
  match b f:
    case False{} _:
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, S, [], grammar, t, index, R0, 0n)),
        Equal.trans(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(S, m), a), Spec.altOf(inn2, a), [], altEq, alt_out(inn2, a, bEq)), ne)
    case True{} 0n:
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      inner_reach(S, m, [], 0n, 0n, m, grammar, t, index, R0, k2, inn2, Equal.sym(Nat, Nat.add(m, 0n), m, Lemma.add_zero_right(m)), it2Eq, {==})
    case True{} 1n+(+f2):
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      +got = ih(f2, ne)
      +got2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, Spec.altOf(inn2, a), [], grammar, t, index, a <> (m <> R0), 0n)), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, Gll.bracketAlt(Gll.nthItem(S, m), a), [], grammar, t, index, a <> (m <> R0), 0n)), False{},
        Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, v, [], grammar, t, index, a <> (m <> R0), 0n)), Spec.altOf(inn2, a), Gll.bracketAlt(Gll.nthItem(S, m), a), Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(S, m), a), Spec.altOf(inn2, a), altEq)), got)
      inner_reach(S, m, [], 1n+f2, 0n, m, grammar, t, index, R0, k2, inn2, Equal.sym(Nat, Nat.add(m, 0n), m, Lemma.add_zero_right(m)), it2Eq,
        alt_reach(inn2, a, f2, 0n, a, [], grammar, t, index, m <> R0, Equal.sym(Nat, Nat.add(a, 0n), a, Lemma.add_zero_right(a)), bEq, got2))

# One level down: what item m of the sequence is.
law locate_step:
  for it2: Maybe<&2, Spec.Item>
  for f: Nat
  for +m: Nat
  for +a: Nat
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +it2Eq: {Gll.nthItem(Gll.seqAt(grammar, index, R0), m) == it2 : Maybe<&2, Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, a <> (m <> R0), dot)
  for ih: LocateIH(rest, grammar, t, index, a <> (m <> R0), dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate_step(it2, f, m, a, rest, grammar, t, index, R0, dot, it2Eq, ne, ih):
  match it2:
    case Some{Spec.Brack{+k2, +inn2}}:
      locate_alt(Nat.is_lt(a, List.length(&2, +List<Spec.Item>, inn2)), f, m, a, rest, grammar, t, index, R0, dot, k2, inn2, {==}, it2Eq, ne, ih)
    case Some{Spec.Sym{+s}}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), Some{Spec.Sym{s}}, it2Eq), ne)
    case Some{Spec.Eps{}}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), Some{Spec.Eps{}}, it2Eq), ne)
    case None{}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), None{}, it2Eq), ne)

# The check visits the bracket named by the prefix, or runs out of nesting fuel on the way
# (which it reports as a conflict too).
law locate:
  for prem: +List<Nat>
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +ne: LocalAt(prem, grammar, t, index, R0, dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(fuel, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate(prem, fuel, grammar, t, index, R0, dot, ne):
  match prem fuel:
    case _ 0n:
      {==}
    case Nil{} 1n+(+f):
      +S = Gll.seqAt(grammar, index, R0)
      local_reach(S, dot, [], f, 0n, dot, grammar, t, index, R0, Equal.sym(Nat, Nat.add(dot, 0n), dot, Lemma.add_zero_right(dot)),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Gll.nthItem(S, dot), grammar, t, index, R0, dot)), List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(S, dot), grammar, t, index, R0, dot)), False{},
          Equal.cong(Maybe<&2, Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(v, grammar, t, index, R0, dot)), Gll.nthItem(S, dot), Spec.itemAt(S, dot), Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(S, dot), Gll.nthItem(S, dot), item_at_eq(S, dot))), ne))
    case Con{m, Nil{}} 1n+(+f):
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{+m, Con{+a, +rest}} 1n+(+f):
      +S = Gll.seqAt(grammar, index, R0)
      +R1 = {a <> (m <> R0) : +List<Nat>}
      +alt = Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.bracketAlt(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, R1),
        alternative_eq(Spec.itemAt(S, m), a), Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Spec.itemAt(S, m), Gll.nthItem(S, m), item_at_eq(S, m)))
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)),
        List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), False{},
        Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, v), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), Gll.seqAt(grammar, index, R1), Spec.bracketAlternative(Spec.itemAt(S, m), a),
          Equal.sym(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, R1), alt)), ne)
      locate_step(Gll.nthItem(S, m), f, m, a, rest, grammar, t, index, R0, dot, {==}, ne2, (fx => nx => locate(rest, fx, grammar, t, index, a <> (m <> R0), dot, nx)))

# Every production is checked.
law prod_reach:
  for prods: +List<Spec.Production>
  for q: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +i0: Nat
  for +n: Nat
  for +e: {n == Nat.add(q, i0) : Nat}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, Spec.rhsOf(prods, q), [], grammar, t, n, [], 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.productionConflicts(prods, grammar, t, i0)) == False{} : Bool}

def prod_reach(prods, q, grammar, t, i0, n, e, ne):
  match prods q:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.productionConflicts([], grammar, t, i0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      +here = LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, i0, [], 0n)
      nonempty_left(here, LL1.productionConflicts(rest, grammar, t, 1n+i0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, n, [], 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, v, [], 0n)), i0, n, Equal.sym(Nat, n, i0, e)), ne))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+q2):
      nonempty_right(LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, i0, [], 0n), LL1.productionConflicts(rest, grammar, t, 1n+i0),
        prod_reach(rest, q2, grammar, t, 1n+i0, n, Equal.trans(Nat, n, 1n+Nat.add(q2, i0), Nat.add(q2, 1n+i0), e, Equal.sym(Nat, Nat.add(q2, 1n+i0), 1n+Nat.add(q2, i0), Lemma.add_succ_right(q2, i0))), ne))

# ======== THE THEOREM ========

law ll1_point:
  for point: Spec.ChoicePoint
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2):
  match point:
    case Spec.NonterminalAt{+x}:
      nonterminal_point(grammar, start, t, po, x, first, second, next, neq, cp1, cp2)
    case Spec.BracketAt{+index, +p, +dot}:
      +seq = Spec.sequenceAt(grammar, index, p)
      +local = enter_local(Spec.itemAt(seq, dot), grammar, start, t, po, index, p, dot, Spec.itemsFrom(1n+dot, seq), first, second, next, neq, {==}, {==}, cp1, cp2)
      nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
        prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), locate(p, Gll.nestFuel(), grammar, t, index, [], dot, local)))
    case Spec.AfterRoundAt{+index, +p, +dot}:
      +seq = Spec.sequenceAt(grammar, index, p)
      +local = after_local(Spec.itemAt(seq, dot), grammar, start, t, po, index, p, dot, Spec.itemsFrom(1n+dot, seq), first, second, next, neq, {==}, {==}, cp1, cp2)
      nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
        prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), locate(p, Gll.nestFuel(), grammar, t, index, [], dot, local)))

# LL(1) BY THE TABLES IS LL(1).
law tables_ll1_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ok: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  Spec.LL1(grammar, start)

def tables_ll1_sound(grammar, start, t, ok):
  +closed = First.tablesClosed(grammar, start, t)
  +none = List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t))
  +po = Lemma.and_true_left(closed, none, ok)
  +noConflict = Lemma.and_true_right_side(closed, none, ok)
  point => first => second => next => neq => cp1 => cp2 =>
    Lemma.false_is_not_true(Equal.trans(Bool, False{}, none, True{}, Equal.sym(Bool, none, False{}, ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2)), noConflict))

# The law tables_ll1_sound.
def Laws.tables_ll1_sound(grammar, start, t, ok):
  tables_ll1_sound(grammar, start, t, ok)
