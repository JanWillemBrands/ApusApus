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
