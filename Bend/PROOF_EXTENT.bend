import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./EXTENT.bend as Ext
import ./UNBEATEN.bend as Unb
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_SUBPARSE.bend as Sub
import ./PROOF_GUARD.bend as PG
import ./PROOF_SUPPORT.bend as Sup
import ./PROOF_PREFER.bend as PP
import ./PROOF_PLUG.bend as Plug
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# @longest AND @shortest KEEP EXACTLY THE EXTENT-BEST TREES: extent_exact.
#
# The oracle's answers come from one search over the boundaries of a sequence's
# children. A forest that reads the items within a constraint makes the search answer
# something other than No; a Yes comes with such a forest. Both directions of the law
# rest on these two facts, and on the oracle's check that every chain of kept steps reads
# the marked item with the best length.

# ======== THE SEARCH ========

def headLen(f: +List<Spec.Tree>) -> Nat:
  match f:
    case Nil{}:
      0n
    case Con{+t, ts}:
      List.length(&2, Nat, Spec.leaves([t]))

law bool_cases:
  for x: Bool
  Either<{x == True{} : Bool}, {x == False{} : Bool}>

def bool_cases(x):
  match x:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{{==}}

law nat_eq_cases:
  for a: Nat
  for b: Nat
  Either<{Nat.is_eq(a, b) == True{} : Bool}, {Nat.is_eq(a, b) == False{} : Bool}>

def nat_eq_cases(a, b):
  bool_cases(Nat.is_eq(a, b))

law eq_pick:
  for +a: Nat
  for +b: Nat
  for cases: Either<{Nat.is_eq(a, b) == True{} : Bool}, {Nat.is_eq(a, b) == False{} : Bool}>
  for yes: {Nat.is_eq(a, b) == True{} : Bool} -> Empty
  for no: {Nat.is_eq(a, b) == False{} : Bool} -> Empty
  Empty

def eq_pick(a, b, cases, yes, no):
  match cases:
    case Inl{e1}:
      yes(e1)
    case Inr{e2}:
      no(e2)

law head_le:
  for ts: +List<Spec.Tree>
  {Nat.is_le(headLen(ts), List.length(&2, Nat, Spec.leaves(ts))) == True{} : Bool}

def head_le(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{+u, +us}:
      +lu = Spec.leaves([u])
      +lus = Spec.leaves(us)
      +l1 = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(u <> us), List.append(&2, Nat, lu, lus), Sub.leaves_cons(u, us))
      +l2 = Lemma.length_append(lu, lus)
      +sumEq = Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(u <> us)), List.length(&2, Nat, List.append(&2, Nat, lu, lus)), Nat.add(List.length(&2, Nat, lu), List.length(&2, Nat, lus)), l1, l2)
      Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, lu), List.length(&2, Nat, Spec.leaves(u <> us))), Nat.is_le(List.length(&2, Nat, lu), Nat.add(List.length(&2, Nat, lu), List.length(&2, Nat, lus))), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(List.length(&2, Nat, lu), v), List.length(&2, Nat, Spec.leaves(u <> us)), Nat.add(List.length(&2, Nat, lu), List.length(&2, Nat, lus)), sumEq), Lemma.le_add_right(List.length(&2, Nat, lu), List.length(&2, Nat, lus)))

# Where the rest of a forest starts and ends, with the first tree's length m.
law len_cons:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {List.length(&2, Nat, Spec.leaves(t <> ts)) == Nat.add(List.length(&2, Nat, Spec.leaves([t])), List.length(&2, Nat, Spec.leaves(ts))) : Nat}

def len_cons(t, ts):
  Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), List.length(&2, Nat, List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts))), Nat.add(List.length(&2, Nat, Spec.leaves([t])), List.length(&2, Nat, Spec.leaves(ts))), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Sub.leaves_cons(t, ts)), Lemma.length_append(Spec.leaves([t]), Spec.leaves(ts)))

law end_b:
  for +from: Nat
  for +m: Nat
  for +lt: Nat
  for +lts: Nat
  for +e: Nat
  for +mEq: {m == lt : Nat}
  for +endEq: {Nat.add(from, Nat.add(lt, lts)) == e : Nat}
  {Nat.add(Nat.add(from, m), lts) == e : Nat}

def end_b(from, m, lt, lts, e, mEq, endEq):
  +a1 = Equal.cong(Nat, Nat, v => Nat.add(Nat.add(from, v), lts), m, lt, mEq)
  Equal.trans(Nat, Nat.add(Nat.add(from, m), lts), Nat.add(Nat.add(from, lt), lts), e, a1, Equal.trans(Nat, Nat.add(Nat.add(from, lt), lts), Nat.add(from, Nat.add(lt, lts)), e, Lemma.add_assoc(from, lt, lts), endEq))

# The set has the item's step: seg is not No.
law seg_not_no:
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +q: Nat
  for +from: Nat
  for +m: Nat
  for +mem: {Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, m)), set) == True{} : Bool}
  for +no: {Ext.seg(set, index, prefix, i, q, from, Nat.add(from, m)) == Guard.No{} : Guard.Tri}
  Empty

def seg_not_no(set, index, prefix, i, q, from, m, mem, no):
  +b = Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, m)), set)
  PG.tri_ne_yes_no(Equal.trans(Guard.Tri, Guard.Yes{}, Ext.triIf(b), Guard.No{}, Equal.cong(Bool, Guard.Tri, v => Ext.triIf(v), True{}, b, Equal.sym(Bool, b, True{}, mem)), no))

law here_not_no:
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +from: Nat
  for +m: Nat
  for +q: Nat
  for +d: Nat
  for +len: Nat
  for +hasStep: Bool
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +okB: {Ext.okAt(q, from, Nat.add(from, m), d, len, hasStep, p, k, j) == True{} : Bool}
  for +rest: Guard.Tri
  for +mem: {Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, m)), set) == True{} : Bool}
  for no: {Guard.andTri(Ext.triIf(Ext.okAt(q, from, Nat.add(from, m), d, len, hasStep, p, k, j)), Guard.andTri(Ext.seg(set, index, prefix, i, q, from, Nat.add(from, m)), rest)) == Guard.No{} : Guard.Tri}
  for restNo: {rest == Guard.No{} : Guard.Tri} -> Empty
  Empty

def here_not_no(set, index, prefix, i, from, m, q, d, len, hasStep, p, k, j, okB, rest, mem, no, restNo):
  +b = Nat.add(from, m)
  +ok = Ext.okAt(q, from, b, d, len, hasStep, p, k, j)
  +sg = Ext.seg(set, index, prefix, i, q, from, b)
  PG.guards_no_pick(Ext.triIf(ok), Guard.andTri(sg, rest), PG.and_no(Ext.triIf(ok), Guard.andTri(sg, rest), no),
    e1 => PG.tri_ne_yes_no(Equal.trans(Guard.Tri, Guard.Yes{}, Ext.triIf(ok), Guard.No{}, Equal.cong(Bool, Guard.Tri, v => Ext.triIf(v), True{}, ok, Equal.sym(Bool, ok, True{}, okB)), e1)),
    e2 => PG.guards_no_pick(sg, rest, PG.and_no(sg, rest, e2),
      e3 => seg_not_no(set, index, prefix, i, q, from, m, mem, e3),
      e4 => restNo(e4)))

law search_here:
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +rest: +List<Spec.Item>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +from: Nat
  for +m: Nat
  for +lt: Nat
  for +lts: Nat
  for +e: Nat
  for +q: Nat
  for +d: Nat
  for +len: Nat
  for +hasStep: Bool
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +g: Nat
  for +mEq: {m == lt : Nat}
  for +okL: {Ext.okAt(q, from, Nat.add(from, lt), d, len, hasStep, p, k, j) == True{} : Bool}
  for +memL: {Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, lt)), set) == True{} : Bool}
  for +ownL: {Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, Nat.add(from, lt)), set) == True{} : Bool}
  for +ltsEq: {lts == List.length(&2, Nat, Spec.leaves(ts)) : Nat}
  for +endL: {Nat.add(from, Nat.add(lt, lts)) == e : Nat}
  for +consL: {Ext.consOk(ts, 1n+q, Nat.add(from, lt), d, len, hasStep, p, k, j) == True{} : Bool}
  for no: {Guard.andTri(Ext.triIf(Ext.okAt(q, from, Nat.add(from, m), d, len, hasStep, p, k, j)), Guard.andTri(Ext.seg(set, index, prefix, i, q, from, Nat.add(from, m)), Ext.search(g, rest, 1n+Nat.sub(e, Nat.add(from, m)), set, index, prefix, i, 1n+q, Nat.add(from, m), e, d, len, hasStep, p, k, j))) == Guard.No{} : Guard.Tri}
  for later: {Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, Nat.add(from, m)), set) == True{} : Bool} -> {Nat.add(Nat.add(from, m), List.length(&2, Nat, Spec.leaves(ts))) == e : Nat} -> {Ext.consOk(ts, 1n+q, Nat.add(from, m), d, len, hasStep, p, k, j) == True{} : Bool} -> {Nat.is_lt(headLen(ts), 1n+Nat.sub(e, Nat.add(from, m))) == True{} : Bool} -> {Ext.search(g, rest, 1n+Nat.sub(e, Nat.add(from, m)), set, index, prefix, i, 1n+q, Nat.add(from, m), e, d, len, hasStep, p, k, j) == Guard.No{} : Guard.Tri} -> Empty
  Empty

def search_here(set, index, prefix, i, rest, t, ts, from, m, lt, lts, e, q, d, len, hasStep, p, k, j, g, mEq, okL, memL, ownL, ltsEq, endL, consL, no, later):
  +b = Nat.add(from, m)
  +ltm = Equal.sym(Nat, m, lt, mEq)
  +okB = Equal.trans(Bool, Ext.okAt(q, from, b, d, len, hasStep, p, k, j), Ext.okAt(q, from, Nat.add(from, lt), d, len, hasStep, p, k, j), True{}, Equal.cong(Nat, Bool, v => Ext.okAt(q, from, Nat.add(from, v), d, len, hasStep, p, k, j), m, lt, mEq), okL)
  +memB = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, b), set), Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, lt)), set), True{}, Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, v)), set), m, lt, mEq), memL)
  +ownB = Equal.trans(Bool, Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, b), set), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, Nat.add(from, lt)), set), True{}, Equal.cong(Nat, Bool, v => Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, Nat.add(from, v)), set), m, lt, mEq), ownL)
  +endB0 = end_b(from, m, lt, lts, e, mEq, endL)
  +endB = Equal.trans(Nat, Nat.add(b, List.length(&2, Nat, Spec.leaves(ts))), Nat.add(b, lts), e, Equal.cong(Nat, Nat, v => Nat.add(b, v), List.length(&2, Nat, Spec.leaves(ts)), lts, Equal.sym(Nat, lts, List.length(&2, Nat, Spec.leaves(ts)), ltsEq)), endB0)
  +consB = Equal.trans(Bool, Ext.consOk(ts, 1n+q, b, d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, Nat.add(from, lt), d, len, hasStep, p, k, j), True{}, Equal.cong(Nat, Bool, v => Ext.consOk(ts, 1n+q, Nat.add(from, v), d, len, hasStep, p, k, j), m, lt, mEq), consL)
  +lt2 = List.length(&2, Nat, Spec.leaves(ts))
  +subEq = Equal.trans(Nat, Nat.sub(e, b), Nat.sub(Nat.add(b, lt2), b), lt2, Equal.cong(Nat, Nat, v => Nat.sub(v, b), e, Nat.add(b, lt2), Equal.sym(Nat, Nat.add(b, lt2), e, endB)), Lemma.sub_add_left(b, lt2))
  +roomB = Equal.trans(Bool, Nat.is_lt(headLen(ts), 1n+Nat.sub(e, b)), Nat.is_lt(headLen(ts), 1n+lt2), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(headLen(ts), 1n+v), Nat.sub(e, b), lt2, subEq), Lemma.lt_of_succ_le(headLen(ts), 1n+lt2, head_le(ts)))
  here_not_no(set, index, prefix, i, from, m, q, d, len, hasStep, p, k, j, okB, Ext.search(g, rest, 1n+Nat.sub(e, b), set, index, prefix, i, 1n+q, b, e, d, len, hasStep, p, k, j), memB, no,
    rN => later(ownB, endB, consB, roomB, rN))

# A forest that reads the items within the constraint, from `from` to e, whose own steps
# (the sequence's steps, item by item) are in the set: the search never answers No.
law search_not_no:
  for gas: Nat
  for +items: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +count: Nat
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +from: Nat
  for +e: Nat
  for +d: Nat
  for +len: Nat
  for +hasStep: Bool
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +fit: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +own: {Spec.allIn(PG.ownSteps(f, index, prefix, q, i, from), set) == True{} : Bool}
  for +endEq: {Nat.add(from, List.length(&2, Nat, Spec.leaves(f))) == e : Nat}
  for +cons: {Ext.consOk(f, q, from, d, len, hasStep, p, k, j) == True{} : Bool}
  for +room: {Nat.is_lt(headLen(f), count) == True{} : Bool}
  for +no: {Ext.search(gas, items, count, set, index, prefix, i, q, from, e, d, len, hasStep, p, k, j) == Guard.No{} : Guard.Tri}
  Empty

def search_not_no(gas, items, f, count, set, index, prefix, i, grammar, q, from, e, d, len, hasStep, p, k, j, fit, own, endEq, cons, room, no):
  match gas:
    case 0n:
      PG.tri_ne_unknown_no(no)
    case 1n+(+g):
      match items:
        case Nil{}:
          match f:
            case Nil{}:
              +fromEq = Equal.trans(Nat, from, Nat.add(from, 0n), e, Equal.sym(Nat, Nat.add(from, 0n), from, Lemma.add_zero_right(from)), endEq)
              +isE = Lemma.nat_eq_of_eq(from, e, fromEq)
              PG.tri_ne_yes_no(Equal.trans(Guard.Tri, Guard.Yes{}, Ext.triIf(Nat.is_eq(from, e)), Guard.No{}, Equal.cong(Bool, Guard.Tri, v => Ext.triIf(v), True{}, Nat.is_eq(from, e), Equal.sym(Bool, Nat.is_eq(from, e), True{}, isE)), no))
            case Con{+t, +ts}:
              Fits.fits_cons_nil(t, ts, grammar, fit)
        case Con{+it, +rest}:
          match f:
            case Nil{}:
              Lemma.false_is_not_true(fit)
            case Con{+t, +ts}:
              match count:
                case 0n:
                  Lemma.lt_zero_false(headLen(t <> ts), room)
                case 1n+(+m):
                  +lt = List.length(&2, Nat, Spec.leaves([t]))
                  +lts = List.length(&2, Nat, Spec.leaves(ts))
                  +b = Nat.add(from, m)
                  +rc = Ext.search(g, rest, 1n+Nat.sub(e, b), set, index, prefix, i, 1n+q, b, e, d, len, hasStep, p, k, j)
                  +here = Guard.andTri(Ext.triIf(Ext.okAt(q, from, b, d, len, hasStep, p, k, j)), Guard.andTri(Ext.seg(set, index, prefix, i, q, from, b), rc))
                  +loop = Ext.search(g, it <> rest, m, set, index, prefix, i, q, from, e, d, len, hasStep, p, k, j)
                  +noHere = PG.or_no_l(here, loop, no)
                  +noLoop = PG.or_no_r(here, loop, no)
                  +fitTs = Fits.fits_tail(t, ts, grammar, it, rest, fit)
                  +okL = Lemma.and_true_left(Ext.okAt(q, from, Nat.add(from, lt), d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, Nat.add(from, lt), d, len, hasStep, p, k, j), cons)
                  +consL = Lemma.and_true_right_side(Ext.okAt(q, from, Nat.add(from, lt), d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, Nat.add(from, lt), d, len, hasStep, p, k, j), cons)
                  +endT = Sub.end_of_one(t, from)
                  +sT = Spec.at(index, prefix, 1n+q, i, from, Sub.endOf(t, from))
                  +oTs = PG.ownSteps(ts, index, prefix, 1n+q, i, Sub.endOf(t, from))
                  +memE = Lemma.and_true_left(Spec.bsrMember(sT, set), Spec.allIn(oTs, set), own)
                  +ownE = Lemma.and_true_right_side(Spec.bsrMember(sT, set), Spec.allIn(oTs, set), own)
                  +memL = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, Nat.add(from, lt)), set), Spec.bsrMember(sT, set), True{}, Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+q, i, from, v), set), Nat.add(from, lt), Sub.endOf(t, from), Equal.sym(Nat, Sub.endOf(t, from), Nat.add(from, lt), endT)), memE)
                  +ownL = Equal.trans(Bool, Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, Nat.add(from, lt)), set), Spec.allIn(oTs, set), True{}, Equal.cong(Nat, Bool, v => Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+q, i, v), set), Nat.add(from, lt), Sub.endOf(t, from), Equal.sym(Nat, Sub.endOf(t, from), Nat.add(from, lt), endT)), ownE)
                  +endL = Equal.trans(Nat, Nat.add(from, Nat.add(lt, lts)), Nat.add(from, List.length(&2, Nat, Spec.leaves(t <> ts))), e, Equal.cong(Nat, Nat, v => Nat.add(from, v), Nat.add(lt, lts), List.length(&2, Nat, Spec.leaves(t <> ts)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(t <> ts)), Nat.add(lt, lts), len_cons(t, ts))), endEq)
                  eq_pick(m, lt, nat_eq_cases(m, lt),
                    eT => search_here(set, index, prefix, i, rest, t, ts, from, m, lt, lts, e, q, d, len, hasStep, p, k, j, g, Lemma.nat_eq_sound(m, lt, eT), okL, memL, ownL, {==}, endL, consL, noHere,
                      (ownB => endB => consB => roomB => rN => search_not_no(g, rest, ts, 1n+Nat.sub(e, b), set, index, prefix, i, grammar, 1n+q, b, e, d, len, hasStep, p, k, j, fitTs, ownB, endB, consB, roomB, rN))),
                    eF => search_not_no(g, it <> rest, t <> ts, m, set, index, prefix, i, grammar, q, from, e, d, len, hasStep, p, k, j, fit, own, endEq, cons, Lemma.lt_succ_ne(lt, m, room, eF), noLoop))

# ======== A CERTIFICATE IS A READING ========

# A forest for the items over (from, e) within the constraint, all of whose steps are in
# the set.
def Reading(+grammar: +List<Spec.Production>, +items: +List<Spec.Item>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +index: Nat, +prefix: +List<Nat>, +from: Nat, +e: Nat, +d: Nat, +len: Nat) -> Type:
  &f: +List<Spec.Tree> -> {Spec.fits(f, grammar, items) == True{} : Bool} & {Spec.leaves(f) == Prefer.tokensFrom(input, from, e) : +List<Nat>} & {Ext.consOk(f, 0n, from, d, len, False{}, 0n, 0n, 0n) == True{} : Bool} & {Spec.allIn(Spec.walk(f, False{}, index, prefix, 0n, from, from), set) == True{} : Bool}

law cert_one:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +its: +List<Spec.Item>
  for +d: Nat
  for +i: Nat
  for +len: Nat
  for +e: Nat
  for +f: +List<Spec.Tree>
  for +ok: {Ext.certOk(grammar, input, set, index, prefix, its, d, i, len, e, f) == True{} : Bool}
  Reading(grammar, its, input, set, index, prefix, i, e, d, len)

def cert_one(grammar, input, set, index, prefix, its, d, i, len, e, f, ok):
  +a = Bool.and(Spec.fits(f, grammar, its), Gll.natsEq(Spec.leaves(f), Prefer.tokensFrom(input, i, e)))
  +b = Bool.and(Ext.consOk(f, 0n, i, d, len, False{}, 0n, 0n, 0n), Spec.allIn(Spec.walk(f, False{}, index, prefix, 0n, i, i), set))
  +okA = Lemma.and_true_left(a, b, ok)
  +okB = Lemma.and_true_right_side(a, b, ok)
  +fit = Lemma.and_true_left(Spec.fits(f, grammar, its), Gll.natsEq(Spec.leaves(f), Prefer.tokensFrom(input, i, e)), okA)
  +lv = G.nats_eq_sound(Spec.leaves(f), Prefer.tokensFrom(input, i, e), Lemma.and_true_right_side(Spec.fits(f, grammar, its), Gll.natsEq(Spec.leaves(f), Prefer.tokensFrom(input, i, e)), okA))
  +cons = Lemma.and_true_left(Ext.consOk(f, 0n, i, d, len, False{}, 0n, 0n, 0n), Spec.allIn(Spec.walk(f, False{}, index, prefix, 0n, i, i), set), okB)
  +all = Lemma.and_true_right_side(Ext.consOk(f, 0n, i, d, len, False{}, 0n, 0n, 0n), Spec.allIn(Spec.walk(f, False{}, index, prefix, 0n, i, i), set), okB)
  (f, (fit, (lv, (cons, all))))

law cert_pick:
  for +f: +List<Spec.Tree>
  for +rest: +List<+List<Spec.Tree>>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +its: +List<Spec.Item>
  for +d: Nat
  for +i: Nat
  for +len: Nat
  for +e: Nat
  for cases: Either<{Ext.certOk(grammar, input, set, index, prefix, its, d, i, len, e, f) == True{} : Bool}, {Ext.anyCert(rest, grammar, input, set, index, prefix, its, d, i, len, e) == True{} : Bool}>
  for later: {Ext.anyCert(rest, grammar, input, set, index, prefix, its, d, i, len, e) == True{} : Bool} -> Reading(grammar, its, input, set, index, prefix, i, e, d, len)
  Reading(grammar, its, input, set, index, prefix, i, e, d, len)

def cert_pick(f, rest, grammar, input, set, index, prefix, its, d, i, len, e, cases, later):
  match cases:
    case Inl{c1}:
      cert_one(grammar, input, set, index, prefix, its, d, i, len, e, f, c1)
    case Inr{c2}:
      later(c2)

law cert_any:
  for fs: +List<+List<Spec.Tree>>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +its: +List<Spec.Item>
  for +d: Nat
  for +i: Nat
  for +len: Nat
  for +e: Nat
  for +ok: {Ext.anyCert(fs, grammar, input, set, index, prefix, its, d, i, len, e) == True{} : Bool}
  Reading(grammar, its, input, set, index, prefix, i, e, d, len)

def cert_any(fs, grammar, input, set, index, prefix, its, d, i, len, e, ok):
  match fs:
    case Nil{}:
      Empty.absurd(Reading(grammar, its, input, set, index, prefix, i, e, d, len), Lemma.false_is_not_true(ok))
    case Con{+f, +rest}:
      cert_pick(f, rest, grammar, input, set, index, prefix, its, d, i, len, e, Lemma.or_true_cases(Ext.certOk(grammar, input, set, index, prefix, its, d, i, len, e, f), Ext.anyCert(rest, grammar, input, set, index, prefix, its, d, i, len, e), ok),
        r => cert_any(rest, grammar, input, set, index, prefix, its, d, i, len, e, r))

# A certified length comes with a reading of that length, made of the set's steps.
law cert_reading:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +its: +List<Spec.Item>
  for +d: Nat
  for +i: Nat
  for +len: Nat
  for +e: Nat
  for +ok: {Ext.certified(Ext.Seq{fuel, grammar, input, set, index, rpath, prefix, its}, d, i, len, e) == True{} : Bool}
  Reading(grammar, its, input, set, index, prefix, i, e, d, len)

def cert_reading(fuel, grammar, input, set, index, rpath, prefix, its, d, i, len, e, ok):
  +fs = Prefer.seqForests(Witness.solve(fuel, grammar, input, set, [], Witness.TSeq{Prune.Seg{index, rpath, i, List.length(&2, Spec.Item, its), e}}))
  cert_any(fs, grammar, input, set, index, prefix, its, d, i, len, e, ok)

law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

def sub_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# ======== A FOREST KEEPS ITS OWN CONSTRAINT ========

# The length of child n, and where it starts and ends when the forest starts at `from`.
def lenAt(f: +List<Spec.Tree>, n: Nat) -> Nat:
  match f n:
    case Nil{} _:
      0n
    case Con{+t, ts} 0n:
      List.length(&2, Nat, Spec.leaves([t]))
    case Con{t, +ts} 1n+m:
      lenAt(ts, m)

def startOf(f: +List<Spec.Tree>, n: Nat, +from: Nat) -> Nat:
  match f n:
    case _ 0n:
      from
    case Nil{} 1n+m:
      from
    case Con{+t, +ts} 1n+m:
      startOf(ts, m, Nat.add(from, List.length(&2, Nat, Spec.leaves([t]))))

def endAt(f: +List<Spec.Tree>, n: Nat, +from: Nat) -> Nat:
  match f n:
    case Nil{} _:
      from
    case Con{+t, ts} 0n:
      Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
    case Con{+t, +ts} 1n+m:
      endAt(ts, m, Nat.add(from, List.length(&2, Nat, Spec.leaves([t]))))

def markOk(f: +List<Spec.Tree>, +q: Nat, +from: Nat, +d: Nat, +len: Nat) -> Bool:
  match f:
    case Nil{}:
      True{}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      Bool.and(Bool.or(Bool.not(Nat.is_eq(q, d)), Nat.is_eq(Nat.sub(b, from), len)), markOk(ts, 1n+q, b, d, len))

def stepsOk(f: +List<Spec.Tree>, +q: Nat, +from: Nat, +hasStep: Bool, +p: Nat, +k: Nat, +j: Nat) -> Bool:
  match f:
    case Nil{}:
      True{}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      Bool.and(Ext.stepOk(hasStep, q, from, b, p, k, j), stepsOk(ts, 1n+q, b, hasStep, p, k, j))

law and_four:
  for a: Bool
  for b: Bool
  for c: Bool
  for d: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  for ec: {c == True{} : Bool}
  for ed: {d == True{} : Bool}
  {Bool.and(Bool.and(a, b), Bool.and(c, d)) == True{} : Bool}

def and_four(a, b, c, d, ea, eb, ec, ed):
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case False{} _ _ _:
      Empty.absurd({Bool.and(Bool.and(False{}, b), Bool.and(c, d)) == True{} : Bool}, Lemma.false_is_not_true(ea))
    case True{} False{} _ _:
      Empty.absurd({Bool.and(Bool.and(True{}, False{}), Bool.and(c, d)) == True{} : Bool}, Lemma.false_is_not_true(eb))
    case True{} True{} False{} _:
      Empty.absurd({Bool.and(Bool.and(True{}, True{}), Bool.and(False{}, d)) == True{} : Bool}, Lemma.false_is_not_true(ec))
    case True{} True{} True{} False{}:
      Empty.absurd({Bool.and(Bool.and(True{}, True{}), Bool.and(True{}, False{})) == True{} : Bool}, Lemma.false_is_not_true(ed))

# The constraint is the mark check and the step check together.
law cons_split:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for +d: Nat
  for +len: Nat
  for +hasStep: Bool
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +mk: {markOk(f, q, from, d, len) == True{} : Bool}
  for +st: {stepsOk(f, q, from, hasStep, p, k, j) == True{} : Bool}
  {Ext.consOk(f, q, from, d, len, hasStep, p, k, j) == True{} : Bool}

def cons_split(f, q, from, d, len, hasStep, p, k, j, mk, st):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      +m1 = Bool.or(Bool.not(Nat.is_eq(q, d)), Nat.is_eq(Nat.sub(b, from), len))
      +s1 = Ext.stepOk(hasStep, q, from, b, p, k, j)
      +mkH = Lemma.and_true_left(m1, markOk(ts, 1n+q, b, d, len), mk)
      +mkT = Lemma.and_true_right_side(m1, markOk(ts, 1n+q, b, d, len), mk)
      +stH = Lemma.and_true_left(s1, stepsOk(ts, 1n+q, b, hasStep, p, k, j), st)
      +stT = Lemma.and_true_right_side(s1, stepsOk(ts, 1n+q, b, hasStep, p, k, j), st)
      Lemma.and_true_intro(Ext.okAt(q, from, b, d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, b, d, len, hasStep, p, k, j), Lemma.and_true_intro(m1, s1, mkH, stH), cons_split(ts, 1n+q, b, d, len, hasStep, p, k, j, mkT, stT))

law eq_succ_add_false:
  for +q: Nat
  for +n: Nat
  {Nat.is_eq(q, Nat.add(q, 1n+n)) == False{} : Bool}

def eq_succ_add_false(q, n):
  Equal.trans(Bool, Nat.is_eq(q, Nat.add(q, 1n+n)), Nat.is_eq(Nat.add(q, 1n+n), q), False{}, Lemma.nat_eq_symm(q, Nat.add(q, 1n+n)), Lemma.add_succ_ne(q, n))

law eq_add_zero:
  for +q: Nat
  {Nat.is_eq(q, Nat.add(q, 0n)) == True{} : Bool}

def eq_add_zero(q):
  Equal.trans(Bool, Nat.is_eq(q, Nat.add(q, 0n)), Nat.is_eq(q, q), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(q, v), Nat.add(q, 0n), q, Lemma.add_zero_right(q)), Lemma.nat_eq_refl(q))

law lt_ne:
  for a: Nat
  for b: Nat
  for lt: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_eq(a, b) == False{} : Bool}

def lt_ne(a, b, lt):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, Lemma.false_is_not_true(lt))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_ne(p, q, lt)

law lt_succ:
  for a: Nat
  for b: Nat
  for lt: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, 1n+b) == True{} : Bool}

def lt_succ(a, b, lt):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 1n) == True{} : Bool}, Lemma.lt_zero_false(a, lt))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_succ(p, q, lt)

# Past the marked item every mark check holds.
law mark_past:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for +d: Nat
  for +len: Nat
  for +gt: {Nat.is_lt(d, q) == True{} : Bool}
  {markOk(f, q, from, d, len) == True{} : Bool}

def mark_past(f, q, from, d, len, gt):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      +ne = Equal.trans(Bool, Nat.is_eq(q, d), Nat.is_eq(d, q), False{}, Lemma.nat_eq_symm(q, d), lt_ne(d, q, gt))
      +h = Equal.cong(Bool, Bool, v => Bool.or(Bool.not(v), Nat.is_eq(Nat.sub(b, from), len)), Nat.is_eq(q, d), False{}, ne)
      Lemma.and_true_intro(Bool.or(Bool.not(Nat.is_eq(q, d)), Nat.is_eq(Nat.sub(b, from), len)), markOk(ts, 1n+q, b, d, len), h, mark_past(ts, 1n+q, b, d, len, lt_succ(d, q, gt)))

law lt_self:
  for q: Nat
  {Nat.is_lt(q, 1n+q) == True{} : Bool}

def lt_self(q):
  match q:
    case 0n:
      {==}
    case 1n+p:
      lt_self(p)

law lt_add_zero:
  for +q: Nat
  {Nat.is_lt(Nat.add(q, 0n), 1n+q) == True{} : Bool}

def lt_add_zero(q):
  Equal.trans(Bool, Nat.is_lt(Nat.add(q, 0n), 1n+q), Nat.is_lt(q, 1n+q), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, 1n+q), Nat.add(q, 0n), q, Lemma.add_zero_right(q)), lt_self(q))

# A forest keeps its own mark: the marked child (dd after q) reads lenAt tokens.
law mark_own:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for dd: Nat
  {markOk(f, q, from, Nat.add(q, dd), lenAt(f, dd)) == True{} : Bool}

def mark_own(f, q, from, dd):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      match dd:
        case 0n:
          +lt = List.length(&2, Nat, Spec.leaves([t]))
          +b = Nat.add(from, lt)
          +sb = Lemma.sub_add_left(from, lt)
          +h = Lemma.or_true_right_intro(Bool.not(Nat.is_eq(q, Nat.add(q, 0n))), Nat.is_eq(Nat.sub(b, from), lt), Lemma.nat_eq_of_eq(Nat.sub(b, from), lt, sb))
          Lemma.and_true_intro(Bool.or(Bool.not(Nat.is_eq(q, Nat.add(q, 0n))), Nat.is_eq(Nat.sub(b, from), lt)), markOk(ts, 1n+q, b, Nat.add(q, 0n), lt), h, mark_past(ts, 1n+q, b, Nat.add(q, 0n), lt, lt_add_zero(q)))
        case 1n+(+n):
          +lt = List.length(&2, Nat, Spec.leaves([t]))
          +b = Nat.add(from, lt)
          +ne = eq_succ_add_false(q, n)
          +h = Equal.cong(Bool, Bool, v => Bool.or(Bool.not(v), Nat.is_eq(Nat.sub(b, from), lenAt(ts, n))), Nat.is_eq(q, Nat.add(q, 1n+n)), False{}, ne)
          +dEq = Equal.trans(Nat, Nat.add(1n+q, n), 1n+Nat.add(q, n), Nat.add(q, 1n+n), {==}, Equal.sym(Nat, Nat.add(q, 1n+n), 1n+Nat.add(q, n), Lemma.add_succ_right(q, n)))
          +rest = Equal.trans(Bool, markOk(ts, 1n+q, b, Nat.add(q, 1n+n), lenAt(ts, n)), markOk(ts, 1n+q, b, Nat.add(1n+q, n), lenAt(ts, n)), True{}, Equal.cong(Nat, Bool, v => markOk(ts, 1n+q, b, v, lenAt(ts, n)), Nat.add(q, 1n+n), Nat.add(1n+q, n), Equal.sym(Nat, Nat.add(1n+q, n), Nat.add(q, 1n+n), dEq)), mark_own(ts, 1n+q, b, n))
          Lemma.and_true_intro(Bool.or(Bool.not(Nat.is_eq(q, Nat.add(q, 1n+n))), Nat.is_eq(Nat.sub(b, from), lenAt(ts, n))), markOk(ts, 1n+q, b, Nat.add(q, 1n+n), lenAt(ts, n)), h, rest)

law steps_none:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for +p: Nat
  for +k: Nat
  for +j: Nat
  {stepsOk(f, q, from, False{}, p, k, j) == True{} : Bool}

def steps_none(f, q, from, p, k, j):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      steps_none(ts, 1n+q, Nat.add(from, List.length(&2, Nat, Spec.leaves([t]))), p, k, j)

law steps_past:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +gt: {Nat.is_lt(p, q) == True{} : Bool}
  {stepsOk(f, q, from, True{}, p, k, j) == True{} : Bool}

def steps_past(f, q, from, p, k, j, gt):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      +ne = Equal.trans(Bool, Nat.is_eq(q, p), Nat.is_eq(p, q), False{}, Lemma.nat_eq_symm(q, p), lt_ne(p, q, gt))
      +h = Equal.cong(Bool, Bool, v => Bool.or(Bool.not(v), Bool.and(Nat.is_eq(from, k), Nat.is_eq(b, j))), Nat.is_eq(q, p), False{}, ne)
      Lemma.and_true_intro(Ext.stepOk(True{}, q, from, b, p, k, j), stepsOk(ts, 1n+q, b, True{}, p, k, j), h, steps_past(ts, 1n+q, b, p, k, j, lt_succ(p, q, gt)))

# A forest keeps its own steps: child pp (after q) starts and ends where it does.
law steps_own:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for pp: Nat
  {stepsOk(f, q, from, True{}, Nat.add(q, pp), startOf(f, pp, from), endAt(f, pp, from)) == True{} : Bool}

def steps_own(f, q, from, pp):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      match pp:
        case 0n:
          +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
          +both = Lemma.and_true_intro(Nat.is_eq(from, from), Nat.is_eq(b, b), Lemma.nat_eq_refl(from), Lemma.nat_eq_refl(b))
          +h = Lemma.or_true_right_intro(Bool.not(Nat.is_eq(q, Nat.add(q, 0n))), Bool.and(Nat.is_eq(from, from), Nat.is_eq(b, b)), both)
          Lemma.and_true_intro(Ext.stepOk(True{}, q, from, b, Nat.add(q, 0n), from, b), stepsOk(ts, 1n+q, b, True{}, Nat.add(q, 0n), from, b), h, steps_past(ts, 1n+q, b, Nat.add(q, 0n), from, b, lt_add_zero(q)))
        case 1n+(+n):
          +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
          +k = startOf(ts, n, b)
          +j = endAt(ts, n, b)
          +ne = eq_succ_add_false(q, n)
          +h = Equal.cong(Bool, Bool, v => Bool.or(Bool.not(v), Bool.and(Nat.is_eq(from, k), Nat.is_eq(b, j))), Nat.is_eq(q, Nat.add(q, 1n+n)), False{}, ne)
          +dEq = Equal.trans(Nat, Nat.add(1n+q, n), 1n+Nat.add(q, n), Nat.add(q, 1n+n), {==}, Equal.sym(Nat, Nat.add(q, 1n+n), 1n+Nat.add(q, n), Lemma.add_succ_right(q, n)))
          +rest = Equal.trans(Bool, stepsOk(ts, 1n+q, b, True{}, Nat.add(q, 1n+n), k, j), stepsOk(ts, 1n+q, b, True{}, Nat.add(1n+q, n), k, j), True{}, Equal.cong(Nat, Bool, v => stepsOk(ts, 1n+q, b, True{}, v, k, j), Nat.add(q, 1n+n), Nat.add(1n+q, n), Equal.sym(Nat, Nat.add(1n+q, n), Nat.add(q, 1n+n), dEq)), steps_own(ts, 1n+q, b, n))
          Lemma.and_true_intro(Ext.stepOk(True{}, q, from, b, Nat.add(q, 1n+n), k, j), stepsOk(ts, 1n+q, b, True{}, Nat.add(q, 1n+n), k, j), h, rest)

law cons_mark:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for +d: Nat
  for +len: Nat
  for +hasStep: Bool
  for +p: Nat
  for +k: Nat
  for +j: Nat
  for +c: {Ext.consOk(f, q, from, d, len, hasStep, p, k, j) == True{} : Bool}
  {markOk(f, q, from, d, len) == True{} : Bool}

def cons_mark(f, q, from, d, len, hasStep, p, k, j, c):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
      +m1 = Bool.or(Bool.not(Nat.is_eq(q, d)), Nat.is_eq(Nat.sub(b, from), len))
      +s1 = Ext.stepOk(hasStep, q, from, b, p, k, j)
      +h = Lemma.and_true_left(Ext.okAt(q, from, b, d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, b, d, len, hasStep, p, k, j), c)
      +r = Lemma.and_true_right_side(Ext.okAt(q, from, b, d, len, hasStep, p, k, j), Ext.consOk(ts, 1n+q, b, d, len, hasStep, p, k, j), c)
      Lemma.and_true_intro(m1, markOk(ts, 1n+q, b, d, len), Lemma.and_true_left(m1, s1, h), cons_mark(ts, 1n+q, b, d, len, hasStep, p, k, j, r))

# The marked child reads len tokens, when the forest has it.
law mark_len:
  for f: +List<Spec.Tree>
  for +q: Nat
  for +from: Nat
  for dd: Nat
  for +len: Nat
  for +mk: {markOk(f, q, from, Nat.add(q, dd), len) == True{} : Bool}
  for +has: {Nat.is_lt(dd, List.length(&2, Spec.Tree, f)) == True{} : Bool}
  {lenAt(f, dd) == len : Nat}

def mark_len(f, q, from, dd, len, mk, has):
  match f:
    case Nil{}:
      Empty.absurd({lenAt([], dd) == len : Nat}, Lemma.lt_zero_false(dd, has))
    case Con{+t, +ts}:
      match dd:
        case 0n:
          +lt = List.length(&2, Nat, Spec.leaves([t]))
          +b = Nat.add(from, lt)
          +h0 = Lemma.and_true_left(Bool.or(Bool.not(Nat.is_eq(q, Nat.add(q, 0n))), Nat.is_eq(Nat.sub(b, from), len)), markOk(ts, 1n+q, b, Nat.add(q, 0n), len), mk)
          +h1 = Equal.trans(Bool, Bool.or(False{}, Nat.is_eq(Nat.sub(b, from), len)), Bool.or(Bool.not(Nat.is_eq(q, Nat.add(q, 0n))), Nat.is_eq(Nat.sub(b, from), len)), True{}, Equal.cong(Bool, Bool, v => Bool.or(Bool.not(v), Nat.is_eq(Nat.sub(b, from), len)), True{}, Nat.is_eq(q, Nat.add(q, 0n)), Equal.sym(Bool, Nat.is_eq(q, Nat.add(q, 0n)), True{}, eq_add_zero(q))), h0)
          +e1 = Lemma.nat_eq_sound(Nat.sub(b, from), len, h1)
          Equal.trans(Nat, lt, Nat.sub(b, from), len, Equal.sym(Nat, Nat.sub(b, from), lt, Lemma.sub_add_left(from, lt)), e1)
        case 1n+(+n):
          +b = Nat.add(from, List.length(&2, Nat, Spec.leaves([t])))
          +r = Lemma.and_true_right_side(Bool.or(Bool.not(Nat.is_eq(q, Nat.add(q, 1n+n))), Nat.is_eq(Nat.sub(b, from), len)), markOk(ts, 1n+q, b, Nat.add(q, 1n+n), len), mk)
          +dEq = Equal.trans(Nat, Nat.add(1n+q, n), 1n+Nat.add(q, n), Nat.add(q, 1n+n), {==}, Equal.sym(Nat, Nat.add(q, 1n+n), 1n+Nat.add(q, n), Lemma.add_succ_right(q, n)))
          +r2 = Equal.trans(Bool, markOk(ts, 1n+q, b, Nat.add(1n+q, n), len), markOk(ts, 1n+q, b, Nat.add(q, 1n+n), len), True{}, Equal.cong(Nat, Bool, v => markOk(ts, 1n+q, b, v, len), Nat.add(1n+q, n), Nat.add(q, 1n+n), dEq), r)
          mark_len(ts, 1n+q, b, n, len, r2, has)

# ======== THE MARKED ITEM AND THE MEASURES ========

def isNoMark(m: Ext.Marked) -> Bool:
  match m:
    case Ext.NoMark{}:
      True{}
    case Ext.OneMark{d, e}:
      False{}
    case Ext.ManyMarks{}:
      False{}

def isMany(m: Ext.Marked) -> Bool:
  match m:
    case Ext.NoMark{}:
      False{}
    case Ext.OneMark{d, e}:
      False{}
    case Ext.ManyMarks{}:
      True{}

def markD(m: Ext.Marked) -> Nat:
  match m:
    case Ext.NoMark{}:
      0n
    case Ext.OneMark{+d, e}:
      d
    case Ext.ManyMarks{}:
      0n

def markE(m: Ext.Marked) -> Spec.Extent:
  match m:
    case Ext.NoMark{}:
      Spec.Longest{}
    case Ext.OneMark{d, +e}:
      e
    case Ext.ManyMarks{}:
      Spec.Longest{}

law add_stays:
  for acc: Ext.Marked
  for found: Maybe<&2, Spec.Extent>
  for +dot: Nat
  for +h: {isNoMark(acc) == False{} : Bool}
  {isNoMark(Ext.addMark(acc, found, dot)) == False{} : Bool}

def add_stays(acc, found, dot, h):
  match acc found:
    case Ext.NoMark{} _:
      Empty.absurd({isNoMark(Ext.addMark(Ext.NoMark{}, found, dot)) == False{} : Bool}, Lemma.true_is_not_false(h))
    case Ext.OneMark{+d, +e} None{}:
      {==}
    case Ext.OneMark{d, e} Some{e2}:
      {==}
    case Ext.ManyMarks{} _:
      {==}

# Once marked, the sequence stays marked.
law marked_stays:
  for its: +List<Spec.Item>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +acc: Ext.Marked
  for +h: {isNoMark(acc) == False{} : Bool}
  {isNoMark(Ext.markedFrom(its, marks, index, prefix, dot, acc)) == False{} : Bool}

def marked_stays(its, marks, index, prefix, dot, acc, h):
  match its:
    case Nil{}:
      h
    case Con{+it, +rest}:
      +found = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      marked_stays(rest, marks, index, prefix, 1n+dot, Ext.addMark(acc, found, dot), add_stays(acc, found, dot, h))

law add_many:
  for acc: Ext.Marked
  for found: Maybe<&2, Spec.Extent>
  for +dot: Nat
  for +h: {isMany(acc) == True{} : Bool}
  {isMany(Ext.addMark(acc, found, dot)) == True{} : Bool}

def add_many(acc, found, dot, h):
  match acc found:
    case Ext.NoMark{} _:
      Empty.absurd({isMany(Ext.addMark(Ext.NoMark{}, found, dot)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Ext.OneMark{d, e} _:
      Empty.absurd({isMany(Ext.addMark(Ext.OneMark{d, e}, found, dot)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Ext.ManyMarks{} _:
      {==}

law many_stays:
  for its: +List<Spec.Item>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +acc: Ext.Marked
  for +h: {isMany(acc) == True{} : Bool}
  {isMany(Ext.markedFrom(its, marks, index, prefix, dot, acc)) == True{} : Bool}

def many_stays(its, marks, index, prefix, dot, acc, h):
  match its:
    case Nil{}:
      h
    case Con{+it, +rest}:
      +found = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      many_stays(rest, marks, index, prefix, 1n+dot, Ext.addMark(acc, found, dot), add_many(acc, found, dot, h))

law measures_nil_items:
  for f: +List<Spec.Tree>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  {Spec.measures(marks, f, [], index, prefix, dot) == [] : +List<Spec.Measure>}

def measures_nil_items(f, marks, index, prefix, dot):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      {==}

law beats_nil:
  for xs: +List<Spec.Measure>
  {Spec.beats(xs, []) == False{} : Bool}

def beats_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Spec.Measure{e, a}:
          {==}

law or_and_f:
  for x: Bool
  for y: Bool
  {Bool.or(x, Bool.and(y, False{})) == x : Bool}

def or_and_f(x, y):
  match x y:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

law beats_one:
  for +e: Spec.Extent
  for +a: Nat
  for +b: Nat
  {Spec.beats([Spec.Measure{e, a}], [Spec.Measure{e, b}]) == Spec.better(e, a, b) : Bool}

def beats_one(e, a, b):
  or_and_f(Spec.better(e, a, b), Nat.is_eq(a, b))

law nomark_pick:
  for found: Maybe<&2, Spec.Extent>
  for +marks: +List<Spec.ExtentMark>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == found : Maybe<&2, Spec.Extent>}
  for +h: {isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), dot))) == True{} : Bool}
  for later: {isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.NoMark{})) == True{} : Bool} -> {Spec.measures(marks, ts, rest, index, prefix, 1n+dot) == [] : +List<Spec.Measure>}
  {Spec.measures(marks, t <> ts, it <> rest, index, prefix, dot) == [] : +List<Spec.Measure>}

def nomark_pick(found, marks, it, rest, t, ts, index, prefix, dot, eqF, h, later):
  match found:
    case None{}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Bool, isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.NoMark{})), isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, ie, dot))), True{}, Equal.cong(Maybe<&2, Spec.Extent>, Bool, v => isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, v, dot))), None{}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, None{}, eqF)), h)
      %Equal.sym(Maybe<&2, Spec.Extent>, ie, None{}, eqF) : {Spec.measureIf(_, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)) == [] : +List<Spec.Measure>}
      later(h2)
    case Some{+e}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Bool, isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{dot, e})), isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, ie, dot))), True{}, Equal.cong(Maybe<&2, Spec.Extent>, Bool, v => isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, v, dot))), Some{e}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, Some{e}, eqF)), h)
      Empty.absurd({Spec.measures(marks, t <> ts, it <> rest, index, prefix, dot) == [] : +List<Spec.Measure>}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{dot, e})), False{}, Equal.sym(Bool, isNoMark(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{dot, e})), True{}, h2), marked_stays(rest, marks, index, prefix, 1n+dot, Ext.OneMark{dot, e}, {==}))))

# With no marked item, a forest has no measures.
law measures_nomark:
  for its: +List<Spec.Item>
  for f: +List<Spec.Tree>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +h: {isNoMark(Ext.markedFrom(its, marks, index, prefix, dot, Ext.NoMark{})) == True{} : Bool}
  {Spec.measures(marks, f, its, index, prefix, dot) == [] : +List<Spec.Measure>}

def measures_nomark(its, f, marks, index, prefix, dot, h):
  match its:
    case Nil{}:
      measures_nil_items(f, marks, index, prefix, dot)
    case Con{+it, +rest}:
      match f:
        case Nil{}:
          {==}
        case Con{+t, +ts}:
          nomark_pick(Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), marks, it, rest, t, ts, index, prefix, dot, {==}, h,
            h2 => measures_nomark(rest, ts, marks, index, prefix, 1n+dot, h2))

def OneRest(+marks: +List<Spec.ExtentMark>, +f: +List<Spec.Tree>, +its: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +d0: Nat, +e0: Spec.Extent, +d: Nat, +e: Spec.Extent) -> Type:
  {d0 == d : Nat} & {e0 == e : Spec.Extent} & {Spec.measures(marks, f, its, index, prefix, dot) == [] : +List<Spec.Measure>}

def tailOf(f: +List<Spec.Tree>) -> +List<Spec.Tree>:
  match f:
    case Nil{}:
      []
    case Con{t, +ts}:
      ts

# The step from the rest of the forest back to the whole: the first item is unmarked.
law one_rest_step:
  for +marks: +List<Spec.ExtentMark>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for f: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d0: Nat
  for +e0: Spec.Extent
  for +d: Nat
  for +e: Spec.Extent
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == None{} : Maybe<&2, Spec.Extent>}
  for r: OneRest(marks, tailOf(f), rest, index, prefix, 1n+dot, d0, e0, d, e)
  OneRest(marks, f, it <> rest, index, prefix, dot, d0, e0, d, e)

def one_rest_step(marks, it, rest, f, index, prefix, dot, d0, e0, d, e, eqF, r):
  match f:
    case Nil{}:
      match r:
        case (a, (b, c)):
          (a, (b, {==}))
    case Con{+t, +ts}:
      match r:
        case (a, (b, c0)):
          +c = {c0 : {Spec.measures(marks, ts, rest, index, prefix, 1n+dot) == [] : +List<Spec.Measure>}}
          +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
          +m = Equal.trans(+List<Spec.Measure>, Spec.measureIf(ie, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), Spec.measureIf(None{}, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), [], Equal.cong(Maybe<&2, Spec.Extent>, +List<Spec.Measure>, v => Spec.measureIf(v, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), ie, None{}, eqF), c)
          (a, (b, m))

law one_pick:
  for found: Maybe<&2, Spec.Extent>
  for +marks: +List<Spec.ExtentMark>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d0: Nat
  for +e0: Spec.Extent
  for +d: Nat
  for +e: Spec.Extent
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == found : Maybe<&2, Spec.Extent>}
  for +h: {Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.OneMark{d0, e0}, Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), dot)) == Ext.OneMark{d, e} : Ext.Marked}
  for later: {Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{d0, e0}) == Ext.OneMark{d, e} : Ext.Marked} -> OneRest(marks, tailOf(f), rest, index, prefix, 1n+dot, d0, e0, d, e)
  OneRest(marks, f, it <> rest, index, prefix, dot, d0, e0, d, e)

def one_pick(found, marks, it, rest, f, index, prefix, dot, d0, e0, d, e, eqF, h, later):
  match found:
    case None{}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Ext.Marked, Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{d0, e0}), Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.OneMark{d0, e0}, ie, dot)), Ext.OneMark{d, e}, Equal.cong(Maybe<&2, Spec.Extent>, Ext.Marked, v => Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.OneMark{d0, e0}, v, dot)), None{}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, None{}, eqF)), h)
      one_rest_step(marks, it, rest, f, index, prefix, dot, d0, e0, d, e, eqF, later(h2))
    case Some{+e2}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Ext.Marked, Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.ManyMarks{}), Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.OneMark{d0, e0}, ie, dot)), Ext.OneMark{d, e}, Equal.cong(Maybe<&2, Spec.Extent>, Ext.Marked, v => Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.OneMark{d0, e0}, v, dot)), Some{e2}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, Some{e2}, eqF)), h)
      +m1 = many_stays(rest, marks, index, prefix, 1n+dot, Ext.ManyMarks{}, {==})
      Empty.absurd(OneRest(marks, f, it <> rest, index, prefix, dot, d0, e0, d, e), Lemma.true_is_not_false(Equal.trans(Bool, True{}, isMany(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.ManyMarks{})), False{}, Equal.sym(Bool, isMany(Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.ManyMarks{})), True{}, m1), Equal.cong(Ext.Marked, Bool, v => isMany(v), Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.ManyMarks{}), Ext.OneMark{d, e}, h2))))

# After the marked item, no more marks: the same mark comes out, and no measures.
law marked_one:
  for its: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d0: Nat
  for +e0: Spec.Extent
  for +d: Nat
  for +e: Spec.Extent
  for +h: {Ext.markedFrom(its, marks, index, prefix, dot, Ext.OneMark{d0, e0}) == Ext.OneMark{d, e} : Ext.Marked}
  OneRest(marks, f, its, index, prefix, dot, d0, e0, d, e)

def marked_one(its, f, marks, index, prefix, dot, d0, e0, d, e, h):
  match its:
    case Nil{}:
      (Equal.cong(Ext.Marked, Nat, v => markD(v), Ext.OneMark{d0, e0}, Ext.OneMark{d, e}, h), (Equal.cong(Ext.Marked, Spec.Extent, v => markE(v), Ext.OneMark{d0, e0}, Ext.OneMark{d, e}, h), measures_nil_items(f, marks, index, prefix, dot)))
    case Con{+it, +rest}:
      one_pick(Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), marks, it, rest, f, index, prefix, dot, d0, e0, d, e, {==}, h,
        h2 => marked_one(rest, tailOf(f), marks, index, prefix, 1n+dot, d0, e0, d, e, h2))

def MeasOne(+marks: +List<Spec.ExtentMark>, +f: +List<Spec.Tree>, +its: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +d: Nat, +e: Spec.Extent) -> Type:
  {Spec.measures(marks, f, its, index, prefix, dot) == [Spec.Measure{e, lenAt(f, Nat.sub(d, dot))}] : +List<Spec.Measure>} & {Nat.is_lt(Nat.sub(d, dot), List.length(&2, Spec.Tree, f)) == True{} : Bool} & {Nat.is_le(dot, d) == True{} : Bool}

law sub_succ_le:
  for d: Nat
  for dot: Nat
  for le: {Nat.is_le(1n+dot, d) == True{} : Bool}
  {Nat.sub(d, dot) == 1n+Nat.sub(d, 1n+dot) : Nat}

def sub_succ_le(d, dot, le):
  match d dot:
    case 0n _:
      Empty.absurd({Nat.sub(0n, dot) == 1n+Nat.sub(0n, 1n+dot) : Nat}, Lemma.false_is_not_true(le))
    case 1n+p 0n:
      Equal.cong(Nat, Nat, v => 1n+v, p, Nat.sub(p, 0n), Equal.sym(Nat, Nat.sub(p, 0n), p, Lemma.sub_zero(p)))
    case 1n+p 1n+q:
      sub_succ_le(p, q, le)

law one_none_step:
  for +marks: +List<Spec.ExtentMark>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d: Nat
  for +e: Spec.Extent
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == None{} : Maybe<&2, Spec.Extent>}
  for mo: MeasOne(marks, ts, rest, index, prefix, 1n+dot, d, e)
  MeasOne(marks, t <> ts, it <> rest, index, prefix, dot, d, e)

def one_none_step(marks, it, rest, t, ts, index, prefix, dot, d, e, eqF, mo):
  match mo:
    case (m0, (lt0, le0)):
      +mR = {m0 : {Spec.measures(marks, ts, rest, index, prefix, 1n+dot) == [Spec.Measure{e, lenAt(ts, Nat.sub(d, 1n+dot))}] : +List<Spec.Measure>}}
      +ltR = {lt0 : {Nat.is_lt(Nat.sub(d, 1n+dot), List.length(&2, Spec.Tree, ts)) == True{} : Bool}}
      +leR = {le0 : {Nat.is_le(1n+dot, d) == True{} : Bool}}
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +sEq = sub_succ_le(d, dot, leR)
      +lenEq = Equal.cong(Nat, Nat, v => lenAt(t <> ts, v), Nat.sub(d, dot), 1n+Nat.sub(d, 1n+dot), sEq)
      +m1 = Equal.trans(+List<Spec.Measure>, Spec.measureIf(ie, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), Spec.measures(marks, ts, rest, index, prefix, 1n+dot), [Spec.Measure{e, lenAt(t <> ts, Nat.sub(d, dot))}], Equal.cong(Maybe<&2, Spec.Extent>, +List<Spec.Measure>, v => Spec.measureIf(v, List.length(&2, Nat, Spec.leaves([t])), Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), ie, None{}, eqF),
        Equal.trans(+List<Spec.Measure>, Spec.measures(marks, ts, rest, index, prefix, 1n+dot), [Spec.Measure{e, lenAt(ts, Nat.sub(d, 1n+dot))}], [Spec.Measure{e, lenAt(t <> ts, Nat.sub(d, dot))}], mR, Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{e, v}], lenAt(ts, Nat.sub(d, 1n+dot)), lenAt(t <> ts, Nat.sub(d, dot)), Equal.sym(Nat, lenAt(t <> ts, Nat.sub(d, dot)), lenAt(ts, Nat.sub(d, 1n+dot)), lenEq))))
      +lt1 = Equal.trans(Bool, Nat.is_lt(Nat.sub(d, dot), 1n+List.length(&2, Spec.Tree, ts)), Nat.is_lt(1n+Nat.sub(d, 1n+dot), 1n+List.length(&2, Spec.Tree, ts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, 1n+List.length(&2, Spec.Tree, ts)), Nat.sub(d, dot), 1n+Nat.sub(d, 1n+dot), sEq), ltR)
      (m1, (lt1, Lemma.le_of_succ_le(dot, d, leR)))

law one_some_step:
  for +marks: +List<Spec.ExtentMark>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d: Nat
  for +e: Spec.Extent
  for +e2: Spec.Extent
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == Some{e2} : Maybe<&2, Spec.Extent>}
  for r: OneRest(marks, ts, rest, index, prefix, 1n+dot, dot, e2, d, e)
  MeasOne(marks, t <> ts, it <> rest, index, prefix, dot, d, e)

def one_some_step(marks, it, rest, t, ts, index, prefix, dot, d, e, e2, eqF, r):
  match r:
    case (dEq0, (eEq0, mts0)):
      +dEq = {dEq0 : {dot == d : Nat}}
      +eEq = {eEq0 : {e2 == e : Spec.Extent}}
      +mts = {mts0 : {Spec.measures(marks, ts, rest, index, prefix, 1n+dot) == [] : +List<Spec.Measure>}}
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +lt = List.length(&2, Nat, Spec.leaves([t]))
      +s0 = Equal.trans(Nat, Nat.sub(d, dot), Nat.sub(dot, dot), 0n, Equal.cong(Nat, Nat, v => Nat.sub(v, dot), d, dot, Equal.sym(Nat, dot, d, dEq)), sub_self(dot))
      +m1 = Equal.trans(+List<Spec.Measure>, Spec.measureIf(ie, lt, Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), Spec.measureIf(Some{e2}, lt, []), [Spec.Measure{e, lenAt(t <> ts, Nat.sub(d, dot))}],
        Equal.trans(+List<Spec.Measure>, Spec.measureIf(ie, lt, Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), Spec.measureIf(Some{e2}, lt, Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), Spec.measureIf(Some{e2}, lt, []), Equal.cong(Maybe<&2, Spec.Extent>, +List<Spec.Measure>, v => Spec.measureIf(v, lt, Spec.measures(marks, ts, rest, index, prefix, 1n+dot)), ie, Some{e2}, eqF), Equal.cong(+List<Spec.Measure>, +List<Spec.Measure>, v => Spec.measureIf(Some{e2}, lt, v), Spec.measures(marks, ts, rest, index, prefix, 1n+dot), [], mts)),
        Equal.trans(+List<Spec.Measure>, [Spec.Measure{e2, lt}], [Spec.Measure{e, lt}], [Spec.Measure{e, lenAt(t <> ts, Nat.sub(d, dot))}], Equal.cong(Spec.Extent, +List<Spec.Measure>, v => [Spec.Measure{v, lt}], e2, e, eEq), Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{e, lenAt(t <> ts, v)}], 0n, Nat.sub(d, dot), Equal.sym(Nat, Nat.sub(d, dot), 0n, s0))))
      +lt1 = Equal.trans(Bool, Nat.is_lt(Nat.sub(d, dot), 1n+List.length(&2, Spec.Tree, ts)), Nat.is_lt(0n, 1n+List.length(&2, Spec.Tree, ts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, 1n+List.length(&2, Spec.Tree, ts)), Nat.sub(d, dot), 0n, s0), {==})
      +le1 = Equal.trans(Bool, Nat.is_le(dot, d), Nat.is_le(dot, dot), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(dot, v), d, dot, Equal.sym(Nat, dot, d, dEq)), Lemma.le_refl(dot))
      (m1, (lt1, le1))

law one_found_pick:
  for found: Maybe<&2, Spec.Extent>
  for +marks: +List<Spec.ExtentMark>
  for +grammar: +List<Spec.Production>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d: Nat
  for +e: Spec.Extent
  for +eqF: {Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])) == found : Maybe<&2, Spec.Extent>}
  for +h: {Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), dot)) == Ext.OneMark{d, e} : Ext.Marked}
  for later: {Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.NoMark{}) == Ext.OneMark{d, e} : Ext.Marked} -> MeasOne(marks, ts, rest, index, prefix, 1n+dot, d, e)
  MeasOne(marks, t <> ts, it <> rest, index, prefix, dot, d, e)

def one_found_pick(found, marks, grammar, it, rest, t, ts, index, prefix, dot, d, e, eqF, h, later):
  match found:
    case None{}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Ext.Marked, Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.NoMark{}), Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, ie, dot)), Ext.OneMark{d, e}, Equal.cong(Maybe<&2, Spec.Extent>, Ext.Marked, v => Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, v, dot)), None{}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, None{}, eqF)), h)
      mo = later(h2)
      one_none_step(marks, it, rest, t, ts, index, prefix, dot, d, e, eqF, mo)
    case Some{+e2}:
      +ie = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      +h2 = Equal.trans(Ext.Marked, Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.OneMark{dot, e2}), Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, ie, dot)), Ext.OneMark{d, e}, Equal.cong(Maybe<&2, Spec.Extent>, Ext.Marked, v => Ext.markedFrom(rest, marks, index, prefix, 1n+dot, Ext.addMark(Ext.NoMark{}, v, dot)), Some{e2}, ie, Equal.sym(Maybe<&2, Spec.Extent>, ie, Some{e2}, eqF)), h)
      one_some_step(marks, it, rest, t, ts, index, prefix, dot, d, e, e2, eqF, marked_one(rest, ts, marks, index, prefix, 1n+dot, dot, e2, d, e, h2))

# With one marked item d, a forest that fits the items has the one measure of child d.
law measures_one:
  for its: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +marks: +List<Spec.ExtentMark>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +d: Nat
  for +e: Spec.Extent
  for +h: {Ext.markedFrom(its, marks, index, prefix, dot, Ext.NoMark{}) == Ext.OneMark{d, e} : Ext.Marked}
  for +fit: {Spec.fits(f, grammar, its) == True{} : Bool}
  MeasOne(marks, f, its, index, prefix, dot, d, e)

def measures_one(its, f, marks, grammar, index, prefix, dot, d, e, h, fit):
  match its:
    case Nil{}:
      Empty.absurd(MeasOne(marks, f, [], index, prefix, dot, d, e), Lemma.true_is_not_false(Equal.cong(Ext.Marked, Bool, v => isNoMark(v), Ext.NoMark{}, Ext.OneMark{d, e}, h)))
    case Con{+it, +rest}:
      match f:
        case Nil{}:
          Empty.absurd(MeasOne(marks, [], it <> rest, index, prefix, dot, d, e), Lemma.false_is_not_true(fit))
        case Con{+t, +ts}:
          one_found_pick(Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot])), marks, grammar, it, rest, t, ts, index, prefix, dot, d, e, {==}, h,
            h2 => measures_one(rest, ts, marks, grammar, index, prefix, 1n+dot, d, e, h2, Fits.fits_tail(t, ts, grammar, it, rest, fit)))

# ======== THE BEST LENGTH ========

def foundOr(b: Ext.Best, +len: Nat) -> Bool:
  match b:
    case Ext.Found{+x}:
      Nat.is_eq(x, len)
    case Ext.NoneFound{}:
      False{}
    case Ext.Unsure{}:
      True{}

def bestLen(b: Ext.Best) -> Nat:
  match b:
    case Ext.Found{+x}:
      x
    case Ext.NoneFound{}:
      0n
    case Ext.Unsure{}:
      0n

def isFound(b: Ext.Best) -> Bool:
  match b:
    case Ext.Found{x}:
      True{}
    case Ext.NoneFound{}:
      False{}
    case Ext.Unsure{}:
      False{}

law found_inj:
  for +a: Nat
  for +b: Nat
  for e: {Ext.Found{a} == Ext.Found{b} : Ext.Best}
  {a == b : Nat}

def found_inj(a, b, e):
  Equal.cong(Ext.Best, Nat, v => bestLen(v), Ext.Found{a}, Ext.Found{b}, e)

law not_found_unsure:
  for +b: Nat
  for e: {Ext.Unsure{} == Ext.Found{b} : Ext.Best}
  Empty

def not_found_unsure(b, e):
  Lemma.false_is_not_true(Equal.cong(Ext.Best, Bool, v => isFound(v), Ext.Unsure{}, Ext.Found{b}, e))

# A certified length is found; without a certificate the search is unsure.
law found_if_eq:
  for c: Bool
  for +a: Nat
  for +b: Nat
  for e: {Ext.foundIf(c, a) == Ext.Found{b} : Ext.Best}
  {a == b : Nat}

def found_if_eq(c, a, b, e):
  match c:
    case True{}:
      found_inj(a, b, e)
    case False{}:
      Empty.absurd({a == b : Nat}, not_found_unsure(b, e))

law found_if_or:
  for c: Bool
  for +n: Nat
  for +Lt: Nat
  for +nEq: {n == Lt : Nat}
  {foundOr(Ext.foundIf(c, n), Lt) == True{} : Bool}

def found_if_or(c, n, Lt, nEq):
  match c:
    case True{}:
      Lemma.nat_eq_of_eq(n, Lt, nEq)
    case False{}:
      {==}

law not_found_none:
  for +b: Nat
  for e: {Ext.NoneFound{} == Ext.Found{b} : Ext.Best}
  Empty

def not_found_none(b, e):
  Lemma.false_is_not_true(Equal.cong(Ext.Best, Bool, v => isFound(v), Ext.NoneFound{}, Ext.Found{b}, e))

# ---- Small order facts ----

law le_pred_ne:
  for L: Nat
  for m: Nat
  for le: {Nat.is_le(L, 1n+m) == True{} : Bool}
  for ne: {Nat.is_eq(L, 1n+m) == False{} : Bool}
  {Nat.is_le(L, m) == True{} : Bool}

def le_pred_ne(L, m, le, ne):
  match L m:
    case 0n _:
      Lemma.zero_le(m)
    case 1n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Lemma.true_is_not_false(ne))
    case 2n+r 0n:
      Empty.absurd({Nat.is_le(2n+r, 0n) == True{} : Bool}, Lemma.false_is_not_true(le))
    case 1n+p 1n+q:
      le_pred_ne(p, q, le, ne)

law lt_le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lt_le_trans(a, b, c, ab, bc):
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(a, c) == True{} : Bool}, Lemma.lt_zero_false(a, ab))
    case _ 1n+q 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, Lemma.false_is_not_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      lt_le_trans(p, q, r, ab, bc)

law lt_ge_absurd:
  for a: Nat
  for b: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  Empty

def lt_ge_absurd(a, b, ab, ba):
  match a b:
    case _ 0n:
      Lemma.lt_zero_false(a, ab)
    case 0n 1n+q:
      Lemma.false_is_not_true(ba)
    case 1n+p 1n+q:
      lt_ge_absurd(p, q, ab, ba)

# ---- Direction 1: before the best length, every length answered No ----

law down_case:
  for t: Guard.Tri
  for +m: Nat
  for +M: Nat
  for +L: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +tEq: {Ext.lengthOk(w, d, i, 1n+m, e) == t : Guard.Tri}
  for +found: {Ext.bestOn(t, w, d, i, 1n+m, e, Ext.firstLength(Ext.downFrom(m), w, d, i, e)) == Ext.Found{M} : Ext.Best}
  for +lt: {Nat.is_lt(M, L) == True{} : Bool}
  for +le: {Nat.is_le(L, 1n+m) == True{} : Bool}
  for lEq: Either<{Nat.is_eq(L, 1n+m) == True{} : Bool}, {Nat.is_eq(L, 1n+m) == False{} : Bool}>
  for later: {Ext.firstLength(Ext.downFrom(m), w, d, i, e) == Ext.Found{M} : Ext.Best} -> {Nat.is_le(L, m) == True{} : Bool} -> {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}
  {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}

def down_case(t, m, M, L, w, d, i, e, tEq, found, lt, le, lEq, later):
  match t:
    case Guard.Yes{}:
      +mEq = found_if_eq(Ext.certified(w, d, i, 1n+m, e), 1n+m, M, found)
      +lt2 = Equal.trans(Bool, Nat.is_lt(1n+m, L), Nat.is_lt(M, L), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, L), 1n+m, M, mEq), lt)
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, lt_ge_absurd(1n+m, L, lt2, le))
    case Guard.Unknown{}:
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, not_found_unsure(M, found))
    case Guard.No{}:
      match lEq:
        case Inl{e1}:
          Equal.trans(Guard.Tri, Ext.lengthOk(w, d, i, L, e), Ext.lengthOk(w, d, i, 1n+m, e), Guard.No{}, Equal.cong(Nat, Guard.Tri, v => Ext.lengthOk(w, d, i, v, e), L, 1n+m, Lemma.nat_eq_sound(L, 1n+m, e1)), tEq)
        case Inr{e2}:
          later(found, le_pred_ne(L, m, le, e2))

law down_no:
  for n: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +M: Nat
  for +L: Nat
  for +found: {Ext.firstLength(Ext.downFrom(n), w, d, i, e) == Ext.Found{M} : Ext.Best}
  for +lt: {Nat.is_lt(M, L) == True{} : Bool}
  for +le: {Nat.is_le(L, n) == True{} : Bool}
  {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}

def down_no(n, w, d, i, e, M, L, found, lt, le):
  match n:
    case 0n:
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, Lemma.lt_zero_false(M, lt_le_trans(M, L, 0n, lt, le)))
    case 1n+(+m):
      down_case(Ext.lengthOk(w, d, i, 1n+m, e), m, M, L, w, d, i, e, {==}, found, lt, le, nat_eq_cases(L, 1n+m),
        f2 => le2 => down_no(m, w, d, i, e, M, L, f2, lt, le2))

law up_case:
  for t: Guard.Tri
  for +m: Nat
  for +from: Nat
  for +M: Nat
  for +L: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +tEq: {Ext.lengthOk(w, d, i, from, e) == t : Guard.Tri}
  for +found: {Ext.bestOn(t, w, d, i, from, e, Ext.firstLength(Ext.upTo(m, 1n+from), w, d, i, e)) == Ext.Found{M} : Ext.Best}
  for +ge: {Nat.is_le(from, L) == True{} : Bool}
  for +lt: {Nat.is_lt(L, M) == True{} : Bool}
  for lEq: Either<{Nat.is_eq(L, from) == True{} : Bool}, {Nat.is_eq(L, from) == False{} : Bool}>
  for later: {Ext.firstLength(Ext.upTo(m, 1n+from), w, d, i, e) == Ext.Found{M} : Ext.Best} -> {Nat.is_le(1n+from, L) == True{} : Bool} -> {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}
  {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}

def up_case(t, m, from, M, L, w, d, i, e, tEq, found, ge, lt, lEq, later):
  match t:
    case Guard.Yes{}:
      +mEq = found_if_eq(Ext.certified(w, d, i, from, e), from, M, found)
      +lt2 = Equal.trans(Bool, Nat.is_lt(L, from), Nat.is_lt(L, M), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(L, v), from, M, mEq), lt)
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, lt_ge_absurd(L, from, lt2, ge))
    case Guard.Unknown{}:
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, not_found_unsure(M, found))
    case Guard.No{}:
      match lEq:
        case Inl{e1}:
          Equal.trans(Guard.Tri, Ext.lengthOk(w, d, i, L, e), Ext.lengthOk(w, d, i, from, e), Guard.No{}, Equal.cong(Nat, Guard.Tri, v => Ext.lengthOk(w, d, i, v, e), L, from, Lemma.nat_eq_sound(L, from, e1)), tEq)
        case Inr{e2}:
          later(found, Lemma.le_succ_ne(from, L, ge, e2))

law up_last:
  for t: Guard.Tri
  for +from: Nat
  for +M: Nat
  for +L: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +found: {Ext.bestOn(t, w, d, i, from, e, Ext.NoneFound{}) == Ext.Found{M} : Ext.Best}
  for +ge: {Nat.is_le(from, L) == True{} : Bool}
  for +lt: {Nat.is_lt(L, M) == True{} : Bool}
  {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}

def up_last(t, from, M, L, w, d, i, e, found, ge, lt):
  match t:
    case Guard.Yes{}:
      +mEq = found_if_eq(Ext.certified(w, d, i, from, e), from, M, found)
      +lt2 = Equal.trans(Bool, Nat.is_lt(L, from), Nat.is_lt(L, M), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(L, v), from, M, mEq), lt)
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, lt_ge_absurd(L, from, lt2, ge))
    case Guard.No{}:
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, not_found_none(M, found))
    case Guard.Unknown{}:
      Empty.absurd({Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}, not_found_unsure(M, found))

law up_no:
  for n: Nat
  for +from: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +M: Nat
  for +L: Nat
  for +found: {Ext.firstLength(Ext.upTo(n, from), w, d, i, e) == Ext.Found{M} : Ext.Best}
  for +ge: {Nat.is_le(from, L) == True{} : Bool}
  for +lt: {Nat.is_lt(L, M) == True{} : Bool}
  {Ext.lengthOk(w, d, i, L, e) == Guard.No{} : Guard.Tri}

def up_no(n, from, w, d, i, e, M, L, found, ge, lt):
  match n:
    case 0n:
      up_last(Ext.lengthOk(w, d, i, from, e), from, M, L, w, d, i, e, found, ge, lt)
    case 1n+(+m):
      up_case(Ext.lengthOk(w, d, i, from, e), m, from, M, L, w, d, i, e, {==}, found, ge, lt, nat_eq_cases(L, from),
        f2 => ge2 => up_no(m, 1n+from, w, d, i, e, M, L, f2, ge2, lt))

# ---- Direction 2: the tree's length is the one found (or the search is unsure) ----

law le_zero_eq:
  for a: Nat
  for le: {Nat.is_le(a, 0n) == True{} : Bool}
  {a == 0n : Nat}

def le_zero_eq(a, le):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, Lemma.false_is_not_true(le))

law found_at:
  for t: Guard.Tri
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +n: Nat
  for +rest: Ext.Best
  for +Lt: Nat
  for +nEq: {n == Lt : Nat}
  for +lenN: Guard.Tri
  for +tEq: {lenN == t : Guard.Tri}
  for notNo: {lenN == Guard.No{} : Guard.Tri} -> Empty
  {foundOr(Ext.bestOn(t, w, d, i, n, e, rest), Lt) == True{} : Bool}

def found_at(t, w, d, i, e, n, rest, Lt, nEq, lenN, tEq, notNo):
  match t:
    case Guard.Yes{}:
      found_if_or(Ext.certified(w, d, i, n, e), n, Lt, nEq)
    case Guard.No{}:
      Empty.absurd({foundOr(rest, Lt) == True{} : Bool}, notNo(tEq))
    case Guard.Unknown{}:
      {==}

law found_pick:
  for +b: Bool
  for +goal: Bool
  for cases: Either<{b == True{} : Bool}, {b == False{} : Bool}>
  for yes: {b == True{} : Bool} -> {goal == True{} : Bool}
  for no: {b == False{} : Bool} -> {goal == True{} : Bool}
  {goal == True{} : Bool}

def found_pick(b, goal, cases, yes, no):
  match cases:
    case Inl{e1}:
      yes(e1)
    case Inr{e2}:
      no(e2)

law hit_at:
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +n: Nat
  for +rest: Ext.Best
  for +lEq: {Lt == n : Nat}
  for notNo: {Ext.lengthOk(w, d, i, Lt, e) == Guard.No{} : Guard.Tri} -> Empty
  {foundOr(Ext.bestOn(Ext.lengthOk(w, d, i, n, e), w, d, i, n, e, rest), Lt) == True{} : Bool}

def hit_at(w, d, i, e, Lt, n, rest, lEq, notNo):
  +lenT = Ext.lengthOk(w, d, i, n, e)
  found_at(lenT, w, d, i, e, n, rest, Lt, Equal.sym(Nat, Lt, n, lEq), lenT, {==},
    e0 => notNo(Equal.trans(Guard.Tri, Ext.lengthOk(w, d, i, Lt, e), lenT, Guard.No{}, Equal.cong(Nat, Guard.Tri, v => Ext.lengthOk(w, d, i, v, e), Lt, n, lEq), e0)))

def NotNo(+w: Ext.Seq, +d: Nat, +i: Nat, +e: Nat, +Lt: Nat) -> Type:
  {Ext.lengthOk(w, d, i, Lt, e) == Guard.No{} : Guard.Tri} -> Empty

def BetterDown(+w: Ext.Seq, +d: Nat, +i: Nat, +e: Nat, +Lt: Nat) -> Type:
  @L: Nat -> {Nat.is_lt(Lt, L) == True{} : Bool} -> {Ext.lengthOk(w, d, i, L, e) == Guard.Yes{} : Guard.Tri} -> {Ext.certified(w, d, i, L, e) == True{} : Bool} -> Empty

# A Yes at a better length gives a certificate, which the caller rules out.
law skip_cert:
  for c: Bool
  for +n: Nat
  for +Lt: Nat
  for k: {c == True{} : Bool} -> Empty
  {foundOr(Ext.foundIf(c, n), Lt) == True{} : Bool}

def skip_cert(c, n, Lt, k):
  match c:
    case True{}:
      Empty.absurd({foundOr(Ext.Found{n}, Lt) == True{} : Bool}, k({==}))
    case False{}:
      {==}

law down_skip:
  for t: Guard.Tri
  for +m: Nat
  for +rest: Ext.Best
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +tEq: {Ext.lengthOk(w, d, i, 1n+m, e) == t : Guard.Tri}
  for +lt: {Nat.is_lt(Lt, 1n+m) == True{} : Bool}
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterDown(w, d, i, e, Lt)
  for cont: NotNo(w, d, i, e, Lt) -> BetterDown(w, d, i, e, Lt) -> {foundOr(rest, Lt) == True{} : Bool}
  {foundOr(Ext.bestOn(t, w, d, i, 1n+m, e, rest), Lt) == True{} : Bool}

def down_skip(t, m, rest, w, d, i, e, Lt, tEq, lt, notNo, better, cont):
  match t:
    case Guard.Yes{}:
      skip_cert(Ext.certified(w, d, i, 1n+m, e), 1n+m, Lt, ce => better(1n+m, lt, tEq, ce))
    case Guard.No{}:
      cont(notNo, better)
    case Guard.Unknown{}:
      {==}

law down_split:
  for +m: Nat
  for +rest: Ext.Best
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +le: {Nat.is_le(Lt, 1n+m) == True{} : Bool}
  for cases: Either<{Nat.is_eq(Lt, 1n+m) == True{} : Bool}, {Nat.is_eq(Lt, 1n+m) == False{} : Bool}>
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterDown(w, d, i, e, Lt)
  for cont: {Nat.is_le(Lt, m) == True{} : Bool} -> NotNo(w, d, i, e, Lt) -> BetterDown(w, d, i, e, Lt) -> {foundOr(rest, Lt) == True{} : Bool}
  {foundOr(Ext.bestOn(Ext.lengthOk(w, d, i, 1n+m, e), w, d, i, 1n+m, e, rest), Lt) == True{} : Bool}

def down_split(m, rest, w, d, i, e, Lt, le, cases, notNo, better, cont):
  match cases:
    case Inl{e1}:
      hit_at(w, d, i, e, Lt, 1n+m, rest, Lemma.nat_eq_sound(Lt, 1n+m, e1), notNo)
    case Inr{e20}:
      +e2 = {e20 : {Nat.is_eq(Lt, 1n+m) == False{} : Bool}}
      +le2 = le_pred_ne(Lt, m, le, e2)
      down_skip(Ext.lengthOk(w, d, i, 1n+m, e), m, rest, w, d, i, e, Lt, {==}, Lemma.lt_of_succ_le(Lt, 1n+m, le2), notNo, better, cont(le2))

law down_found:
  for n: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +le: {Nat.is_le(Lt, n) == True{} : Bool}
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterDown(w, d, i, e, Lt)
  {foundOr(Ext.firstLength(Ext.downFrom(n), w, d, i, e), Lt) == True{} : Bool}

def down_found(n, w, d, i, e, Lt, le, notNo, better):
  match n:
    case 0n:
      +z = le_zero_eq(Lt, le)
      hit_at(w, d, i, e, Lt, 0n, Ext.NoneFound{}, z, notNo)
    case 1n+(+m):
      down_split(m, Ext.firstLength(Ext.downFrom(m), w, d, i, e), w, d, i, e, Lt, le, nat_eq_cases(Lt, 1n+m), notNo, better,
        le2 => nn => bb => down_found(m, w, d, i, e, Lt, le2, nn, bb))

def BetterUp(+w: Ext.Seq, +d: Nat, +i: Nat, +e: Nat, +Lt: Nat) -> Type:
  @L: Nat -> {Nat.is_lt(L, Lt) == True{} : Bool} -> {Ext.lengthOk(w, d, i, L, e) == Guard.Yes{} : Guard.Tri} -> {Ext.certified(w, d, i, L, e) == True{} : Bool} -> Empty

law up_skip:
  for t: Guard.Tri
  for +from: Nat
  for +rest: Ext.Best
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +tEq: {Ext.lengthOk(w, d, i, from, e) == t : Guard.Tri}
  for +lt: {Nat.is_lt(from, Lt) == True{} : Bool}
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterUp(w, d, i, e, Lt)
  for cont: NotNo(w, d, i, e, Lt) -> BetterUp(w, d, i, e, Lt) -> {foundOr(rest, Lt) == True{} : Bool}
  {foundOr(Ext.bestOn(t, w, d, i, from, e, rest), Lt) == True{} : Bool}

def up_skip(t, from, rest, w, d, i, e, Lt, tEq, lt, notNo, better, cont):
  match t:
    case Guard.Yes{}:
      skip_cert(Ext.certified(w, d, i, from, e), from, Lt, ce => better(from, lt, tEq, ce))
    case Guard.No{}:
      cont(notNo, better)
    case Guard.Unknown{}:
      {==}

law up_split:
  for +m: Nat
  for +from: Nat
  for +rest: Ext.Best
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +ge: {Nat.is_le(from, Lt) == True{} : Bool}
  for cases: Either<{Nat.is_eq(Lt, from) == True{} : Bool}, {Nat.is_eq(Lt, from) == False{} : Bool}>
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterUp(w, d, i, e, Lt)
  for cont: {Nat.is_le(1n+from, Lt) == True{} : Bool} -> NotNo(w, d, i, e, Lt) -> BetterUp(w, d, i, e, Lt) -> {foundOr(rest, Lt) == True{} : Bool}
  {foundOr(Ext.bestOn(Ext.lengthOk(w, d, i, from, e), w, d, i, from, e, rest), Lt) == True{} : Bool}

def up_split(m, from, rest, w, d, i, e, Lt, ge, cases, notNo, better, cont):
  match cases:
    case Inl{e1}:
      hit_at(w, d, i, e, Lt, from, rest, Lemma.nat_eq_sound(Lt, from, e1), notNo)
    case Inr{e20}:
      +e2 = {e20 : {Nat.is_eq(Lt, from) == False{} : Bool}}
      +ge2 = Lemma.le_succ_ne(from, Lt, ge, e2)
      up_skip(Ext.lengthOk(w, d, i, from, e), from, rest, w, d, i, e, Lt, {==}, Lemma.lt_of_succ_le(from, Lt, ge2), notNo, better, cont(ge2))

law le_antisym:
  for a: Nat
  for b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, Lemma.false_is_not_true(ba))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Lemma.false_is_not_true(ab))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, v => 1n+v, p, q, le_antisym(p, q, ab, ba))

law up_found:
  for n: Nat
  for +from: Nat
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lt: Nat
  for +ge: {Nat.is_le(from, Lt) == True{} : Bool}
  for +le: {Nat.is_le(Lt, Nat.add(from, n)) == True{} : Bool}
  for notNo: NotNo(w, d, i, e, Lt)
  for better: BetterUp(w, d, i, e, Lt)
  {foundOr(Ext.firstLength(Ext.upTo(n, from), w, d, i, e), Lt) == True{} : Bool}

def up_found(n, from, w, d, i, e, Lt, ge, le, notNo, better):
  match n:
    case 0n:
      +le0 = Equal.trans(Bool, Nat.is_le(Lt, from), Nat.is_le(Lt, Nat.add(from, 0n)), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(Lt, v), from, Nat.add(from, 0n), Equal.sym(Nat, Nat.add(from, 0n), from, Lemma.add_zero_right(from))), le)
      hit_at(w, d, i, e, Lt, from, Ext.NoneFound{}, le_antisym(Lt, from, le0, ge), notNo)
    case 1n+(+m):
      +le1 = Equal.trans(Bool, Nat.is_le(Lt, Nat.add(1n+from, m)), Nat.is_le(Lt, Nat.add(from, 1n+m)), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(Lt, v), Nat.add(1n+from, m), Nat.add(from, 1n+m), Equal.sym(Nat, Nat.add(from, 1n+m), 1n+Nat.add(from, m), Lemma.add_succ_right(from, m))), le)
      up_split(m, from, Ext.firstLength(Ext.upTo(m, 1n+from), w, d, i, e), w, d, i, e, Lt, ge, nat_eq_cases(Lt, from), notNo, better,
        ge2 => nn => bb => up_found(m, 1n+from, w, d, i, e, Lt, ge2, le1, nn, bb))

# ======== THE KEPT STEPS ========

law ekept_sub_pick:
  for b: Bool
  for +e: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Spec.bsrMember(y, rest) == True{} : Bool}
  {Spec.bsrMember(y, e <> rest) == True{} : Bool}

def ekept_sub_pick(b, e, rest, ks, y, m, searchRest):
  match b:
    case True{}:
      G.member_pick(y, e, ks, e <> rest, G.ebnf_member_cases(y, e, ks, m), R.bsr_member_head(e, rest), later => R.bsr_member_cons(y, e, rest, searchRest(later)))
    case False{}:
      R.bsr_member_cons(y, e, rest, searchRest(m))

# A kept step is a step of the set.
law ekept_sub:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Ext.extentKept(es, set0, fuel, grammar, marks, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def ekept_sub(es, fuel, grammar, marks, input, set0, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      ekept_sub_pick(Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), e, rest, Ext.extentKept(rest, set0, fuel, grammar, marks, input), y, m,
        later => ekept_sub(rest, fuel, grammar, marks, input, set0, y, later))

law ekept_keep_case:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for -ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, ks) == True{} : Bool}>
  for +isB: {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}
  {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}

def ekept_keep_case(fuel, grammar, marks, input, set0, e, ks, y, cases, isB, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Spec.Bsr, y, e, same) : {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, _)) == True{} : Bool}
      isB
    case Inr{later}:
      searchRest(later)

law ekept_keep_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for +isB: {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)) == b : Bool}
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, ks) == True{} : Bool} -> {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}
  {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}

def ekept_keep_pick(b, fuel, grammar, marks, input, set0, e, isB, ks, y, m, searchRest):
  match b:
    case True{}:
      ekept_keep_case(fuel, grammar, marks, input, set0, e, ks, y, G.ebnf_member_cases(y, e, ks, m), isB, searchRest)
    case False{}:
      searchRest(m)

# A kept step's verdict was Keep.
law ekept_keep:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Ext.extentKept(es, set0, fuel, grammar, marks, input)) == True{} : Bool}
  {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}

def ekept_keep(es, fuel, grammar, marks, input, set0, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      ekept_keep_pick(Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), fuel, grammar, marks, input, set0, e, {==}, Ext.extentKept(rest, set0, fuel, grammar, marks, input), y, m,
        later => ekept_keep(rest, fuel, grammar, marks, input, set0, y, later))

law ekept_of_pick:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for +isB: {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)) == b : Bool}
  for +rest: +List<Spec.Bsr>
  for +ks: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for cases: Either<{y == e : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +ok: {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}
  for searchRest: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Spec.bsrMember(y, ks) == True{} : Bool}
  {Spec.bsrMember(y, Prune.keepPick(b, e, ks)) == True{} : Bool}

def ekept_of_pick(b, fuel, grammar, marks, input, set0, e, isB, rest, ks, y, cases, ok, searchRest):
  match cases:
    case Inl{same0}:
      +same = {same0 : {y == e : Spec.Bsr}}
      +okE = Equal.trans(Bool, Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)), True{}, Equal.cong(Spec.Bsr, Bool, v => Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, v)), e, y, Equal.sym(Spec.Bsr, y, e, same)), ok)
      +isT = Equal.trans(Bool, b, Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), True{}, Equal.sym(Bool, Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), b, isB), okE)
      %Equal.sym(Spec.Bsr, y, e, same) : {Spec.bsrMember(_, Prune.keepPick(b, e, ks)) == True{} : Bool}
      R.keep_link_head(b, isT, e, ks)
    case Inr{later}:
      R.keep_link_later(b, e, ks, y, searchRest(later))

# A step of the set whose verdict was Keep is kept.
law ekept_of:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  for +ok: {Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}
  {Spec.bsrMember(y, Ext.extentKept(es, set0, fuel, grammar, marks, input)) == True{} : Bool}

def ekept_of(es, fuel, grammar, marks, input, set0, y, m, ok):
  match es:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, []) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+e, +rest}:
      ekept_of_pick(Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, e)), fuel, grammar, marks, input, set0, e, {==}, rest, Ext.extentKept(rest, set0, fuel, grammar, marks, input), y, G.ebnf_member_cases(y, e, rest, m), ok,
        later => ekept_of(rest, fuel, grammar, marks, input, set0, y, later, ok))

# A step of an answered set passed its check, and was decided.
law each_pick:
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +P: Bool
  for +Q: Bool
  for cases: Either<{y == x : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}>
  for +okX: {P == True{} : Bool}
  for same: {y == x : Spec.Bsr} -> {P == Q : Bool}
  for later: {Spec.bsrMember(y, rest) == True{} : Bool} -> {Q == True{} : Bool}
  {Q == True{} : Bool}

def each_pick(x, rest, y, P, Q, cases, okX, same, later):
  match cases:
    case Inl{e1}:
      Equal.trans(Bool, Q, P, True{}, Equal.sym(Bool, P, Q, same(e1)), okX)
    case Inr{e2}:
      later(e2)

law checked_of:
  for es: +List<Spec.Bsr>
  for +set0: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +ok: {Ext.allChecked(es, set0, fuel, grammar, marks, input) == True{} : Bool}
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  {Ext.checkStep(set0, fuel, grammar, marks, input, y) == True{} : Bool}

def checked_of(es, set0, fuel, grammar, marks, input, ok, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Ext.checkStep(set0, fuel, grammar, marks, input, y) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+x, +rest}:
      +okX = Lemma.and_true_left(Ext.checkStep(set0, fuel, grammar, marks, input, x), Ext.allChecked(rest, set0, fuel, grammar, marks, input), ok)
      +okR = Lemma.and_true_right_side(Ext.checkStep(set0, fuel, grammar, marks, input, x), Ext.allChecked(rest, set0, fuel, grammar, marks, input), ok)
      each_pick(x, rest, y, Ext.checkStep(set0, fuel, grammar, marks, input, x), Ext.checkStep(set0, fuel, grammar, marks, input, y), G.ebnf_member_cases(y, x, rest, m), okX,
        e1 => Equal.cong(Spec.Bsr, Bool, v => Ext.checkStep(set0, fuel, grammar, marks, input, v), x, y, Equal.sym(Spec.Bsr, y, x, e1)),
        later => checked_of(rest, set0, fuel, grammar, marks, input, okR, y, later))

law eknown_of:
  for es: +List<Spec.Bsr>
  for +set0: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +ok: {Ext.allKnown(es, set0, fuel, grammar, marks, input) == True{} : Bool}
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, es) == True{} : Bool}
  {Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}

def eknown_of(es, set0, fuel, grammar, marks, input, ok, y, m):
  match es:
    case Nil{}:
      Empty.absurd({Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+x, +rest}:
      +okX = Lemma.and_true_left(Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, x)), Ext.allKnown(rest, set0, fuel, grammar, marks, input), ok)
      +okR = Lemma.and_true_right_side(Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, x)), Ext.allKnown(rest, set0, fuel, grammar, marks, input), ok)
      each_pick(x, rest, y, Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, x)), Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, y)), G.ebnf_member_cases(y, x, rest, m), okX,
        e1 => Equal.cong(Spec.Bsr, Bool, v => Guard.isKnown(Ext.stepVerdict(set0, fuel, grammar, marks, input, v)), x, y, Equal.sym(Spec.Bsr, y, x, e1)),
        later => eknown_of(rest, set0, fuel, grammar, marks, input, okR, y, later))

# ======== WHERE THE OWN STEPS ARE ========

law end_of_add:
  for +t: Spec.Tree
  for +k: Nat
  {Sub.endOf(t, k) == Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))) : Nat}

def end_of_add(t, k):
  Sub.end_of_one(t, k)

# The own step of child pp, read from the step list.
law own_nth:
  for f: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +set: +List<Spec.Bsr>
  for pp: Nat
  for +all: {Spec.allIn(PG.ownSteps(f, index, prefix, dot, i, k), set) == True{} : Bool}
  for +has: {Nat.is_lt(pp, List.length(&2, Spec.Tree, f)) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, pp), i, startOf(f, pp, k), endAt(f, pp, k)), set) == True{} : Bool}

def own_nth(f, index, prefix, dot, i, k, set, pp, all, has):
  match f:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, pp), i, startOf([], pp, k), endAt([], pp, k)), set) == True{} : Bool}, Lemma.lt_zero_false(pp, has))
    case Con{+t, +ts}:
      match pp:
        case 0n:
          +e = Sub.endOf(t, k)
          +x = Spec.at(index, prefix, 1n+dot, i, k, e)
          +m = Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, e), set), all)
          +eq1 = Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))), set), 1n+Nat.add(dot, 0n), 1n+dot, Equal.cong(Nat, Nat, v => 1n+v, Nat.add(dot, 0n), dot, Lemma.add_zero_right(dot)))
          +eq2 = Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, v), set), Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), e, Equal.sym(Nat, e, Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))), end_of_add(t, k)))
          Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, 0n), i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))), set), Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))), set), True{}, eq1, Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))), set), Spec.bsrMember(x, set), True{}, eq2, m))
        case 1n+(+p):
          +e = Sub.endOf(t, k)
          +x = Spec.at(index, prefix, 1n+dot, i, k, e)
          +rest = Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, e), set), all)
          +r = own_nth(ts, index, prefix, 1n+dot, i, e, set, p, rest, has)
          +b = Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))
          +eB = end_of_add(t, k)
          +ix = Equal.cong(Nat, Nat, v => 1n+v, Nat.add(dot, 1n+p), 1n+Nat.add(dot, p), Lemma.add_succ_right(dot, p))
          +r2 = Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, 1n+p), i, startOf(ts, p, b), endAt(ts, p, b)), set), Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(1n+dot, p), i, startOf(ts, p, e), endAt(ts, p, e)), set), True{},
            Equal.trans(Bool, Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, 1n+p), i, startOf(ts, p, b), endAt(ts, p, b)), set), Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(1n+dot, p), i, startOf(ts, p, b), endAt(ts, p, b)), set), Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(1n+dot, p), i, startOf(ts, p, e), endAt(ts, p, e)), set),
              Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, v, i, startOf(ts, p, b), endAt(ts, p, b)), set), 1n+Nat.add(dot, 1n+p), 1n+Nat.add(1n+dot, p), ix),
              Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(1n+dot, p), i, startOf(ts, p, v), endAt(ts, p, v)), set), b, e, Equal.sym(Nat, e, b, eB))), r)
          r2

law end_last:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +k: Nat
  {endAt(t <> ts, List.length(&2, Spec.Tree, ts), k) == Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> ts))) : Nat}

def end_last(ts, t, k):
  match ts:
    case Nil{}:
      +lt = List.length(&2, Nat, Spec.leaves([t]))
      Equal.cong(Nat, Nat, v => Nat.add(k, v), lt, List.length(&2, Nat, Spec.leaves([t])), {==})
    case Con{+u, +us}:
      +lt = List.length(&2, Nat, Spec.leaves([t]))
      +b = Nat.add(k, lt)
      +r = end_last(us, u, b)
      +lus = List.length(&2, Nat, Spec.leaves(u <> us))
      +l1 = len_cons(t, u <> us)
      Equal.trans(Nat, endAt(u <> us, List.length(&2, Spec.Tree, us), b), Nat.add(b, lus), Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> u <> us))), r,
        Equal.trans(Nat, Nat.add(b, lus), Nat.add(k, Nat.add(lt, lus)), Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> u <> us))), Lemma.add_assoc(k, lt, lus), Equal.cong(Nat, Nat, v => Nat.add(k, v), Nat.add(lt, lus), List.length(&2, Nat, Spec.leaves(t <> u <> us)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(t <> u <> us)), Nat.add(lt, lus), l1))))

law span_len:
  for f: +List<Spec.Tree>
  for pp: Nat
  for +k: Nat
  {Nat.sub(endAt(f, pp, k), startOf(f, pp, k)) == lenAt(f, pp) : Nat}

def span_len(f, pp, k):
  match f:
    case Nil{}:
      match pp:
        case 0n:
          sub_self(k)
        case 1n+p:
          sub_self(k)
    case Con{+t, +ts}:
      match pp:
        case 0n:
          Lemma.sub_add_left(k, List.length(&2, Nat, Spec.leaves([t])))
        case 1n+(+p):
          span_len(ts, p, Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))))

law len_at_le:
  for f: +List<Spec.Tree>
  for n: Nat
  {Nat.is_le(lenAt(f, n), List.length(&2, Nat, Spec.leaves(f))) == True{} : Bool}

def len_at_le(f, n):
  match f:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+t, +ts}:
      match n:
        case 0n:
          +lt = List.length(&2, Nat, Spec.leaves([t]))
          +lts = List.length(&2, Nat, Spec.leaves(ts))
          Equal.trans(Bool, Nat.is_le(lt, List.length(&2, Nat, Spec.leaves(t <> ts))), Nat.is_le(lt, Nat.add(lt, lts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(lt, v), List.length(&2, Nat, Spec.leaves(t <> ts)), Nat.add(lt, lts), len_cons(t, ts)), Lemma.le_add_right(lt, lts))
        case 1n+(+p):
          +lt = List.length(&2, Nat, Spec.leaves([t]))
          +lts = List.length(&2, Nat, Spec.leaves(ts))
          Equal.trans(Bool, Nat.is_le(lenAt(ts, p), List.length(&2, Nat, Spec.leaves(t <> ts))), Nat.is_le(lenAt(ts, p), Nat.add(lt, lts)), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(lenAt(ts, p), v), List.length(&2, Nat, Spec.leaves(t <> ts)), Nat.add(lt, lts), len_cons(t, ts)), Lemma.le_trans(lenAt(ts, p), lts, Nat.add(lt, lts), len_at_le(ts, p), Lemma.le_add_left(lt, lts)))

# ======== WHAT THE ORACLE SAYS ABOUT A STEP OF A SEQUENCE ========

def Mk(+grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +index: Nat, +rpath: +List<Nat>) -> Ext.Marked:
  Ext.markedFrom(Gll.seqAt(grammar, index, rpath), marks, index, Gll.reverseOnto(rpath, []), 0n, Ext.NoMark{})

law verdict_decode:
  for +set0: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dd: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Ext.stepVerdict(set0, fuel, grammar, marks, input, Spec.at(index, prefix, dd, i, k, j)) == Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(set0, fuel, grammar, input, index, rpath), dd, i, k, j) : Guard.Tri}

def verdict_decode(set0, fuel, grammar, marks, input, index, rpath, prefix, pEq, dd, i, k, j):
  Equal.cong(+List<Nat>, Guard.Tri, v => Ext.verdictAt(v, set0, fuel, grammar, marks, input, index, i, k, j), Gll.reverseOnto(List.append(&2, Nat, prefix, [dd]), []), dd <> rpath, R.step_rev(rpath, prefix, dd, pEq))

law check_decode:
  for +set0: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +dd: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Ext.checkStep(set0, fuel, grammar, marks, input, Spec.at(index, prefix, dd, i, k, j)) == Ext.checkFor(Mk(grammar, marks, index, rpath), Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, Spec.at(index, prefix, dd, i, k, j))), Ext.seqOf(set0, fuel, grammar, input, index, rpath), dd, i, k, j) : Bool}

def check_decode(set0, fuel, grammar, marks, input, index, rpath, prefix, pEq, dd, i, k, j):
  +kept = Guard.isYes(Ext.stepVerdict(set0, fuel, grammar, marks, input, Spec.at(index, prefix, dd, i, k, j)))
  Equal.cong(+List<Nat>, Bool, v => Ext.checkAt(v, kept, set0, fuel, grammar, marks, input, index, i, k, j), Gll.reverseOnto(List.append(&2, Nat, prefix, [dd]), []), dd <> rpath, R.step_rev(rpath, prefix, dd, pEq))

# ---- Ends ----

law ends_head:
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +rest: +List<Spec.Bsr>
  {Prefer.natIn(e, Ext.endsOf(Spec.Bsr{Spec.Slot{index, endPath}, i, k, e} <> rest, index, endPath, i)) == True{} : Bool}

def ends_head(index, endPath, i, k, e, rest):
  +c = Lemma.and_true_intro(Nat.is_eq(index, index), Bool.and(Spec.pathEq(endPath, endPath), Nat.is_eq(i, i)), Lemma.nat_eq_refl(index), Lemma.and_true_intro(Spec.pathEq(endPath, endPath), Nat.is_eq(i, i), R.path_eq_refl(endPath), Lemma.nat_eq_refl(i)))
  +cond = Bool.and(Nat.is_eq(index, index), Bool.and(Spec.pathEq(endPath, endPath), Nat.is_eq(i, i)))
  %Equal.sym(Bool, cond, True{}, c) : {Prefer.natIn(e, Ext.consEnd(Ext.endIf(_, e), Ext.endsOf(rest, index, endPath, i))) == True{} : Bool}
  Lemma.or_true_left_intro(Nat.is_eq(e, e), Prefer.natIn(e, Ext.endsOf(rest, index, endPath, i)), Lemma.nat_eq_refl(e))

law ends_cons_found:
  for found: Maybe<&2, Nat>
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +e: Nat
  for +rest: +List<Spec.Bsr>
  for +h: {Prefer.natIn(e, Ext.endsOf(rest, index, endPath, i)) == True{} : Bool}
  {Prefer.natIn(e, Ext.consEnd(found, Ext.endsOf(rest, index, endPath, i))) == True{} : Bool}

def ends_cons_found(found, index, endPath, i, e, rest, h):
  match found:
    case Some{+j}:
      Lemma.or_true_right_intro(Nat.is_eq(e, j), Prefer.natIn(e, Ext.endsOf(rest, index, endPath, i)), h)
    case None{}:
      h

law ends_cons:
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +e: Nat
  for +y: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +h: {Prefer.natIn(e, Ext.endsOf(rest, index, endPath, i)) == True{} : Bool}
  {Prefer.natIn(e, Ext.endsOf(y <> rest, index, endPath, i)) == True{} : Bool}

def ends_cons(index, endPath, i, e, y, rest, h):
  ends_cons_found(Ext.endsHere(index, endPath, i, y), index, endPath, i, e, rest, h)

law ends_pick:
  for +x: Spec.Bsr
  for +y: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +e: Nat
  for cases: Either<{x == y : Spec.Bsr}, {Spec.bsrMember(x, rest) == True{} : Bool}>
  for headIn: {x == y : Spec.Bsr} -> {Prefer.natIn(e, Ext.endsOf(y <> rest, index, endPath, i)) == True{} : Bool}
  for later: {Spec.bsrMember(x, rest) == True{} : Bool} -> {Prefer.natIn(e, Ext.endsOf(rest, index, endPath, i)) == True{} : Bool}
  {Prefer.natIn(e, Ext.endsOf(y <> rest, index, endPath, i)) == True{} : Bool}

def ends_pick(x, y, rest, index, endPath, i, e, cases, headIn, later):
  match cases:
    case Inl{e1}:
      headIn(e1)
    case Inr{e2}:
      ends_cons(index, endPath, i, e, y, rest, later(e2))

law ends_at:
  for +x: Spec.Bsr
  for +y: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +xEq: {x == Spec.Bsr{Spec.Slot{index, endPath}, i, k, e} : Spec.Bsr}
  for +e1: {x == y : Spec.Bsr}
  {Prefer.natIn(e, Ext.endsOf(y <> rest, index, endPath, i)) == True{} : Bool}

def ends_at(x, y, rest, index, endPath, i, k, e, xEq, e1):
  %Equal.trans(Spec.Bsr, Spec.Bsr{Spec.Slot{index, endPath}, i, k, e}, x, y, Equal.sym(Spec.Bsr, x, Spec.Bsr{Spec.Slot{index, endPath}, i, k, e}, xEq), e1) : {Prefer.natIn(e, Ext.endsOf(_ <> rest, index, endPath, i)) == True{} : Bool}
  ends_head(index, endPath, i, k, e, rest)

# The end of a step of the set that ends the sequence is one of its ends.
law ends_in:
  for set: +List<Spec.Bsr>
  for +index: Nat
  for +endPath: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for m: {Spec.bsrMember(Spec.Bsr{Spec.Slot{index, endPath}, i, k, e}, set) == True{} : Bool}
  {Prefer.natIn(e, Ext.endsOf(set, index, endPath, i)) == True{} : Bool}

def ends_in(set, index, endPath, i, k, e, m):
  match set:
    case Nil{}:
      Empty.absurd({Prefer.natIn(e, []) == True{} : Bool}, G.ebnf_not_in_empty(Spec.Bsr{Spec.Slot{index, endPath}, i, k, e}, m))
    case Con{+y, +rest}:
      +x = {Spec.Bsr{Spec.Slot{index, endPath}, i, k, e} : Spec.Bsr}
      ends_pick(x, y, rest, index, endPath, i, e, G.ebnf_member_cases(x, y, rest, m),
        e1 => ends_at(x, y, rest, index, endPath, i, k, e, {==}, e1),
        later => ends_in(rest, index, endPath, i, k, e, later))

law nat_in_pick:
  for +e: Nat
  for +x: Nat
  for +rest: +List<Nat>
  for cases: Either<{Nat.is_eq(e, x) == True{} : Bool}, {Prefer.natIn(e, rest) == True{} : Bool}>
  for P: Bool
  for here: {e == x : Nat} -> {P == True{} : Bool}
  for later: {Prefer.natIn(e, rest) == True{} : Bool} -> {P == True{} : Bool}
  {P == True{} : Bool}

def nat_in_pick(e, x, rest, cases, P, here, later):
  match cases:
    case Inl{e1}:
      here(Lemma.nat_eq_sound(e, x, e1))
    case Inr{e2}:
      later(e2)

law ends_ok_at:
  for es: +List<Nat>
  for +ext: Spec.Extent
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +ok: {Ext.endsOk(es, ext, w, d, i, k, j) == True{} : Bool}
  for +e: Nat
  for inE: {Prefer.natIn(e, es) == True{} : Bool}
  {Ext.endOk(ext, w, d, i, k, j, e) == True{} : Bool}

def ends_ok_at(es, ext, w, d, i, k, j, ok, e, inE):
  match es:
    case Nil{}:
      Empty.absurd({Ext.endOk(ext, w, d, i, k, j, e) == True{} : Bool}, Lemma.false_is_not_true(inE))
    case Con{+x, +rest}:
      +okX = Lemma.and_true_left(Ext.endOk(ext, w, d, i, k, j, x), Ext.endsOk(rest, ext, w, d, i, k, j), ok)
      +okR = Lemma.and_true_right_side(Ext.endOk(ext, w, d, i, k, j, x), Ext.endsOk(rest, ext, w, d, i, k, j), ok)
      nat_in_pick(e, x, rest, Lemma.or_true_cases(Nat.is_eq(e, x), Prefer.natIn(e, rest), inE), Ext.endOk(ext, w, d, i, k, j, e),
        ex => Equal.trans(Bool, Ext.endOk(ext, w, d, i, k, j, e), Ext.endOk(ext, w, d, i, k, j, x), True{}, Equal.cong(Nat, Bool, v => Ext.endOk(ext, w, d, i, k, j, v), e, x, ex), okX),
        later => ends_ok_at(rest, ext, w, d, i, k, j, okR, e, later))

law tri_pick:
  for +e: Nat
  for +x: Nat
  for +rest: +List<Nat>
  for cases: Either<{Nat.is_eq(e, x) == True{} : Bool}, {Prefer.natIn(e, rest) == True{} : Bool}>
  for +P: Guard.Tri
  for here: {e == x : Nat} -> {P == Guard.No{} : Guard.Tri}
  for later: {Prefer.natIn(e, rest) == True{} : Bool} -> {P == Guard.No{} : Guard.Tri}
  {P == Guard.No{} : Guard.Tri}

def tri_pick(e, x, rest, cases, P, here, later):
  match cases:
    case Inl{e1}:
      here(Lemma.nat_eq_sound(e, x, e1))
    case Inr{e2}:
      later(e2)

law some_best_at:
  for es: +List<Nat>
  for +ext: Spec.Extent
  for +w: Ext.Seq
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +no: {Ext.onSomeBest(es, ext, w, p, d, i, k, j) == Guard.No{} : Guard.Tri}
  for +e: Nat
  for inE: {Prefer.natIn(e, es) == True{} : Bool}
  {Ext.onBest(Ext.bestLength(ext, w, d, i, e), w, p, d, i, k, j, e) == Guard.No{} : Guard.Tri}

def some_best_at(es, ext, w, p, d, i, k, j, no, e, inE):
  match es:
    case Nil{}:
      Empty.absurd({Ext.onBest(Ext.bestLength(ext, w, d, i, e), w, p, d, i, k, j, e) == Guard.No{} : Guard.Tri}, Lemma.false_is_not_true(inE))
    case Con{+x, +rest}:
      +hx = Ext.onBest(Ext.bestLength(ext, w, d, i, x), w, p, d, i, k, j, x)
      +hr = Ext.onSomeBest(rest, ext, w, p, d, i, k, j)
      +noX = PG.or_no_l(hx, hr, no)
      +noR = PG.or_no_r(hx, hr, no)
      tri_pick(e, x, rest, Lemma.or_true_cases(Nat.is_eq(e, x), Prefer.natIn(e, rest), inE), Ext.onBest(Ext.bestLength(ext, w, d, i, e), w, p, d, i, k, j, e),
        ex => Equal.trans(Guard.Tri, Ext.onBest(Ext.bestLength(ext, w, d, i, e), w, p, d, i, k, j, e), hx, Guard.No{}, Equal.cong(Nat, Guard.Tri, v => Ext.onBest(Ext.bestLength(ext, w, d, i, v), w, p, d, i, k, j, v), e, x, ex), noX),
        later => some_best_at(rest, ext, w, p, d, i, k, j, noR, e, later))

law found_is_eq:
  for b: Ext.Best
  for +len: Nat
  for e: {Ext.foundIs(b, len) == True{} : Bool}
  {b == Ext.Found{len} : Ext.Best}

def found_is_eq(b, len, e):
  match b:
    case Ext.Found{+x}:
      Equal.cong(Nat, Ext.Best, v => Ext.Found{v}, x, len, Lemma.nat_eq_sound(x, len, e))
    case Ext.NoneFound{}:
      Empty.absurd({Ext.NoneFound{} == Ext.Found{len} : Ext.Best}, Lemma.false_is_not_true(e))
    case Ext.Unsure{}:
      Empty.absurd({Ext.Unsure{} == Ext.Found{len} : Ext.Best}, Lemma.false_is_not_true(e))

law is_no_false:
  for t: Guard.Tri
  for notNo: {t == Guard.No{} : Guard.Tri} -> Empty
  {Ext.isNo(t) == False{} : Bool}

def is_no_false(t, notNo):
  match t:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({True{} == False{} : Bool}, notNo({==}))
    case Guard.Unknown{}:
      {==}

# ======== DIRECTION 1 AT A NODE: KEPT OWN STEPS, SO NO BETTER READING ========

# A better reading of the children of a node or pick, that phases 1 and 2 keep where they
# stand: the sequence's rules `own`, the tokens `after`, and `above`, `span`.
def Rival(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +index: Nat, +rpath: +List<Nat>, +own: +List<Spec.Guard>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +ch: +List<Spec.Tree>) -> Type:
  Spec.ExtentRival(grammar, guards, pmarks, marks, Gll.seqAt(grammar, index, rpath), own, index, Gll.reverseOnto(rpath, []), Spec.leaves(ch), after, above, span, ch)

# What the walk knows of such a reading: it can take the children's place in the tree,
# so its own steps are in the set (PROOF_PLUG.bend).
def RivalIn(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +index: Nat, +rpath: +List<Nat>, +own: +List<Spec.Guard>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +ch: +List<Spec.Tree>, +i: Nat, +s: +List<Spec.Bsr>) -> Type:
  @f2: +List<Spec.Tree> -> {Spec.fits(f2, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool} -> {Spec.leaves(f2) == Spec.leaves(ch) : +List<Nat>} ->
    Spec.AllHold(grammar, own, Gll.seqAt(grammar, index, rpath), f2, List.append(&2, Nat, Spec.leaves(ch), after)) -> Spec.Admissible(grammar, guards, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, after) -> Spec.Unbeaten(grammar, guards, pmarks, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, above, span, after) ->
    {Spec.allIn(PG.ownSteps(f2, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}

# Kept steps are steps of the set.
law all_ekept:
  for xs: +List<Spec.Bsr>
  for +es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set0: +List<Spec.Bsr>
  for +all: {Spec.allIn(xs, Ext.extentKept(es, set0, fuel, grammar, marks, input)) == True{} : Bool}
  {Spec.allIn(xs, es) == True{} : Bool}

def all_ekept(xs, es, fuel, grammar, marks, input, set0, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +K = Ext.extentKept(es, set0, fuel, grammar, marks, input)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      +mr = Lemma.and_true_right_side(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      %Equal.sym(Bool, Spec.bsrMember(x, es), True{}, ekept_sub(es, fuel, grammar, marks, input, set0, x, mx)) : {Bool.and(_, Spec.allIn(rest, es)) == True{} : Bool}
      %Equal.sym(Bool, Spec.allIn(rest, es), True{}, all_ekept(rest, es, fuel, grammar, marks, input, set0, mr)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# The rival's length is no longer reachable: lengthOk said No at it, yet it reads.
law rival_reads:
  for +s: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +f2: +List<Spec.Tree>
  for +fit2: {Spec.fits(f2, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +own2: {Spec.allIn(PG.ownSteps(f2, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +endEq2: {Nat.add(i, List.length(&2, Nat, Spec.leaves(f2))) == e : Nat}
  for +no: {Ext.lengthOk(Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, lenAt(f2, d), e) == Guard.No{} : Guard.Tri}
  Empty

def rival_reads(s, fuel, grammar, input, index, rpath, d, i, e, f2, fit2, own2, endEq2, no):
  +S = Gll.seqAt(grammar, index, rpath)
  +L2 = lenAt(f2, d)
  +lf = List.length(&2, Nat, Spec.leaves(f2))
  +subE = Equal.trans(Nat, Nat.sub(e, i), Nat.sub(Nat.add(i, lf), i), lf, Equal.cong(Nat, Nat, v => Nat.sub(v, i), e, Nat.add(i, lf), Equal.sym(Nat, Nat.add(i, lf), e, endEq2)), Lemma.sub_add_left(i, lf))
  +room = Equal.trans(Bool, Nat.is_lt(headLen(f2), 1n+Nat.sub(e, i)), Nat.is_lt(headLen(f2), 1n+lf), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(headLen(f2), 1n+v), Nat.sub(e, i), lf, subE), Lemma.lt_of_succ_le(headLen(f2), 1n+lf, head_le(f2)))
  +cons = cons_split(f2, 0n, i, d, L2, False{}, 0n, 0n, 0n, mark_own(f2, 0n, i, d), steps_none(f2, 0n, i, 0n, 0n, 0n))
  search_not_no(Ext.gasFor(S, i, e), S, f2, 1n+Nat.sub(e, i), s, index, Gll.reverseOnto(rpath, []), i, grammar, 0n, i, e, d, L2, False{}, 0n, 0n, 0n, fit2, own2, endEq2, cons, room, no)

# A better rival over (i, e) would read a length that the oracle found to be no reading.
law rival_ext:
  for ext: Spec.Extent
  for +w: Ext.Seq
  for +d: Nat
  for +i: Nat
  for +e: Nat
  for +Lc: Nat
  for +L2: Nat
  for +found: {Ext.bestLength(ext, w, d, i, e) == Ext.Found{Lc} : Ext.Best}
  for +bt: {Spec.better(ext, L2, Lc) == True{} : Bool}
  for +le: {Nat.is_le(L2, Nat.sub(e, i)) == True{} : Bool}
  {Ext.lengthOk(w, d, i, L2, e) == Guard.No{} : Guard.Tri}

def rival_ext(ext, w, d, i, e, Lc, L2, found, bt, le):
  match ext:
    case Spec.Longest{}:
      down_no(Nat.sub(e, i), w, d, i, e, Lc, L2, found, bt, le)
    case Spec.Shortest{}:
      up_no(Nat.sub(e, i), 0n, w, d, i, e, Lc, L2, found, Lemma.zero_le(L2), bt)

law check_on:
  for +d: Nat
  for +rest: Bool
  for +ok: {Bool.or(Bool.or(Bool.not(True{}), Bool.not(Nat.is_eq(1n+d, 1n+d))), rest) == True{} : Bool}
  {rest == True{} : Bool}

def check_on(d, rest, ok):
  +ex = Equal.cong(Bool, Bool, v => Bool.not(v), Nat.is_eq(d, d), True{}, Lemma.nat_eq_refl(d))
  Lemma.or_false_left(Bool.or(Bool.not(True{}), Bool.not(Nat.is_eq(1n+d, 1n+d))), rest, ex, ok)

law best_with_mo:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(t <> ts, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(t <> ts, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for mo: MeasOne(marks, t <> ts, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, d, ext)
  {Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(t <> ts)))) == Ext.Found{lenAt(t <> ts, d)} : Ext.Best}

def best_with_mo(fuel, grammar, marks, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, ext, mEq, mo):
  match mo:
    case (m0, (lt0, le0)):
      +S = Gll.seqAt(grammar, index, rpath)
      +P = Gll.reverseOnto(rpath, [])
      +ch = {t <> ts : +List<Spec.Tree>}
      +K = Ext.extentKept(s, s, fuel, grammar, marks, input)
      +L = List.length(&2, Nat, Spec.leaves(ch))
      +e = Nat.add(i, L)
      +ltD = Equal.trans(Bool, Nat.is_lt(d, List.length(&2, Spec.Tree, ch)), Nat.is_lt(Nat.sub(d, 0n), List.length(&2, Spec.Tree, ch)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, List.length(&2, Spec.Tree, ch)), d, Nat.sub(d, 0n), Equal.sym(Nat, Nat.sub(d, 0n), d, Lemma.sub_zero(d))), lt0)
      +kd = startOf(ch, d, i)
      +jd = endAt(ch, d, i)
      +xd = Spec.at(index, prefix, 1n+d, i, kd, jd)
      +memK = own_nth(ch, index, prefix, 0n, i, i, K, d, allK, ltD)
      +memS = ekept_sub(s, fuel, grammar, marks, input, s, xd, memK)
      +keptY = ekept_keep(s, fuel, grammar, marks, input, s, xd, memK)
      +chk = checked_of(s, s, fuel, grammar, marks, input, okC, xd, memS)
      +kv = Guard.isYes(Ext.stepVerdict(s, fuel, grammar, marks, input, xd))
      +ends = Ext.endsOf(s, index, List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), i)
      +chk2 = Equal.trans(Bool, Ext.checkFor(Mk(grammar, marks, index, rpath), kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), Ext.checkStep(s, fuel, grammar, marks, input, xd), True{}, Equal.sym(Bool, Ext.checkStep(s, fuel, grammar, marks, input, xd), Ext.checkFor(Mk(grammar, marks, index, rpath), kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), check_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, 1n+d, i, kd, jd)), chk)
      +chk3 = Equal.trans(Bool, Ext.checkFor(Ext.OneMark{d, ext}, True{}, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), Ext.checkFor(Mk(grammar, marks, index, rpath), kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), True{},
        Equal.trans(Bool, Ext.checkFor(Ext.OneMark{d, ext}, True{}, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), Ext.checkFor(Ext.OneMark{d, ext}, kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), Ext.checkFor(Mk(grammar, marks, index, rpath), kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd),
          Equal.cong(Bool, Bool, v => Ext.checkFor(Ext.OneMark{d, ext}, v, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), True{}, kv, Equal.sym(Bool, kv, True{}, keptY)),
          Equal.cong(Ext.Marked, Bool, v => Ext.checkFor(v, kv, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+d, i, kd, jd), Ext.OneMark{d, ext}, Mk(grammar, marks, index, rpath), Equal.sym(Ext.Marked, Mk(grammar, marks, index, rpath), Ext.OneMark{d, ext}, mEq))), chk2)
      +okEnds = check_on(d, Ext.endsOk(ends, ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, kd, jd), chk3)
      +nS = Fits.fits_count(ch, grammar, S, fit)
      +memL = own_nth(ch, index, prefix, 0n, i, i, K, List.length(&2, Spec.Tree, ts), allK, lt_self(List.length(&2, Spec.Tree, ts)))
      +kL = startOf(ch, List.length(&2, Spec.Tree, ts), i)
      +xl = Spec.at(index, prefix, 1n+List.length(&2, Spec.Tree, ts), i, kL, endAt(ch, List.length(&2, Spec.Tree, ts), i))
      +memLS = ekept_sub(s, fuel, grammar, marks, input, s, xl, memL)
      +endP = List.append(&2, Nat, prefix, [1n+List.length(&2, Spec.Tree, ts)])
      +memLS2 = Equal.trans(Bool, Spec.bsrMember(Spec.Bsr{Spec.Slot{index, endP}, i, kL, e}, s), Spec.bsrMember(xl, s), True{}, Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.Bsr{Spec.Slot{index, endP}, i, kL, v}, s), e, endAt(ch, List.length(&2, Spec.Tree, ts), i), Equal.sym(Nat, endAt(ch, List.length(&2, Spec.Tree, ts), i), e, end_last(ts, t, i))), memLS)
      +inE0 = ends_in(s, index, endP, i, kL, e, memLS2)
      +pathEq = Equal.trans(+List<Nat>, endP, List.append(&2, Nat, P, [1n+List.length(&2, Spec.Tree, ts)]), List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [1n+List.length(&2, Spec.Tree, ts)]), prefix, P, pEq), Equal.cong(Nat, +List<Nat>, v => List.append(&2, Nat, P, [v]), 1n+List.length(&2, Spec.Tree, ts), List.length(&2, Spec.Item, S), nS))
      +inE = Equal.trans(Bool, Prefer.natIn(e, ends), Prefer.natIn(e, Ext.endsOf(s, index, endP, i)), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.natIn(e, Ext.endsOf(s, index, v, i)), List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), endP, Equal.sym(+List<Nat>, endP, List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), pathEq)), inE0)
      +eOk = ends_ok_at(ends, ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, kd, jd, okEnds, e, inE)
      +sp = span_len(ch, d, i)
      +lenD = Nat.sub(jd, kd)
      +mk0 = mark_own(ch, 0n, i, d)
      +mk = Equal.trans(Bool, markOk(ch, 0n, i, d, lenD), markOk(ch, 0n, i, d, lenAt(ch, d)), True{}, Equal.cong(Nat, Bool, v => markOk(ch, 0n, i, d, v), lenD, lenAt(ch, d), sp), mk0)
      +cons = cons_split(ch, 0n, i, d, lenD, True{}, d, kd, jd, mk, steps_own(ch, 0n, i, d))
      +subE = Lemma.sub_add_left(i, L)
      +room = Equal.trans(Bool, Nat.is_lt(headLen(ch), 1n+Nat.sub(e, i)), Nat.is_lt(headLen(ch), 1n+L), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(headLen(ch), 1n+v), Nat.sub(e, i), L, subE), Lemma.lt_of_succ_le(headLen(ch), 1n+L, head_le(ch)))
      +srch = Ext.readsWith(Ext.seqOf(s, fuel, grammar, input, index, rpath), d, lenD, True{}, d, kd, jd, i, e)
      +ownS0 = all_ekept(PG.ownSteps(ch, index, prefix, 0n, i, i), s, fuel, grammar, marks, input, s, allK)
      +ownS = Equal.trans(Bool, Spec.allIn(PG.ownSteps(ch, index, P, 0n, i, i), s), Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(PG.ownSteps(ch, index, v, 0n, i, i), s), P, prefix, Equal.sym(+List<Nat>, prefix, P, pEq)), ownS0)
      +isNoF = is_no_false(srch, no => search_not_no(Ext.gasFor(S, i, e), S, ch, 1n+Nat.sub(e, i), s, index, P, i, grammar, 0n, i, e, d, lenD, True{}, d, kd, jd, fit, ownS, {==}, cons, room, no))
      +fnd = Lemma.or_false_left(Ext.isNo(srch), Ext.foundIs(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, e), lenD), isNoF, eOk)
      +fEq = found_is_eq(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, e), lenD, fnd)
      Equal.trans(Ext.Best, Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, e), Ext.Found{lenD}, Ext.Found{lenAt(ch, d)}, fEq, Equal.cong(Nat, Ext.Best, v => Ext.Found{v}, lenD, lenAt(ch, d), sp))

# The oracle's check, at the tree's marked child and the tree's own end: the best length
# there is the tree's.
law best_from_check:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(t <> ts, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(t <> ts, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  {Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(t <> ts)))) == Ext.Found{lenAt(t <> ts, d)} : Ext.Best}

def best_from_check(fuel, grammar, marks, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, ext, mEq):
  best_with_mo(fuel, grammar, marks, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, ext, mEq, measures_one(Gll.seqAt(grammar, index, rpath), t <> ts, marks, grammar, index, Gll.reverseOnto(rpath, []), 0n, d, ext, mEq, fit))

def isBad(m: Ext.Marked, l: Bool) -> Bool:
  match m l:
    case Ext.ManyMarks{} _:
      True{}
    case Ext.OneMark{d, e} True{}:
      True{}
    case Ext.OneMark{d, e} False{}:
      False{}
    case Ext.NoMark{} _:
      False{}

law bad_verdict:
  for m: Ext.Marked
  for l: Bool
  for +w: Ext.Seq
  for +dd: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +bad: {isBad(m, l) == True{} : Bool}
  for +yes: {Guard.isYes(Ext.verdictFor(m, l, w, dd, i, k, j)) == True{} : Bool}
  Empty

def bad_verdict(m, l, w, dd, i, k, j, bad, yes):
  match m l:
    case Ext.ManyMarks{} _:
      Lemma.false_is_not_true(yes)
    case Ext.OneMark{d, e} True{}:
      Lemma.false_is_not_true(yes)
    case Ext.OneMark{d, e} False{}:
      Lemma.false_is_not_true(bad)
    case Ext.NoMark{} _:
      Lemma.false_is_not_true(bad)

def FirstOwn(+index: Nat, +prefix: +List<Nat>, +i: Nat, +set: +List<Spec.Bsr>) -> Type:
  &dd: Nat -> &k: Nat -> &j: Nat -> {Spec.bsrMember(Spec.at(index, prefix, dd, i, k, j), set) == True{} : Bool}

law own_first:
  for ch: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +set: +List<Spec.Bsr>
  for +all: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), set) == True{} : Bool}
  FirstOwn(index, prefix, i, set)

def own_first(ch, index, prefix, i, set, all):
  match ch:
    case Nil{}:
      (0n, (i, (i, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 0n, i, i, i), set), True{}, all))))
    case Con{+t, +ts}:
      +e = Sub.endOf(t, i)
      (1n, (i, (e, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 1n, i, i, e), set), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n, i, e), set), all))))

# A bad mark (two marked items, or a mark on a loop's alternative) can't have kept steps.
law bad_kept:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +bad: {isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)) == True{} : Bool}
  for first: FirstOwn(index, prefix, i, Ext.extentKept(s, s, fuel, grammar, marks, input))
  Empty

def bad_kept(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, bad, first):
  match first:
    case (dd0, rest0):
      match rest0:
        case (k0, (j0, m0)):
          +dd = {dd0 : Nat}
          +k = {k0 : Nat}
          +j = {j0 : Nat}
          +x = Spec.at(index, prefix, dd, i, k, j)
          +y = ekept_keep(s, fuel, grammar, marks, input, s, x, m0)
          +y2 = Equal.trans(Bool, Guard.isYes(Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j)), Guard.isYes(Ext.stepVerdict(s, fuel, grammar, marks, input, x)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j), Ext.stepVerdict(s, fuel, grammar, marks, input, x), Equal.sym(Guard.Tri, Ext.stepVerdict(s, fuel, grammar, marks, input, x), Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j), verdict_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, dd, i, k, j))), y)
          bad_verdict(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j, bad, y2)

law Lemma_beats2:
  for +a: +List<Spec.Measure>
  for +a2: +List<Spec.Measure>
  for +b: +List<Spec.Measure>
  for +b2: +List<Spec.Measure>
  for +ea: {a == a2 : +List<Spec.Measure>}
  for +eb: {b == b2 : +List<Spec.Measure>}
  {Spec.beats(a, b) == Spec.beats(a2, b2) : Bool}

def Lemma_beats2(a, a2, b, b2, ea, eb):
  Equal.trans(Bool, Spec.beats(a, b), Spec.beats(a2, b), Spec.beats(a2, b2), Equal.cong(+List<Spec.Measure>, Bool, v => Spec.beats(v, b), a, a2, ea), Equal.cong(+List<Spec.Measure>, Bool, v => Spec.beats(a2, v), b, b2, eb))

law rival_with:
  for +s: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +d: Nat
  for +ext: Spec.Extent
  for +f2: +List<Spec.Tree>
  for +fit2: {Spec.fits(f2, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +lv2: {Spec.leaves(f2) == Spec.leaves(t <> ts) : +List<Nat>}
  for +own2: {Spec.allIn(PG.ownSteps(f2, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +bt: {Spec.beats(Spec.measures(marks, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n), Spec.measures(marks, t <> ts, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n)) == True{} : Bool}
  for +best: {Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(t <> ts)))) == Ext.Found{lenAt(t <> ts, d)} : Ext.Best}
  for mo2: MeasOne(marks, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, d, ext)
  for mo1: MeasOne(marks, t <> ts, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, d, ext)
  Empty

def rival_with(s, fuel, grammar, marks, input, index, rpath, t, ts, i, next, pos, d, ext, f2, fit2, lv2, own2, bt, best, mo2, mo1):
  match mo2:
    case (m20, rest2):
      match mo1:
        case (m10, rest1):
          +S = Gll.seqAt(grammar, index, rpath)
          +P = Gll.reverseOnto(rpath, [])
          +ch = {t <> ts : +List<Spec.Tree>}
          +L = List.length(&2, Nat, Spec.leaves(ch))
          +e = Nat.add(i, L)
          +s0 = Lemma.sub_zero(d)
          +L2 = lenAt(f2, d)
          +Lc = lenAt(ch, d)
          +m2 = Equal.trans(+List<Spec.Measure>, Spec.measures(marks, f2, S, index, P, 0n), [Spec.Measure{ext, lenAt(f2, Nat.sub(d, 0n))}], [Spec.Measure{ext, L2}], m20, Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{ext, lenAt(f2, v)}], Nat.sub(d, 0n), d, s0))
          +m1 = Equal.trans(+List<Spec.Measure>, Spec.measures(marks, ch, S, index, P, 0n), [Spec.Measure{ext, lenAt(ch, Nat.sub(d, 0n))}], [Spec.Measure{ext, Lc}], m10, Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{ext, lenAt(ch, v)}], Nat.sub(d, 0n), d, s0))
          +bt2 = Equal.trans(Bool, Spec.beats([Spec.Measure{ext, L2}], [Spec.Measure{ext, Lc}]), Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), True{},
            Equal.sym(Bool, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), Spec.beats([Spec.Measure{ext, L2}], [Spec.Measure{ext, Lc}]), Lemma_beats2(Spec.measures(marks, f2, S, index, P, 0n), [Spec.Measure{ext, L2}], Spec.measures(marks, ch, S, index, P, 0n), [Spec.Measure{ext, Lc}], m2, m1)), bt)
          +bt3 = Equal.trans(Bool, Spec.better(ext, L2, Lc), Spec.beats([Spec.Measure{ext, L2}], [Spec.Measure{ext, Lc}]), True{}, Equal.sym(Bool, Spec.beats([Spec.Measure{ext, L2}], [Spec.Measure{ext, Lc}]), Spec.better(ext, L2, Lc), beats_one(ext, L2, Lc)), bt2)
          +lenEq = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(f2), Spec.leaves(ch), lv2)
          +subE = Lemma.sub_add_left(i, L)
          +le = Equal.trans(Bool, Nat.is_le(L2, Nat.sub(e, i)), Nat.is_le(L2, List.length(&2, Nat, Spec.leaves(f2))), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(L2, v), Nat.sub(e, i), List.length(&2, Nat, Spec.leaves(f2)), Equal.trans(Nat, Nat.sub(e, i), L, List.length(&2, Nat, Spec.leaves(f2)), subE, Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(f2)), L, lenEq))), len_at_le(f2, d))
          +noL2 = rival_ext(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, e, Lc, L2, best, bt3, le)
          +endEq2 = Equal.cong(Nat, Nat, v => Nat.add(i, v), List.length(&2, Nat, Spec.leaves(f2)), L, lenEq)
          rival_reads(s, fuel, grammar, input, index, rpath, d, i, e, f2, fit2, own2, endEq2, noL2)

# One marked item, and not in a loop: no better rival.
law no_rival_one:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(t <> ts), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(t <> ts, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(t <> ts, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for plugIn: RivalIn(grammar, guards, pmarks, index, rpath, own, after, above, span, t <> ts, i, s)
  for r: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, t <> ts)
  Empty

def no_rival_one(fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, ext, mEq, plugIn, r):
  match r:
    case (f20, (fit20, (lv20, (bt0, (hold0, (adm0, unb0)))))):
      +S = Gll.seqAt(grammar, index, rpath)
      +P = Gll.reverseOnto(rpath, [])
      +ch = {t <> ts : +List<Spec.Tree>}
      +f2 = {f20 : +List<Spec.Tree>}
      +fit2 = {fit20 : {Spec.fits(f2, grammar, S) == True{} : Bool}}
      +lv2 = {lv20 : {Spec.leaves(f2) == Spec.leaves(ch) : +List<Nat>}}
      +bt = {bt0 : {Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)) == True{} : Bool}}
      +L = List.length(&2, Nat, Spec.leaves(ch))
      +e = Nat.add(i, L)
      +own2 = plugIn(f2, fit2, lv2, hold0, adm0, unb0)
      +best = best_from_check(fuel, grammar, marks, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, ext, mEq)
      mo2 = measures_one(S, f2, marks, grammar, index, P, 0n, d, ext, mEq, fit2)
      mo1 = measures_one(S, ch, marks, grammar, index, P, 0n, d, ext, mEq, fit)
      rival_with(s, fuel, grammar, marks, input, index, rpath, t, ts, i, next, pos, d, ext, f2, fit2, lv2, own2, bt, best, mo2, mo1)

law empty_one:
  for +marks: +List<Spec.ExtentMark>
  for +its: +List<Spec.Item>
  for +index: Nat
  for +prefix: +List<Nat>
  for +d: Nat
  for +e: Spec.Extent
  for mo: MeasOne(marks, [], its, index, prefix, 0n, d, e)
  Empty

def empty_one(marks, its, index, prefix, d, e, mo):
  match mo:
    case (a, (lt0, c)):
      Lemma.lt_zero_false(Nat.sub(d, 0n), lt0)

law rival_case:
  for m: Ext.Marked
  for l: Bool
  for +ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +badEq: {isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)) == isBad(m, l) : Bool}
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for plugIn: RivalIn(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for r: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)
  Empty

def rival_case(m, l, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, mEq, badEq, i, next, pos, fit, allK, plugIn, r):
  match m l ch:
    case Ext.NoMark{} _ _:
      match r:
        case (f20, (fit20, (lv20, (bt0, hr)))):
          +S = Gll.seqAt(grammar, index, rpath)
          +P = Gll.reverseOnto(rpath, [])
          +f2 = {f20 : +List<Spec.Tree>}
          +h = Equal.cong(Ext.Marked, Bool, v => isNoMark(v), Mk(grammar, marks, index, rpath), Ext.NoMark{}, mEq)
          +m2 = measures_nomark(S, f2, marks, index, P, 0n, h)
          +m1 = measures_nomark(S, ch, marks, index, P, 0n, h)
          Lemma.false_is_not_true(Equal.trans(Bool, False{}, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), True{}, Equal.sym(Bool, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), False{}, Lemma_beats2(Spec.measures(marks, f2, S, index, P, 0n), [], Spec.measures(marks, ch, S, index, P, 0n), [], m2, m1)), bt0))
    case Ext.ManyMarks{} _ _:
      bad_kept(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, badEq, own_first(ch, index, prefix, i, Ext.extentKept(s, s, fuel, grammar, marks, input), allK))
    case Ext.OneMark{+d, +e} True{} _:
      bad_kept(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, badEq, own_first(ch, index, prefix, i, Ext.extentKept(s, s, fuel, grammar, marks, input), allK))
    case Ext.OneMark{+d, +e} False{} Nil{}:
      empty_one(marks, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), d, e, measures_one(Gll.seqAt(grammar, index, rpath), [], marks, grammar, index, Gll.reverseOnto(rpath, []), 0n, d, e, mEq, fit))
    case Ext.OneMark{+d, +e} False{} Con{+t, +ts}:
      no_rival_one(fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, t, ts, i, next, pos, fit, allK, d, e, mEq, plugIn, r)

law rival_m:
  for m: Ext.Marked
  for l: Bool
  for +ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == l : Bool}
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for plugIn: RivalIn(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for r: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)
  Empty

def rival_m(m, l, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, mEq, lEq, i, next, pos, fit, allK, plugIn, r):
  +S = Gll.seqAt(grammar, index, rpath)
  +P = Gll.reverseOnto(rpath, [])
  +K = Ext.extentKept(s, s, fuel, grammar, marks, input)
  +badEq = Equal.trans(Bool, isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)), isBad(m, Ext.seqLoopy(rpath, grammar, index)), isBad(m, l), Equal.cong(Ext.Marked, Bool, v => isBad(v, Ext.seqLoopy(rpath, grammar, index)), Mk(grammar, marks, index, rpath), m, mEq), Equal.cong(Bool, Bool, v => isBad(m, v), Ext.seqLoopy(rpath, grammar, index), l, lEq))
  rival_case(m, l, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, mEq, badEq, i, next, pos, fit, allK, plugIn, r)

# Direction 1 at a node: its own steps are kept, so its children have no better reading.
law no_rival:
  for ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allK: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for plugIn: RivalIn(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty

def no_rival(ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, i, next, pos, fit, allK, plugIn):
  r => rival_m(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okC, index, rpath, prefix, pEq, {==}, {==}, i, next, pos, fit, allK, plugIn, r)

# ======== A SUFFIX OF THE CHILDREN ========

law start_zero:
  for f: +List<Spec.Tree>
  for +k0: Nat
  {startOf(f, 0n, k0) == k0 : Nat}

def start_zero(f, k0):
  match f:
    case Nil{}:
      {==}
    case Con{t, ts}:
      {==}

law start_app:
  for done: +List<Spec.Tree>
  for +f: +List<Spec.Tree>
  for +k0: Nat
  {startOf(List.append(&2, Spec.Tree, done, f), List.length(&2, Spec.Tree, done), k0) == Nat.add(k0, List.length(&2, Nat, Spec.leaves(done))) : Nat}

def start_app(done, f, k0):
  match done:
    case Nil{}:
      Equal.trans(Nat, startOf(f, 0n, k0), k0, Nat.add(k0, 0n), start_zero(f, k0), Equal.sym(Nat, Nat.add(k0, 0n), k0, Lemma.add_zero_right(k0)))
    case Con{+u, +us}:
      +lu = List.length(&2, Nat, Spec.leaves([u]))
      +r = start_app(us, f, Nat.add(k0, lu))
      Equal.trans(Nat, startOf(List.append(&2, Spec.Tree, us, f), List.length(&2, Spec.Tree, us), Nat.add(k0, lu)), Nat.add(Nat.add(k0, lu), List.length(&2, Nat, Spec.leaves(us))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(u <> us))), r,
        Equal.trans(Nat, Nat.add(Nat.add(k0, lu), List.length(&2, Nat, Spec.leaves(us))), Nat.add(k0, Nat.add(lu, List.length(&2, Nat, Spec.leaves(us)))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(u <> us))), Lemma.add_assoc(k0, lu, List.length(&2, Nat, Spec.leaves(us))), Equal.cong(Nat, Nat, v => Nat.add(k0, v), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves(u <> us)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(u <> us)), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), len_cons(u, us)))))

law end_app:
  for done: +List<Spec.Tree>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +k0: Nat
  {endAt(List.append(&2, Spec.Tree, done, t <> ts), List.length(&2, Spec.Tree, done), k0) == Nat.add(Nat.add(k0, List.length(&2, Nat, Spec.leaves(done))), List.length(&2, Nat, Spec.leaves([t]))) : Nat}

def end_app(done, t, ts, k0):
  match done:
    case Nil{}:
      Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves([t]))), k0, Nat.add(k0, 0n), Equal.sym(Nat, Nat.add(k0, 0n), k0, Lemma.add_zero_right(k0)))
    case Con{+u, +us}:
      +lu = List.length(&2, Nat, Spec.leaves([u]))
      +r = end_app(us, t, ts, Nat.add(k0, lu))
      +a = Equal.trans(Nat, Nat.add(Nat.add(k0, lu), List.length(&2, Nat, Spec.leaves(us))), Nat.add(k0, Nat.add(lu, List.length(&2, Nat, Spec.leaves(us)))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(u <> us))), Lemma.add_assoc(k0, lu, List.length(&2, Nat, Spec.leaves(us))), Equal.cong(Nat, Nat, v => Nat.add(k0, v), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves(u <> us)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(u <> us)), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), len_cons(u, us))))
      Equal.trans(Nat, endAt(List.append(&2, Spec.Tree, us, t <> ts), List.length(&2, Spec.Tree, us), Nat.add(k0, lu)), Nat.add(Nat.add(Nat.add(k0, lu), List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves([t]))), Nat.add(Nat.add(k0, List.length(&2, Nat, Spec.leaves(u <> us))), List.length(&2, Nat, Spec.leaves([t]))), r,
        Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves([t]))), Nat.add(Nat.add(k0, lu), List.length(&2, Nat, Spec.leaves(us))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(u <> us))), a))

law tree_app_one:
  for done: +List<Spec.Tree>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, done, [t]), ts) == List.append(&2, Spec.Tree, done, t <> ts) : +List<Spec.Tree>}

def tree_app_one(done, t, ts):
  match done:
    case Nil{}:
      {==}
    case Con{+u, +us}:
      Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => u <> v, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, us, [t]), ts), List.append(&2, Spec.Tree, us, t <> ts), tree_app_one(us, t, ts))

law len_app_one:
  for done: +List<Spec.Tree>
  for +t: Spec.Tree
  {List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, done, [t])) == 1n+List.length(&2, Spec.Tree, done) : Nat}

def len_app_one(done, t):
  match done:
    case Nil{}:
      {==}
    case Con{+u, +us}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, us, [t])), 1n+List.length(&2, Spec.Tree, us), len_app_one(us, t))

law leaves_len_app_one:
  for done: +List<Spec.Tree>
  for +t: Spec.Tree
  {List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, done, [t]))) == Nat.add(List.length(&2, Nat, Spec.leaves(done)), List.length(&2, Nat, Spec.leaves([t]))) : Nat}

def leaves_len_app_one(done, t):
  match done:
    case Nil{}:
      {==}
    case Con{+u, +us}:
      +lu = List.length(&2, Nat, Spec.leaves([u]))
      +r = leaves_len_app_one(us, t)
      +c1 = len_cons(u, List.append(&2, Spec.Tree, us, [t]))
      +c2 = len_cons(u, us)
      Equal.trans(Nat, List.length(&2, Nat, Spec.leaves(u <> List.append(&2, Spec.Tree, us, [t]))), Nat.add(lu, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, us, [t])))), Nat.add(List.length(&2, Nat, Spec.leaves(u <> us)), List.length(&2, Nat, Spec.leaves([t]))), c1,
        Equal.trans(Nat, Nat.add(lu, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, us, [t])))), Nat.add(lu, Nat.add(List.length(&2, Nat, Spec.leaves(us)), List.length(&2, Nat, Spec.leaves([t])))), Nat.add(List.length(&2, Nat, Spec.leaves(u <> us)), List.length(&2, Nat, Spec.leaves([t]))), Equal.cong(Nat, Nat, v => Nat.add(lu, v), List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, us, [t]))), Nat.add(List.length(&2, Nat, Spec.leaves(us)), List.length(&2, Nat, Spec.leaves([t]))), r),
          Equal.trans(Nat, Nat.add(lu, Nat.add(List.length(&2, Nat, Spec.leaves(us)), List.length(&2, Nat, Spec.leaves([t])))), Nat.add(Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves([t]))), Nat.add(List.length(&2, Nat, Spec.leaves(u <> us)), List.length(&2, Nat, Spec.leaves([t]))), Equal.sym(Nat, Nat.add(Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves([t]))), Nat.add(lu, Nat.add(List.length(&2, Nat, Spec.leaves(us)), List.length(&2, Nat, Spec.leaves([t])))), Lemma.add_assoc(lu, List.length(&2, Nat, Spec.leaves(us)), List.length(&2, Nat, Spec.leaves([t])))), Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Nat, Spec.leaves([t]))), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), List.length(&2, Nat, Spec.leaves(u <> us)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(u <> us)), Nat.add(lu, List.length(&2, Nat, Spec.leaves(us))), c2)))))

# ======== DIRECTION 2 AT A NODE: NO BETTER READING, SO THE OWN STEPS ARE KEPT ========

law tok_all:
  for +input: +List<Nat>
  for +i: Nat
  for +ch: +List<Spec.Tree>
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  {Prefer.tokensFrom(input, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))) == Spec.leaves(ch) : +List<Nat>}

def tok_all(input, i, ch, next, pos):
  +L = List.length(&2, Nat, Spec.leaves(ch))
  Equal.trans(+List<Nat>, Prefer.tokensFrom(input, i, Nat.add(i, L)), Lemma.takeN(L, Lemma.dropN(i, input)), Spec.leaves(ch), PG.tok_take(input, i, L),
    Equal.trans(+List<Nat>, Lemma.takeN(L, Lemma.dropN(i, input)), Lemma.takeN(L, List.append(&2, Nat, Spec.leaves(ch), next)), Spec.leaves(ch), Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(L, v), Lemma.dropN(i, input), List.append(&2, Nat, Spec.leaves(ch), next), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), next), Lemma.dropN(i, input), pos)), Lemma.take_append_length(Spec.leaves(ch), next)))

# What the walk knows of a reading made of the set's steps: phases 1 and 2 keep it where
# the children stand (the set is the preference oracle's, pruned).
def RivalKept(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +index: Nat, +rpath: +List<Nat>, +own: +List<Spec.Guard>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +ch: +List<Spec.Tree>, +i: Nat, +s: +List<Spec.Bsr>) -> Type:
  @f2: +List<Spec.Tree> -> {Spec.fits(f2, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool} -> {Spec.leaves(f2) == Spec.leaves(ch) : +List<Nat>} -> {Spec.allIn(Spec.walk(f2, False{}, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool} ->
    Spec.AllHold(grammar, own, Gll.seqAt(grammar, index, rpath), f2, List.append(&2, Nat, Spec.leaves(ch), after)) & Spec.Admissible(grammar, guards, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, after) & Spec.Unbeaten(grammar, guards, pmarks, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, above, span, after)

law rival_build:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +d: Nat
  for +ext: Spec.Extent
  for +L: Nat
  for +bt: {Spec.better(ext, L, lenAt(ch, d)) == True{} : Bool}
  for +f2: +List<Spec.Tree>
  for +fit2: {Spec.fits(f2, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +lv2: {Spec.leaves(f2) == Prefer.tokensFrom(input, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))) : +List<Nat>}
  for +cons2: {Ext.consOk(f2, 0n, i, d, L, False{}, 0n, 0n, 0n) == True{} : Bool}
  for +all2: {Spec.allIn(Spec.walk(f2, False{}, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for mo2: MeasOne(marks, f2, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, d, ext)
  for mo1: MeasOne(marks, ch, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), 0n, d, ext)
  Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)

def rival_build(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, d, ext, L, bt, f2, fit2, lv2, cons2, all2, keep, mo2, mo1):
  match mo2:
    case (m20, (lt20, le20)):
      match mo1:
        case (m10, rest1):
          +S = Gll.seqAt(grammar, index, rpath)
          +P = Gll.reverseOnto(rpath, [])
          +s0 = Lemma.sub_zero(d)
          +has = Equal.trans(Bool, Nat.is_lt(d, List.length(&2, Spec.Tree, f2)), Nat.is_lt(Nat.sub(d, 0n), List.length(&2, Spec.Tree, f2)), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(v, List.length(&2, Spec.Tree, f2)), d, Nat.sub(d, 0n), Equal.sym(Nat, Nat.sub(d, 0n), d, s0)), lt20)
          +lenEq = mark_len(f2, 0n, i, d, L, cons_mark(f2, 0n, i, d, L, False{}, 0n, 0n, 0n, cons2), has)
          +Lc = lenAt(ch, d)
          +m2 = Equal.trans(+List<Spec.Measure>, Spec.measures(marks, f2, S, index, P, 0n), [Spec.Measure{ext, lenAt(f2, Nat.sub(d, 0n))}], [Spec.Measure{ext, L}], m20, Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{ext, v}], lenAt(f2, Nat.sub(d, 0n)), L, Equal.trans(Nat, lenAt(f2, Nat.sub(d, 0n)), lenAt(f2, d), L, Equal.cong(Nat, Nat, v => lenAt(f2, v), Nat.sub(d, 0n), d, s0), lenEq)))
          +m1 = Equal.trans(+List<Spec.Measure>, Spec.measures(marks, ch, S, index, P, 0n), [Spec.Measure{ext, lenAt(ch, Nat.sub(d, 0n))}], [Spec.Measure{ext, Lc}], m10, Equal.cong(Nat, +List<Spec.Measure>, v => [Spec.Measure{ext, lenAt(ch, v)}], Nat.sub(d, 0n), d, s0))
          +bts = Equal.trans(Bool, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), Spec.beats([Spec.Measure{ext, L}], [Spec.Measure{ext, Lc}]), True{}, Lemma_beats2(Spec.measures(marks, f2, S, index, P, 0n), [Spec.Measure{ext, L}], Spec.measures(marks, ch, S, index, P, 0n), [Spec.Measure{ext, Lc}], m2, m1), Equal.trans(Bool, Spec.beats([Spec.Measure{ext, L}], [Spec.Measure{ext, Lc}]), Spec.better(ext, L, Lc), True{}, beats_one(ext, L, Lc), bt))
          +lvC = Equal.trans(+List<Nat>, Spec.leaves(f2), Prefer.tokensFrom(input, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))), Spec.leaves(ch), lv2, tok_all(input, i, ch, next, pos))
          (f2, (fit2, (lvC, (bts, keep(f2, fit2, lvC, all2)))))

law rival_from_reading:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +L: Nat
  for +bt: {Spec.better(ext, L, lenAt(ch, d)) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for rd: Reading(grammar, Gll.seqAt(grammar, index, rpath), input, s, index, Gll.reverseOnto(rpath, []), i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), d, L)
  Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)

def rival_from_reading(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, d, ext, mEq, L, bt, keep, rd):
  match rd:
    case (f20, (fit20, (lv20, (cons20, all20)))):
      +S = Gll.seqAt(grammar, index, rpath)
      +P = Gll.reverseOnto(rpath, [])
      +f2 = {f20 : +List<Spec.Tree>}
      +fit2 = {fit20 : {Spec.fits(f2, grammar, S) == True{} : Bool}}
      +lv2 = {lv20 : {Spec.leaves(f2) == Prefer.tokensFrom(input, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))) : +List<Nat>}}
      +cons2 = {cons20 : {Ext.consOk(f2, 0n, i, d, L, False{}, 0n, 0n, 0n) == True{} : Bool}}
      +all2 = {all20 : {Spec.allIn(Spec.walk(f2, False{}, index, P, 0n, i, i), s) == True{} : Bool}}
      mo2 = measures_one(S, f2, marks, grammar, index, P, 0n, d, ext, mEq, fit2)
      mo1 = measures_one(S, ch, marks, grammar, index, P, 0n, d, ext, mEq, fit)
      rival_build(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, d, ext, L, bt, f2, fit2, lv2, cons2, all2, keep, mo2, mo1)

# A certified length L gives a rival, when L beats the tree's length.
law rival_of_cert:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +L: Nat
  for +bt: {Spec.better(ext, L, lenAt(ch, d)) == True{} : Bool}
  for +cert: {Ext.certified(Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, L, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)

def rival_of_cert(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, d, ext, mEq, L, bt, cert, keep):
  +S = Gll.seqAt(grammar, index, rpath)
  +P = Gll.reverseOnto(rpath, [])
  +e = Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))
  rd = cert_reading(fuel, grammar, input, s, index, rpath, P, S, d, i, L, e, cert)
  rival_from_reading(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, d, ext, mEq, L, bt, keep, rd)

law best_found_ext:
  for ext: Spec.Extent
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allP: {Spec.allIn(PG.ownSteps(ch, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +d: Nat
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +le: {Nat.is_le(lenAt(ch, d), Nat.sub(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), i)) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for noRival: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty
  {foundOr(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))), lenAt(ch, d)) == True{} : Bool}

def best_found_ext(ext, fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, allP, d, mEq, le, keep, noRival):
  match ext:
    case Spec.Longest{}:
      +W = Ext.seqOf(s, fuel, grammar, input, index, rpath)
      +e = Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))
      down_found(Nat.sub(e, i), W, d, i, e, lenAt(ch, d), le,
        no => rival_reads(s, fuel, grammar, input, index, rpath, d, i, e, ch, fit, allP, {==}, no),
        L => lt => y => c => noRival(rival_of_cert(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, d, Spec.Longest{}, mEq, L, lt, c, keep)))
    case Spec.Shortest{}:
      +W = Ext.seqOf(s, fuel, grammar, input, index, rpath)
      +e = Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))
      up_found(Nat.sub(e, i), 0n, W, d, i, e, lenAt(ch, d), Lemma.zero_le(lenAt(ch, d)), le,
        no => rival_reads(s, fuel, grammar, input, index, rpath, d, i, e, ch, fit, allP, {==}, no),
        L => lt => y => c => noRival(rival_of_cert(fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, d, Spec.Shortest{}, mEq, L, lt, c, keep)))

# The tree's length is the one found, or the search is unsure.
law best_found:
  for ext: Spec.Extent
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allP: {Spec.allIn(PG.ownSteps(ch, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +d: Nat
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for noRival: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty
  {foundOr(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))), lenAt(ch, d)) == True{} : Bool}

def best_found(ext, fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, allP, d, mEq, keep, noRival):
  +W = Ext.seqOf(s, fuel, grammar, input, index, rpath)
  +Lch = List.length(&2, Nat, Spec.leaves(ch))
  +e = Nat.add(i, Lch)
  +Lc = lenAt(ch, d)
  +subE = Lemma.sub_add_left(i, Lch)
  +le = Equal.trans(Bool, Nat.is_le(Lc, Nat.sub(e, i)), Nat.is_le(Lc, Lch), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(Lc, v), Nat.sub(e, i), Lch, subE), len_at_le(ch, d))
  best_found_ext(ext, fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, ch, i, next, pos, fit, allP, d, mEq, le, keep, noRival)

law onbest_case:
  for b: Ext.Best
  for +w: Ext.Seq
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +e: Nat
  for +Lc: Nat
  for +F: {foundOr(b, Lc) == True{} : Bool}
  for +no: {Ext.onBest(b, w, p, d, i, k, j, e) == Guard.No{} : Guard.Tri}
  for later: {Ext.readsWith(w, d, Lc, True{}, p, k, j, i, e) == Guard.No{} : Guard.Tri} -> Empty
  Empty

def onbest_case(b, w, p, d, i, k, j, e, Lc, F, no, later):
  match b:
    case Ext.Found{+x}:
      +xEq = Lemma.nat_eq_sound(x, Lc, F)
      later(Equal.trans(Guard.Tri, Ext.readsWith(w, d, Lc, True{}, p, k, j, i, e), Ext.readsWith(w, d, x, True{}, p, k, j, i, e), Guard.No{}, Equal.cong(Nat, Guard.Tri, v => Ext.readsWith(w, d, v, True{}, p, k, j, i, e), Lc, x, Equal.sym(Nat, x, Lc, xEq)), no))
    case Ext.NoneFound{}:
      Lemma.false_is_not_true(F)
    case Ext.Unsure{}:
      PG.tri_ne_unknown_no(no)

law sub_one:
  for +p: Nat
  {Nat.sub(1n+p, 1n) == p : Nat}

def sub_one(p):
  Lemma.sub_zero(p)

# An own step (child p) of a node with one mark, whose children have no better reading.
law step_kept_one:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allP: {Spec.allIn(PG.ownSteps(ch, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == False{} : Bool}
  for +F: {foundOr(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))), lenAt(ch, d)) == True{} : Bool}
  for +inE: {Prefer.natIn(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), Ext.endsOf(s, index, List.append(&2, Nat, Gll.reverseOnto(rpath, []), [List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath))]), i)) == True{} : Bool}
  for +p: Nat
  for +memS: {Spec.bsrMember(Spec.at(index, prefix, 1n+p, i, startOf(ch, p, i), endAt(ch, p, i)), s) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, 1n+p, i, startOf(ch, p, i), endAt(ch, p, i)), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def step_kept_one(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, ch, i, next, pos, fit, allP, d, ext, mEq, lEq, F, inE, p, memS):
  +S = Gll.seqAt(grammar, index, rpath)
  +P = Gll.reverseOnto(rpath, [])
  +k = startOf(ch, p, i)
  +j = endAt(ch, p, i)
  +y = Spec.at(index, prefix, 1n+p, i, k, j)
  +Lch = List.length(&2, Nat, Spec.leaves(ch))
  +e = Nat.add(i, Lch)
  +Lc = lenAt(ch, d)
  +ends = Ext.endsOf(s, index, List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), i)
  +v = Ext.stepVerdict(s, fuel, grammar, marks, input, y)
  +vOne = Ext.verdictFor(Ext.OneMark{d, ext}, False{}, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j)
  +dec = verdict_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, 1n+p, i, k, j)
  +vEq = Equal.trans(Guard.Tri, v, Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j), vOne, dec,
    Equal.trans(Guard.Tri, Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j), Ext.verdictFor(Ext.OneMark{d, ext}, Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j), vOne,
      Equal.cong(Ext.Marked, Guard.Tri, w => Ext.verdictFor(w, Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j), Mk(grammar, marks, index, rpath), Ext.OneMark{d, ext}, mEq),
      Equal.cong(Bool, Guard.Tri, w => Ext.verdictFor(Ext.OneMark{d, ext}, w, Ext.seqOf(s, fuel, grammar, input, index, rpath), 1n+p, i, k, j), Ext.seqLoopy(rpath, grammar, index), False{}, lEq)))
  +kn = eknown_of(s, s, fuel, grammar, marks, input, okK, y, memS)
  +sp = sub_one(p)
  +p1 = Nat.sub(1n+p, 1n)
  +st0 = steps_own(ch, 0n, i, p)
  +st = Equal.trans(Bool, stepsOk(ch, 0n, i, True{}, p1, k, j), stepsOk(ch, 0n, i, True{}, p, k, j), True{}, Equal.cong(Nat, Bool, w => stepsOk(ch, 0n, i, True{}, w, k, j), p1, p, sp), st0)
  +cons = cons_split(ch, 0n, i, d, Lc, True{}, p1, k, j, mark_own(ch, 0n, i, d), st)
  +subE = Lemma.sub_add_left(i, Lch)
  +room = Equal.trans(Bool, Nat.is_lt(headLen(ch), 1n+Nat.sub(e, i)), Nat.is_lt(headLen(ch), 1n+Lch), True{}, Equal.cong(Nat, Bool, w => Nat.is_lt(headLen(ch), 1n+w), Nat.sub(e, i), Lch, subE), Lemma.lt_of_succ_le(headLen(ch), 1n+Lch, head_le(ch)))
  +yes = PG.yes_of_known(v, kn, vNo => onbest_case(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, e), Ext.seqOf(s, fuel, grammar, input, index, rpath), p1, d, i, k, j, e, Lc, F,
    some_best_at(ends, ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), p1, d, i, k, j, Equal.trans(Guard.Tri, vOne, v, Guard.No{}, Equal.sym(Guard.Tri, v, vOne, vEq), vNo), e, inE),
    no => search_not_no(Ext.gasFor(S, i, e), S, ch, 1n+Nat.sub(e, i), s, index, P, i, grammar, 0n, i, e, d, Lc, True{}, p1, k, j, fit, allP, {==}, cons, room, no)))
  ekept_of(s, fuel, grammar, marks, input, s, y, memS, PG.is_yes_of(v, yes))

law empty_kept_one:
  for dot: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +k: Nat
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == False{} : Bool}
  for +allS: {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), s) == True{} : Bool}
  {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def empty_kept_one(dot, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, k, d, ext, mEq, lEq, allS):
  match dot:
    case 0n:
      +y = Spec.at(index, prefix, 0n, i, k, k)
      +P = Gll.reverseOnto(rpath, [])
      +S = Gll.seqAt(grammar, index, rpath)
      +memS = Lemma.and_true_left(Spec.bsrMember(y, s), True{}, allS)
      +dec = verdict_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, 0n, i, k, k)
      +vEq = Equal.trans(Guard.Tri, Ext.stepVerdict(s, fuel, grammar, marks, input, y), Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 0n, i, k, k), Guard.Yes{}, dec,
        Equal.trans(Guard.Tri, Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 0n, i, k, k), Ext.verdictFor(Ext.OneMark{d, ext}, Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 0n, i, k, k), Guard.Yes{},
          Equal.cong(Ext.Marked, Guard.Tri, w => Ext.verdictFor(w, Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), 0n, i, k, k), Mk(grammar, marks, index, rpath), Ext.OneMark{d, ext}, mEq),
          Equal.cong(Bool, Guard.Tri, w => Ext.verdictFor(Ext.OneMark{d, ext}, w, Ext.seqOf(s, fuel, grammar, input, index, rpath), 0n, i, k, k), Ext.seqLoopy(rpath, grammar, index), False{}, lEq)))
      Lemma.and_true_intro(Spec.bsrMember(y, Ext.extentKept(s, s, fuel, grammar, marks, input)), True{}, ekept_of(s, fuel, grammar, marks, input, s, y, memS, PG.is_yes_of(Ext.stepVerdict(s, fuel, grammar, marks, input, y), vEq)), {==})
    case 1n+q:
      {==}

law span_eq:
  for +index: Nat
  for +prefix: +List<Nat>
  for +dd: Nat
  for +i: Nat
  for +k1: Nat
  for +k2: Nat
  for +j1: Nat
  for +j2: Nat
  for +ek: {k1 == k2 : Nat}
  for +ej: {j1 == j2 : Nat}
  {Spec.at(index, prefix, dd, i, k1, j1) == Spec.at(index, prefix, dd, i, k2, j2) : Spec.Bsr}

def span_eq(index, prefix, dd, i, k1, k2, j1, j2, ek, ej):
  Equal.trans(Spec.Bsr, Spec.at(index, prefix, dd, i, k1, j1), Spec.at(index, prefix, dd, i, k2, j1), Spec.at(index, prefix, dd, i, k2, j2), Equal.cong(Nat, Spec.Bsr, w => Spec.at(index, prefix, dd, i, w, j1), k1, k2, ek), Equal.cong(Nat, Spec.Bsr, w => Spec.at(index, prefix, dd, i, k2, w), j1, j2, ej))

law own_iter:
  for f: +List<Spec.Tree>
  for +done: +List<Spec.Tree>
  for +dot: Nat
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allP: {Spec.allIn(PG.ownSteps(ch, index, Gll.reverseOnto(rpath, []), 0n, i, i), s) == True{} : Bool}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == False{} : Bool}
  for +F: {foundOr(Ext.bestLength(ext, Ext.seqOf(s, fuel, grammar, input, index, rpath), d, i, Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))), lenAt(ch, d)) == True{} : Bool}
  for +inE: {Prefer.natIn(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), Ext.endsOf(s, index, List.append(&2, Nat, Gll.reverseOnto(rpath, []), [List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath))]), i)) == True{} : Bool}
  for +chEq: {List.append(&2, Spec.Tree, done, f) == ch : +List<Spec.Tree>}
  for +dEq: {List.length(&2, Spec.Tree, done) == dot : Nat}
  for +kEq: {k == Nat.add(i, List.length(&2, Nat, Spec.leaves(done))) : Nat}
  for +allS: {Spec.allIn(PG.ownSteps(f, index, prefix, dot, i, k), s) == True{} : Bool}
  {Spec.allIn(PG.ownSteps(f, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def own_iter(f, done, dot, k, fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, ch, i, next, pos, fit, allP, d, ext, mEq, lEq, F, inE, chEq, dEq, kEq, allS):
  match f:
    case Nil{}:
      empty_kept_one(dot, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, k, d, ext, mEq, lEq, allS)
    case Con{+u, +us}:
      +K = Ext.extentKept(s, s, fuel, grammar, marks, input)
      +e = Sub.endOf(u, k)
      +y = Spec.at(index, prefix, 1n+dot, i, k, e)
      +memS = Lemma.and_true_left(Spec.bsrMember(y, s), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), s), allS)
      +restS = Lemma.and_true_right_side(Spec.bsrMember(y, s), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), s), allS)
      +app = List.append(&2, Spec.Tree, done, u <> us)
      +ld = List.length(&2, Nat, Spec.leaves(done))
      +lu = List.length(&2, Nat, Spec.leaves([u]))
      +s1 = Equal.trans(Nat, startOf(ch, dot, i), startOf(app, dot, i), k, Equal.cong(+List<Spec.Tree>, Nat, w => startOf(w, dot, i), ch, app, Equal.sym(+List<Spec.Tree>, app, ch, chEq)),
        Equal.trans(Nat, startOf(app, dot, i), startOf(app, List.length(&2, Spec.Tree, done), i), k, Equal.cong(Nat, Nat, w => startOf(app, w, i), dot, List.length(&2, Spec.Tree, done), Equal.sym(Nat, List.length(&2, Spec.Tree, done), dot, dEq)),
          Equal.trans(Nat, startOf(app, List.length(&2, Spec.Tree, done), i), Nat.add(i, ld), k, start_app(done, u <> us, i), Equal.sym(Nat, k, Nat.add(i, ld), kEq))))
      +e1 = Equal.trans(Nat, endAt(ch, dot, i), endAt(app, dot, i), e, Equal.cong(+List<Spec.Tree>, Nat, w => endAt(w, dot, i), ch, app, Equal.sym(+List<Spec.Tree>, app, ch, chEq)),
        Equal.trans(Nat, endAt(app, dot, i), endAt(app, List.length(&2, Spec.Tree, done), i), e, Equal.cong(Nat, Nat, w => endAt(app, w, i), dot, List.length(&2, Spec.Tree, done), Equal.sym(Nat, List.length(&2, Spec.Tree, done), dot, dEq)),
          Equal.trans(Nat, endAt(app, List.length(&2, Spec.Tree, done), i), Nat.add(Nat.add(i, ld), lu), e, end_app(done, u, us, i),
            Equal.trans(Nat, Nat.add(Nat.add(i, ld), lu), Nat.add(k, lu), e, Equal.cong(Nat, Nat, w => Nat.add(w, lu), Nat.add(i, ld), k, Equal.sym(Nat, k, Nat.add(i, ld), kEq)), Equal.sym(Nat, e, Nat.add(k, lu), end_of_add(u, k))))))
      +yF = Spec.at(index, prefix, 1n+dot, i, startOf(ch, dot, i), endAt(ch, dot, i))
      +spanEq = span_eq(index, prefix, 1n+dot, i, startOf(ch, dot, i), k, endAt(ch, dot, i), e, s1, e1)
      +memSF = Equal.trans(Bool, Spec.bsrMember(yF, s), Spec.bsrMember(y, s), True{}, Equal.cong(Spec.Bsr, Bool, w => Spec.bsrMember(w, s), yF, y, spanEq), memS)
      +memKF = step_kept_one(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, ch, i, next, pos, fit, allP, d, ext, mEq, lEq, F, inE, dot, memSF)
      +memK = Equal.trans(Bool, Spec.bsrMember(y, K), Spec.bsrMember(yF, K), True{}, Equal.cong(Spec.Bsr, Bool, w => Spec.bsrMember(w, K), y, yF, Equal.sym(Spec.Bsr, yF, y, spanEq)), memKF)
      +done2 = List.append(&2, Spec.Tree, done, [u])
      +chEq2 = Equal.trans(+List<Spec.Tree>, List.append(&2, Spec.Tree, done2, us), app, ch, tree_app_one(done, u, us), chEq)
      +dEq2 = Equal.trans(Nat, List.length(&2, Spec.Tree, done2), 1n+List.length(&2, Spec.Tree, done), 1n+dot, len_app_one(done, u), Equal.cong(Nat, Nat, w => 1n+w, List.length(&2, Spec.Tree, done), dot, dEq))
      +kEq2 = Equal.trans(Nat, e, Nat.add(k, lu), Nat.add(i, List.length(&2, Nat, Spec.leaves(done2))), end_of_add(u, k),
        Equal.trans(Nat, Nat.add(k, lu), Nat.add(Nat.add(i, ld), lu), Nat.add(i, List.length(&2, Nat, Spec.leaves(done2))), Equal.cong(Nat, Nat, w => Nat.add(w, lu), k, Nat.add(i, ld), kEq),
          Equal.trans(Nat, Nat.add(Nat.add(i, ld), lu), Nat.add(i, Nat.add(ld, lu)), Nat.add(i, List.length(&2, Nat, Spec.leaves(done2))), Lemma.add_assoc(i, ld, lu), Equal.cong(Nat, Nat, w => Nat.add(i, w), Nat.add(ld, lu), List.length(&2, Nat, Spec.leaves(done2)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(done2)), Nat.add(ld, lu), leaves_len_app_one(done, u))))))
      +rest = own_iter(us, done2, 1n+dot, e, fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, ch, i, next, pos, fit, allP, d, ext, mEq, lEq, F, inE, chEq2, dEq2, kEq2, restS)
      Lemma.and_true_intro(Spec.bsrMember(y, K), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), K), memK, rest)

# ---- Direction 2 at a node or pick: its own steps are kept ----

# Without a mark every own step answers Yes.
law nomark_kept_at:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.NoMark{} : Ext.Marked}
  for +dd: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +mem: {Spec.bsrMember(Spec.at(index, prefix, dd, i, k, j), s) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, dd, i, k, j), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def nomark_kept_at(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, dd, i, k, j, mem):
  +y = Spec.at(index, prefix, dd, i, k, j)
  +P = Gll.reverseOnto(rpath, [])
  +S = Gll.seqAt(grammar, index, rpath)
  +L = Ext.seqLoopy(rpath, grammar, index)
  +dec = verdict_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, dd, i, k, j)
  +v2 = Equal.trans(Guard.Tri, Ext.stepVerdict(s, fuel, grammar, marks, input, y), Ext.verdictFor(Mk(grammar, marks, index, rpath), L, Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j), Guard.Yes{}, dec,
    Equal.cong(Ext.Marked, Guard.Tri, w => Ext.verdictFor(w, L, Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j), Mk(grammar, marks, index, rpath), Ext.NoMark{}, mEq))
  ekept_of(s, fuel, grammar, marks, input, s, y, mem, PG.is_yes_of(Ext.stepVerdict(s, fuel, grammar, marks, input, y), v2))

law nomark_empty:
  for dot: Nat
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.NoMark{} : Ext.Marked}
  for +i: Nat
  for +allS: {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), s) == True{} : Bool}
  {Spec.allIn(Spec.emptyStep(dot, index, prefix, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def nomark_empty(dot, k, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, allS):
  match dot:
    case 0n:
      +y = Spec.at(index, prefix, 0n, i, k, k)
      +memS = Lemma.and_true_left(Spec.bsrMember(y, s), True{}, allS)
      Lemma.and_true_intro(Spec.bsrMember(y, Ext.extentKept(s, s, fuel, grammar, marks, input)), True{}, nomark_kept_at(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, 0n, i, k, k, memS), {==})
    case 1n+q:
      {==}

law nomark_iter:
  for f: +List<Spec.Tree>
  for +dot: Nat
  for +k: Nat
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.NoMark{} : Ext.Marked}
  for +i: Nat
  for +allS: {Spec.allIn(PG.ownSteps(f, index, prefix, dot, i, k), s) == True{} : Bool}
  {Spec.allIn(PG.ownSteps(f, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def nomark_iter(f, dot, k, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, allS):
  match f:
    case Nil{}:
      nomark_empty(dot, k, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, allS)
    case Con{+u, +us}:
      +K = Ext.extentKept(s, s, fuel, grammar, marks, input)
      +e = Sub.endOf(u, k)
      +y = Spec.at(index, prefix, 1n+dot, i, k, e)
      +memS = Lemma.and_true_left(Spec.bsrMember(y, s), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), s), allS)
      +restS = Lemma.and_true_right_side(Spec.bsrMember(y, s), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), s), allS)
      Lemma.and_true_intro(Spec.bsrMember(y, K), Spec.allIn(PG.ownSteps(us, index, prefix, 1n+dot, i, e), K), nomark_kept_at(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, 1n+dot, i, k, e, memS), nomark_iter(us, 1n+dot, e, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, restS))

law bad_verdict_known:
  for m: Ext.Marked
  for l: Bool
  for +w: Ext.Seq
  for +dd: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +bad: {isBad(m, l) == True{} : Bool}
  for +kn: {Guard.isKnown(Ext.verdictFor(m, l, w, dd, i, k, j)) == True{} : Bool}
  Empty

def bad_verdict_known(m, l, w, dd, i, k, j, bad, kn):
  match m l:
    case Ext.ManyMarks{} _:
      Lemma.false_is_not_true(kn)
    case Ext.OneMark{d, e} True{}:
      Lemma.false_is_not_true(kn)
    case Ext.OneMark{d, e} False{}:
      Lemma.false_is_not_true(bad)
    case Ext.NoMark{} _:
      Lemma.false_is_not_true(bad)

# A bad mark gives Unknown at every own step, which the oracle refuses to answer with.
law bad_known:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +i: Nat
  for +bad: {isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)) == True{} : Bool}
  for first: FirstOwn(index, prefix, i, s)
  Empty

def bad_known(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, i, bad, first):
  match first:
    case (dd0, rest0):
      match rest0:
        case (k0, (j0, m0)):
          +dd = {dd0 : Nat}
          +k = {k0 : Nat}
          +j = {j0 : Nat}
          +x = Spec.at(index, prefix, dd, i, k, j)
          +V = Ext.verdictFor(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j)
          +kn = eknown_of(s, s, fuel, grammar, marks, input, okK, x, m0)
          +kn2 = Equal.trans(Bool, Guard.isKnown(V), Guard.isKnown(Ext.stepVerdict(s, fuel, grammar, marks, input, x)), True{}, Equal.cong(Guard.Tri, Bool, v => Guard.isKnown(v), V, Ext.stepVerdict(s, fuel, grammar, marks, input, x), Equal.sym(Guard.Tri, Ext.stepVerdict(s, fuel, grammar, marks, input, x), V, verdict_decode(s, fuel, grammar, marks, input, index, rpath, prefix, pEq, dd, i, k, j))), kn)
          bad_verdict_known(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index), Ext.seqOf(s, fuel, grammar, input, index, rpath), dd, i, k, j, bad, kn2)

# The tree's own end is one of the sequence's ends in the set.
law own_end_in:
  for +grammar: +List<Spec.Production>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +i: Nat
  for +fit: {Spec.fits(t <> ts, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allS: {Spec.allIn(PG.ownSteps(t <> ts, index, prefix, 0n, i, i), s) == True{} : Bool}
  {Prefer.natIn(Nat.add(i, List.length(&2, Nat, Spec.leaves(t <> ts))), Ext.endsOf(s, index, List.append(&2, Nat, Gll.reverseOnto(rpath, []), [List.length(&2, Spec.Item, Gll.seqAt(grammar, index, rpath))]), i)) == True{} : Bool}

def own_end_in(grammar, s, index, rpath, prefix, pEq, t, ts, i, fit, allS):
  +S = Gll.seqAt(grammar, index, rpath)
  +P = Gll.reverseOnto(rpath, [])
  +ch = {t <> ts : +List<Spec.Tree>}
  +e = Nat.add(i, List.length(&2, Nat, Spec.leaves(ch)))
  +nS = Fits.fits_count(ch, grammar, S, fit)
  +memL = own_nth(ch, index, prefix, 0n, i, i, s, List.length(&2, Spec.Tree, ts), allS, lt_self(List.length(&2, Spec.Tree, ts)))
  +kL = startOf(ch, List.length(&2, Spec.Tree, ts), i)
  +endP = List.append(&2, Nat, prefix, [1n+List.length(&2, Spec.Tree, ts)])
  +memL2 = Equal.trans(Bool, Spec.bsrMember(Spec.Bsr{Spec.Slot{index, endP}, i, kL, e}, s), Spec.bsrMember(Spec.at(index, prefix, 1n+List.length(&2, Spec.Tree, ts), i, kL, endAt(ch, List.length(&2, Spec.Tree, ts), i)), s), True{}, Equal.cong(Nat, Bool, v => Spec.bsrMember(Spec.Bsr{Spec.Slot{index, endP}, i, kL, v}, s), e, endAt(ch, List.length(&2, Spec.Tree, ts), i), Equal.sym(Nat, endAt(ch, List.length(&2, Spec.Tree, ts), i), e, end_last(ts, t, i))), memL)
  +inE0 = ends_in(s, index, endP, i, kL, e, memL2)
  +pathEq = Equal.trans(+List<Nat>, endP, List.append(&2, Nat, P, [1n+List.length(&2, Spec.Tree, ts)]), List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [1n+List.length(&2, Spec.Tree, ts)]), prefix, P, pEq), Equal.cong(Nat, +List<Nat>, v => List.append(&2, Nat, P, [v]), 1n+List.length(&2, Spec.Tree, ts), List.length(&2, Spec.Item, S), nS))
  Equal.trans(Bool, Prefer.natIn(e, Ext.endsOf(s, index, List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), i)), Prefer.natIn(e, Ext.endsOf(s, index, endP, i)), True{}, Equal.cong(+List<Nat>, Bool, v => Prefer.natIn(e, Ext.endsOf(s, index, v, i)), List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), endP, Equal.sym(+List<Nat>, endP, List.append(&2, Nat, P, [List.length(&2, Spec.Item, S)]), pathEq)), inE0)

law owner_fine:
  for ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == False{} : Bool}
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +bnd: {Nat.is_le(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, input)) == True{} : Bool}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allS: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), s) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for noRival: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty
  {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def owner_fine(ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okK, index, rpath, prefix, pEq, d, ext, mEq, lEq, i, next, pos, bnd, fit, allS, keep, noRival):
  match ch:
    case Nil{}:
      empty_kept_one(0n, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, i, d, ext, mEq, lEq, allS)
    case Con{+t, +ts}:
      +allP = Equal.trans(Bool, Spec.allIn(PG.ownSteps(t <> ts, index, Gll.reverseOnto(rpath, []), 0n, i, i), s), Spec.allIn(PG.ownSteps(t <> ts, index, prefix, 0n, i, i), s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(PG.ownSteps(t <> ts, index, v, 0n, i, i), s), Gll.reverseOnto(rpath, []), prefix, Equal.sym(+List<Nat>, prefix, Gll.reverseOnto(rpath, []), pEq)), allS)
      +F = best_found(ext, fuel, grammar, marks, guards, pmarks, own, after, above, span, s, input, index, rpath, t <> ts, i, next, pos, fit, allP, d, mEq, keep, noRival)
      +inE = own_end_in(grammar, s, index, rpath, prefix, pEq, t, ts, i, fit, allS)
      +kEq = Equal.sym(Nat, Nat.add(i, 0n), i, Lemma.add_zero_right(i))
      own_iter(t <> ts, [], 0n, i, fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, t <> ts, i, next, pos, fit, allP, d, ext, mEq, lEq, F, inE, {==}, {==}, kEq, allS)

law owner_one:
  for l: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +d: Nat
  for +ext: Spec.Extent
  for +mEq: {Mk(grammar, marks, index, rpath) == Ext.OneMark{d, ext} : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == l : Bool}
  for ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +bnd: {Nat.is_le(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, input)) == True{} : Bool}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allS: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), s) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for noRival: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty
  {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def owner_one(l, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okK, index, rpath, prefix, pEq, d, ext, mEq, lEq, ch, i, next, pos, bnd, fit, allS, keep, noRival):
  match l:
    case True{}:
      goal = {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
      +b1 = Equal.cong(Ext.Marked, Bool, w => isBad(w, Ext.seqLoopy(rpath, grammar, index)), Mk(grammar, marks, index, rpath), Ext.OneMark{d, ext}, mEq)
      +b2 = Equal.cong(Bool, Bool, w => isBad(Ext.OneMark{d, ext}, w), Ext.seqLoopy(rpath, grammar, index), True{}, lEq)
      +bad = Equal.trans(Bool, isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)), isBad(Ext.OneMark{d, ext}, Ext.seqLoopy(rpath, grammar, index)), True{}, b1, Equal.trans(Bool, isBad(Ext.OneMark{d, ext}, Ext.seqLoopy(rpath, grammar, index)), isBad(Ext.OneMark{d, ext}, True{}), True{}, b2, {==}))
      Empty.absurd(goal, bad_known(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, i, bad, own_first(ch, index, prefix, i, s, allS)))
    case False{}:
      owner_fine(ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okK, index, rpath, prefix, pEq, d, ext, mEq, lEq, i, next, pos, bnd, fit, allS, keep, noRival)

law owner_m:
  for m: Ext.Marked
  for l: Bool
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == l : Bool}
  for ch: +List<Spec.Tree>
  for +i: Nat
  for +next: +List<Nat>
  for +pos: {List.append(&2, Nat, Spec.leaves(ch), next) == Lemma.dropN(i, input) : +List<Nat>}
  for +bnd: {Nat.is_le(Nat.add(i, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, input)) == True{} : Bool}
  for +fit: {Spec.fits(ch, grammar, Gll.seqAt(grammar, index, rpath)) == True{} : Bool}
  for +allS: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), s) == True{} : Bool}
  for keep: RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)
  for noRival: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch) -> Empty
  {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def owner_m(m, l, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okK, index, rpath, prefix, pEq, mEq, lEq, ch, i, next, pos, bnd, fit, allS, keep, noRival):
  match m:
    case Ext.NoMark{}:
      nomark_iter(ch, 0n, i, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, allS)
    case Ext.ManyMarks{}:
      goal = {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, i), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
      +bad = Equal.trans(Bool, isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)), isBad(Ext.ManyMarks{}, Ext.seqLoopy(rpath, grammar, index)), True{}, Equal.cong(Ext.Marked, Bool, w => isBad(w, Ext.seqLoopy(rpath, grammar, index)), Mk(grammar, marks, index, rpath), Ext.ManyMarks{}, mEq), {==})
      Empty.absurd(goal, bad_known(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, i, bad, own_first(ch, index, prefix, i, s, allS)))
    case Ext.OneMark{+d, +ext}:
      owner_one(l, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, okK, index, rpath, prefix, pEq, d, ext, mEq, lEq, ch, i, next, pos, bnd, fit, allS, keep, noRival)

# ======== WHAT THE TREE WALKS NEED ========

# A forest read at k ends inside the input.
law drop_bound:
  for k: Nat
  for +input: +List<Nat>
  for +w: +List<Nat>
  for +next: +List<Nat>
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for +pos: {List.append(&2, Nat, w, next) == Lemma.dropN(k, input) : +List<Nat>}
  {Nat.is_le(Nat.add(k, List.length(&2, Nat, w)), List.length(&2, Nat, input)) == True{} : Bool}

def drop_bound(k, input, w, next, kb, pos):
  match k:
    case 0n:
      +lw = List.length(&2, Nat, w)
      Equal.trans(Bool, Nat.is_le(lw, List.length(&2, Nat, input)), Nat.is_le(lw, List.length(&2, Nat, List.append(&2, Nat, w, next))), True{},
        Equal.cong(+List<Nat>, Bool, v => Nat.is_le(lw, List.length(&2, Nat, v)), input, List.append(&2, Nat, w, next), Equal.sym(+List<Nat>, List.append(&2, Nat, w, next), input, pos)),
        Equal.trans(Bool, Nat.is_le(lw, List.length(&2, Nat, List.append(&2, Nat, w, next))), Nat.is_le(lw, Nat.add(lw, List.length(&2, Nat, next))), True{},
          Equal.cong(Nat, Bool, v => Nat.is_le(lw, v), List.length(&2, Nat, List.append(&2, Nat, w, next)), Nat.add(lw, List.length(&2, Nat, next)), Lemma.length_append(w, next)),
          Lemma.le_add_right(lw, List.length(&2, Nat, next))))
    case 1n+p:
      match input:
        case Nil{}:
          Empty.absurd({Nat.is_le(Nat.add(1n+p, List.length(&2, Nat, w)), 0n) == True{} : Bool}, Lemma.false_is_not_true(kb))
        case Con{+y, +ys}:
          drop_bound(p, ys, w, next, kb, pos)

# A leaf read at k: k is before the end.
law drop_cons_bound:
  for k: Nat
  for +input: +List<Nat>
  for +x: Nat
  for +r: +List<Nat>
  for +pos: {x <> r == Lemma.dropN(k, input) : +List<Nat>}
  {Nat.is_le(1n+k, List.length(&2, Nat, input)) == True{} : Bool}

def drop_cons_bound(k, input, x, r, pos):
  match k:
    case 0n:
      Equal.trans(Bool, Nat.is_le(1n, List.length(&2, Nat, input)), Nat.is_le(1n, List.length(&2, Nat, x <> r)), True{}, Equal.cong(+List<Nat>, Bool, v => Nat.is_le(1n, List.length(&2, Nat, v)), input, x <> r, Equal.sym(+List<Nat>, x <> r, input, pos)), Lemma.zero_le(List.length(&2, Nat, r)))
    case 1n+p:
      match input:
        case Nil{}:
          Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Nat>, Bool, v => List.is_empty(&2, Nat, v), x <> r, [], pos)))
        case Con{+y, +ys}:
          drop_cons_bound(p, ys, x, r, pos)

# The first own step, for a sequence starting anywhere.
law own_first_k:
  for ch: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +set: +List<Spec.Bsr>
  for +all: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), set) == True{} : Bool}
  FirstOwn(index, prefix, i, set)

def own_first_k(ch, index, prefix, i, k, set, all):
  match ch:
    case Nil{}:
      (0n, (k, (k, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, k), set), True{}, all))))
    case Con{+t, +ts}:
      +e = Sub.endOf(t, k)
      (1n, (k, (e, Lemma.and_true_left(Spec.bsrMember(Spec.at(index, prefix, 1n, i, k, e), set), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n, i, e), set), all))))

# A round's alternative is a loopy sequence.
law loop_seq:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +loopIt: {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +isL: {Gll.isLoop(kind) == True{} : Bool}
  {Ext.seqLoopy(a <> m <> outer, grammar, index) == True{} : Bool}

def loop_seq(grammar, index, a, m, outer, kind, alts, loopIt, isL):
  Equal.trans(Bool, Ext.loopItem(G.loopItem(grammar, index, m <> outer)), Ext.loopItem(Some{Spec.Brack{kind, alts}}), True{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Ext.loopItem(v), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt), isL)

# A rival read along equal items and an equal path.
law rival_tr:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +own: +List<Spec.Guard>
  for +index: Nat
  for +its1: +List<Spec.Item>
  for +its2: +List<Spec.Item>
  for +eI: {its1 == its2 : +List<Spec.Item>}
  for +p1: +List<Nat>
  for +p2: +List<Nat>
  for +eP: {p1 == p2 : +List<Nat>}
  for +w: +List<Nat>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +ch: +List<Spec.Tree>
  for r: Spec.ExtentRival(grammar, guards, pmarks, marks, its2, own, index, p2, w, after, above, span, ch)
  Spec.ExtentRival(grammar, guards, pmarks, marks, its1, own, index, p1, w, after, above, span, ch)

def rival_tr(grammar, guards, pmarks, marks, own, index, its1, its2, eI, p1, p2, eP, w, after, above, span, ch, r):
  %Equal.sym(+List<Spec.Item>, its1, its2, eI) : Spec.ExtentRival(grammar, guards, pmarks, marks, _, own, index, p1, w, after, above, span, ch)
  %Equal.sym(+List<Nat>, p1, p2, eP) : Spec.ExtentRival(grammar, guards, pmarks, marks, its2, own, index, _, w, after, above, span, ch)
  r

law rival_loopy_m:
  for m: Ext.Marked
  for +ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +badM: {isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)) == isBad(m, True{}) : Bool}
  for +i: Nat
  for +k: Nat
  for +allK: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for r: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)
  Empty

def rival_loopy_m(m, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, index, rpath, prefix, pEq, mEq, badM, i, k, allK, r):
  match m:
    case Ext.NoMark{}:
      match r:
        case (f20, (fit20, (lv20, (bt0, hr)))):
          +S = Gll.seqAt(grammar, index, rpath)
          +P = Gll.reverseOnto(rpath, [])
          +f2 = {f20 : +List<Spec.Tree>}
          +h = Equal.cong(Ext.Marked, Bool, v => isNoMark(v), Mk(grammar, marks, index, rpath), Ext.NoMark{}, mEq)
          +m2 = measures_nomark(S, f2, marks, index, P, 0n, h)
          +m1 = measures_nomark(S, ch, marks, index, P, 0n, h)
          Lemma.false_is_not_true(Equal.trans(Bool, False{}, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), True{}, Equal.sym(Bool, Spec.beats(Spec.measures(marks, f2, S, index, P, 0n), Spec.measures(marks, ch, S, index, P, 0n)), False{}, Lemma_beats2(Spec.measures(marks, f2, S, index, P, 0n), [], Spec.measures(marks, ch, S, index, P, 0n), [], m2, m1)), bt0))
    case Ext.ManyMarks{}:
      bad_kept(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, badM, own_first_k(ch, index, prefix, i, k, Ext.extentKept(s, s, fuel, grammar, marks, input), allK))
    case Ext.OneMark{+d, +e}:
      bad_kept(fuel, grammar, marks, input, s, index, rpath, prefix, pEq, i, badM, own_first_k(ch, index, prefix, i, k, Ext.extentKept(s, s, fuel, grammar, marks, input), allK))

# Direction 1 in a round: the alternative of a loop has no rival.
law rival_loopy:
  for m: Ext.Marked
  for +ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == True{} : Bool}
  for +i: Nat
  for +k: Nat
  for +allK: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  for r: Rival(grammar, guards, pmarks, marks, index, rpath, own, after, above, span, ch)
  Empty

def rival_loopy(m, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, index, rpath, prefix, pEq, mEq, lEq, i, k, allK, r):
  +L = Ext.seqLoopy(rpath, grammar, index)
  +b1 = Equal.cong(Bool, Bool, w => isBad(Mk(grammar, marks, index, rpath), w), L, True{}, lEq)
  +b2 = Equal.cong(Ext.Marked, Bool, w => isBad(w, True{}), Mk(grammar, marks, index, rpath), m, mEq)
  +badM = Equal.trans(Bool, isBad(Mk(grammar, marks, index, rpath), L), isBad(Mk(grammar, marks, index, rpath), True{}), isBad(m, True{}), b1, b2)
  rival_loopy_m(m, ch, fuel, grammar, marks, guards, pmarks, own, after, above, span, input, s, index, rpath, prefix, pEq, mEq, badM, i, k, allK, r)

# Direction 2 in a round: the own steps of a loop's alternative are kept.
law owner_loopy:
  for m: Ext.Marked
  for +ch: +List<Spec.Tree>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +mEq: {Mk(grammar, marks, index, rpath) == m : Ext.Marked}
  for +lEq: {Ext.seqLoopy(rpath, grammar, index) == True{} : Bool}
  for +i: Nat
  for +k: Nat
  for +allS: {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), s) == True{} : Bool}
  {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def owner_loopy(m, ch, fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, mEq, lEq, i, k, allS):
  match m:
    case Ext.NoMark{}:
      nomark_iter(ch, 0n, k, fuel, grammar, marks, input, s, index, rpath, prefix, pEq, mEq, i, allS)
    case Ext.ManyMarks{}:
      goal = {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
      +bad = Equal.cong(Ext.Marked, Bool, w => isBad(w, Ext.seqLoopy(rpath, grammar, index)), Mk(grammar, marks, index, rpath), Ext.ManyMarks{}, mEq)
      Empty.absurd(goal, bad_known(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, i, bad, own_first_k(ch, index, prefix, i, k, s, allS)))
    case Ext.OneMark{+d, +ext}:
      goal = {Spec.allIn(PG.ownSteps(ch, index, prefix, 0n, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
      +b1 = Equal.cong(Ext.Marked, Bool, w => isBad(w, Ext.seqLoopy(rpath, grammar, index)), Mk(grammar, marks, index, rpath), Ext.OneMark{d, ext}, mEq)
      +b2 = Equal.cong(Bool, Bool, w => isBad(Ext.OneMark{d, ext}, w), Ext.seqLoopy(rpath, grammar, index), True{}, lEq)
      +bad = Equal.trans(Bool, isBad(Mk(grammar, marks, index, rpath), Ext.seqLoopy(rpath, grammar, index)), isBad(Ext.OneMark{d, ext}, Ext.seqLoopy(rpath, grammar, index)), True{}, b1, b2)
      Empty.absurd(goal, bad_known(fuel, grammar, marks, input, s, okK, index, rpath, prefix, pEq, i, bad, own_first_k(ch, index, prefix, i, k, s, allS)))

# The pruned set holds only steps of the set it was pruned from.
law sup_sub:
  for es: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Unb.supportedOf(es, set, grammar, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def sup_sub(es, set, grammar, input, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      ekept_sub_pick(Unb.supported(set, grammar, input, e), e, rest, Unb.supportedOf(rest, set, grammar, input), y, m,
        later => sup_sub(rest, set, grammar, input, y, later))

law grow_sub:
  for n: Nat
  for +es: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for sub: {Spec.bsrMember(y, set) == True{} : Bool} -> {Spec.bsrMember(y, es) == True{} : Bool}
  for m: {Spec.bsrMember(y, Unb.grow(n, es, set, grammar, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def grow_sub(n, es, set, grammar, input, y, sub, m):
  match n:
    case 0n:
      sub(m)
    case 1n+(+p):
      grow_sub(p, es, Unb.supportedOf(es, set, grammar, input), grammar, input, y, h => sup_sub(es, set, grammar, input, y, h), m)

law all_grow:
  for xs: +List<Spec.Bsr>
  for +es: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +all: {Spec.allIn(xs, Unb.grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input)) == True{} : Bool}
  {Spec.allIn(xs, es) == True{} : Bool}

def all_grow(xs, es, grammar, input, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +K = Unb.grow(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      +mr = Lemma.and_true_right_side(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      +inX = grow_sub(1n+List.length(&2, Spec.Bsr, es), es, [], grammar, input, x, h => Empty.absurd({Spec.bsrMember(x, es) == True{} : Bool}, G.ebnf_not_in_empty(x, h)), mx)
      %Equal.sym(Bool, Spec.bsrMember(x, es), True{}, inX) : {Bool.and(_, Spec.allIn(rest, es)) == True{} : Bool}
      %Equal.sym(Bool, Spec.allIn(rest, es), True{}, all_grow(rest, es, grammar, input, mr)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# ======== DIRECTION 1: WHERE A RIVAL'S STEPS ARE ========

# The innermost frame of the zipper is not a loop's: its hole is a node's or a pick's
# children (or the root's).
def innerOk(z: +List<Plug.Frame>) -> Bool:
  match z:
    case Nil{}:
      True{}
    case Con{Plug.NodeKid{l, q, r}, rest}:
      True{}
    case Con{Plug.PickKid{l, a, r}, rest}:
      True{}
    case Con{Plug.LoopKid{l, r}, rest}:
      False{}

# Such a hole asks the same of every forest that may take its place.
law hole_indep:
  for +z: +List<Plug.Frame>
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +nl: {innerOk(z) == True{} : Bool}
  {Plug.holeOf(grammar, q0, z, y2) == Plug.holeOf(grammar, q0, z, y) : +List<Spec.Item>}

def hole_indep(z, grammar, q0, y, y2, nl):
  match z:
    case Nil{}:
      {==}
    case Con{+fr, +rest}:
      match fr:
        case Plug.NodeKid{+l, +q, +r}:
          {==}
        case Plug.PickKid{+l, +a, +r}:
          +fr2 = {Plug.PickKid{l, a, r} : Plug.Frame}
          +hEq = Plug.holeof_len(rest, grammar, q0, Plug.fill(fr2, y), Plug.fill(fr2, y2), Plug.fill_len(fr2, y, y2))
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeAt(grammar, fr2, Plug.itemAtOr(v, List.length(&2, Spec.Tree, l)), y2), Plug.holeOf(grammar, q0, rest, Plug.fill(fr2, y2)), Plug.holeOf(grammar, q0, rest, Plug.fill(fr2, y)), hEq)
        case Plug.LoopKid{+l, +r}:
          Empty.absurd({Plug.holeOf(grammar, q0, Plug.LoopKid{l, r} <> rest, y2) == Plug.holeOf(grammar, q0, Plug.LoopKid{l, r} <> rest, y) : +List<Spec.Item>}, Lemma.false_is_not_true(nl))

law shape_ok:
  for +z: +List<Plug.Frame>
  for +y: +List<Spec.Tree>
  for +y2: +List<Spec.Tree>
  for +nl: {innerOk(z) == True{} : Bool}
  {Plug.zshape(z, y, y2) == True{} : Bool}

def shape_ok(z, y, y2, nl):
  match z:
    case Nil{}:
      {==}
    case Con{+fr, +rest}:
      match fr:
        case Plug.NodeKid{+l, +q, +r}:
          {==}
        case Plug.PickKid{+l, +a, +r}:
          {==}
        case Plug.LoopKid{+l, +r}:
          Empty.absurd({Plug.zshape(Plug.LoopKid{l, r} <> rest, y, y2) == True{} : Bool}, Lemma.false_is_not_true(nl))

# Facts at a hole, moved along an equal place.
law at_hold:
  for +grammar: +List<Spec.Production>
  for +c: Plug.Ctx
  for +c2: Plug.Ctx
  for +e: {c2 == c : Plug.Ctx}
  for +y: +List<Spec.Tree>
  for h: Plug.HoldAt(grammar, c2, y)
  Plug.HoldAt(grammar, c, y)

def at_hold(grammar, c, c2, e, y, h):
  %e : Plug.HoldAt(grammar, _, y)
  h

law at_adm:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +c: Plug.Ctx
  for +c2: Plug.Ctx
  for +e: {c2 == c : Plug.Ctx}
  for +y: +List<Spec.Tree>
  for h: Plug.AdmAt(grammar, guards, c2, y)
  Plug.AdmAt(grammar, guards, c, y)

def at_adm(grammar, guards, c, c2, e, y, h):
  %e : Plug.AdmAt(grammar, guards, _, y)
  h

law at_unb:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +c: Plug.Ctx
  for +c2: Plug.Ctx
  for +e: {c2 == c : Plug.Ctx}
  for +y: +List<Spec.Tree>
  for h: Plug.UnbAt(grammar, guards, pmarks, c2, y)
  Plug.UnbAt(grammar, guards, pmarks, c, y)

def at_unb(grammar, guards, pmarks, c, c2, e, y, h):
  %e : Plug.UnbAt(grammar, guards, pmarks, _, y)
  h

# The rival's rules read its tokens, which are the children's.
law hold_leaves:
  for +grammar: +List<Spec.Production>
  for +own: +List<Spec.Guard>
  for +items: +List<Spec.Item>
  for +f2: +List<Spec.Tree>
  for +ch: +List<Spec.Tree>
  for +after: +List<Nat>
  for +lv: {Spec.leaves(f2) == Spec.leaves(ch) : +List<Nat>}
  for h: Spec.AllHold(grammar, own, items, f2, List.append(&2, Nat, Spec.leaves(ch), after))
  Spec.AllHold(grammar, own, items, f2, List.append(&2, Nat, Spec.leaves(f2), after))

def hold_leaves(grammar, own, items, f2, ch, after, lv, h):
  %Equal.sym(+List<Nat>, Spec.leaves(f2), Spec.leaves(ch), lv) : Spec.AllHold(grammar, own, items, f2, List.append(&2, Nat, _, after))
  h

# The two halves of the preference oracle's law, for one tree.
law whole_mk:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +t: Spec.Tree
  for +fitT: {Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([t]) == input : +List<Nat>}
  for au: Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  Spec.UnbeatenTree(grammar, guards, pmarks, start, input, t)

def whole_mk(grammar, guards, pmarks, start, input, t, fitT, lvT, au):
  match au:
    case (a, u):
      ((fitT, (lvT, a)), u)

law whole_of:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +t: Spec.Tree
  for +fitT: {Spec.fits([t], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([t]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool}
  for both: ({Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool} -> Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])) & (Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool})
  Spec.UnbeatenTree(grammar, guards, pmarks, start, input, t)

def whole_of(grammar, guards, pmarks, start, input, set, t, fitT, lvT, inT, both):
  match both:
    case (to, frm):
      whole_mk(grammar, guards, pmarks, start, input, t, fitT, lvT, to(inT))

law back_of:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +start: Nat
  for +set: +List<Spec.Bsr>
  for +t: Spec.Tree
  for both: ({Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool} -> Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])) & (Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool})
  for a: Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [])
  for u: Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool}

def back_of(grammar, guards, pmarks, start, set, t, both, a, u):
  match both:
    case (to, frm):
      frm((a, u))

# A RIVAL TAKES THE CHILDREN'S PLACE. At a hole of the tree that is a node's or a pick's
# children, a forest that reads the same tokens and that phases 1 and 2 keep there takes
# their place in an unbeaten tree (PROOF_PLUG.bend), so its steps are in the preference
# oracle's set, and, pruned from below, in the extent oracle's.
law plug_in:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +U: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +q0: Nat
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +z: +List<Plug.Frame>
  for +ch: +List<Spec.Tree>
  for +own: +List<Spec.Guard>
  for +index: Nat
  for +rpath: +List<Nat>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +k: Nat
  for +nl: {innerOk(z) == True{} : Bool}
  for +okZ: {Plug.zipOk(grammar, q0, z, ch) == True{} : Bool}
  for +ctxE: {Plug.ctxOf(grammar, guards, start, q0, z, ch) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, Gll.reverseOnto(rpath, []), above, span, after} : Plug.Ctx}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, Gll.reverseOnto(rpath, []), 0n, k, k} : Plug.Coord}
  for +holeE: {Plug.holeOf(grammar, q0, z, ch) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +posCh: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, ch)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, ch)}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, ch)}, 0n), U) == True{} : Bool}
  RivalIn(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, k, s)

def plug_in(grammar, guards, pmarks, start, input, fuel, U, s, q0, gotU, closed, z, ch, own, index, rpath, after, above, span, k, nl, okZ, ctxE, coE, holeE, posCh, fitT, lvT, inT):
  +f2 => +fit2 => +lv2 => hold => adm => unb =>
    +P = Gll.reverseOnto(rpath, [])
    +S = Gll.seqAt(grammar, index, rpath)
    +sc = {Plug.SeqCtx{own, S, index, P, above, span, after} : Plug.Ctx}
    +c = Plug.ctxOf(grammar, guards, start, q0, z, ch)
    +ecs = Equal.sym(Plug.Ctx, c, sc, ctxE)
    +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, f2), Plug.holeOf(grammar, q0, z, ch), S, hole_indep(z, grammar, q0, ch, f2, nl), holeE)
    +fitH = Equal.trans(Bool, Spec.fits(f2, grammar, Plug.holeOf(grammar, q0, z, f2)), Spec.fits(f2, grammar, S), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), Plug.holeOf(grammar, q0, z, f2), S, hE2), fit2)
    +t = {Spec.Node{q0, Plug.zip(z, ch)} : Spec.Tree}
    whole = whole_of(grammar, guards, pmarks, start, input, U, t, fitT, lvT, inT, Laws.prefer_avoid_exact(fuel, grammar, guards, pmarks, start, input, U, gotU)(t, fitT, lvT))
    +inU = Plug.plug_rival(z, ch, f2, grammar, guards, pmarks, start, q0, input, U, okZ, fitH, lv2, shape_ok(z, ch, f2, nl),
      at_hold(grammar, c, sc, ecs, f2, hold_leaves(grammar, own, S, f2, ch, after, lv2, hold)), at_adm(grammar, guards, c, sc, ecs, f2, adm), at_unb(grammar, guards, pmarks, c, sc, ecs, f2, unb), whole,
      (+t2 => +ft => +lt => a => u => back_of(grammar, guards, pmarks, start, U, t2, Laws.prefer_avoid_exact(fuel, grammar, guards, pmarks, start, input, U, gotU)(t2, ft, lt), a, u)))
    +inU2 = Equal.trans(Bool, Spec.allIn(Spec.walk(f2, False{}, index, P, 0n, k, k), U), Spec.allIn(Plug.walkAt(Plug.coordOf(q0, z), f2), U), True{}, Equal.cong(Plug.Coord, Bool, v => Spec.allIn(Plug.walkAt(v, f2), U), Plug.Coord{False{}, index, P, 0n, k, k}, Plug.coordOf(q0, z), Equal.sym(Plug.Coord, Plug.coordOf(q0, z), Plug.Coord{False{}, index, P, 0n, k, k}, coE)), inU)
    +pos2 = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f2), after), List.append(&2, Nat, Spec.leaves(ch), after), Lemma.dropN(k, input), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f2), Spec.leaves(ch), lv2), posCh)
    +bef = Lemma.or_true_left_intro(Nat.is_eq(k, k), Unb.roundBefore(rpath, s, grammar, index, k, k), Lemma.nat_eq_refl(k))
    +inS = Sup.sw_walk(f2, False{}, grammar, input, U, s, closed, index, rpath, P, 0n, k, k, S, Spec.Group{}, [], after, {==}, pos2, ({==}, (fit2, (inU2, bef))))
    PG.own_sub(f2, index, P, 0n, k, k, s, inS)

# ======== DIRECTION 1: A TREE OF KEPT STEPS IS BEST ========
#
# The walk knows where it stands in the tree: the zipper z to the sequence it walks, the
# trees L of that sequence before the forest, and where the sequence starts (k0). So at
# every node and pick it can set a rival in the children's place (plug_in).

def EAdmReady(rounds: Bool, +grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}, +U: +List<Spec.Bsr>, +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}, +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}, +q0: Nat, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>, +own: +List<Spec.Guard>, +z: +List<Plug.Frame>, +L: +List<Spec.Tree>, +k0: Nat) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool} & {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Plug.dotAfter(L, 0n) == dot : Nat} & {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, forest)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx} & {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, forest)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool} & {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, forest)) == Plug.RoundCtx{alts, index, prefix, above, span, after} : Plug.Ctx} & {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, forest)) == Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, forest)), Spec.Brack{Spec.Group{}, alts}) : +List<Spec.Item>}

def EAdmDone(rounds: Bool, +grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +forest: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>, +above: +List<Nat>, +span: +List<Nat>, +after: +List<Nat>) -> Type:
  match rounds:
    case False{}:
      Spec.ExtentBest(grammar, guards, pmarks, marks, forest, items, index, prefix, dot, above, span, after)
    case True{}:
      Spec.RoundsBest(grammar, guards, pmarks, marks, forest, alts, index, prefix, above, span, after)

def EAdmIH(+grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}, +U: +List<Spec.Bsr>, +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}, +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}, +q0: Nat, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @after: +List<Nat> -> @above: +List<Nat> -> @span: +List<Nat> -> @own: +List<Spec.Guard> -> @z: +List<Plug.Frame> -> @L: +List<Spec.Tree> -> @k0: Nat ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> {Plug.coordOf(q0, z) == Plug.Coord{rounds, index, prefix, 0n, i, k0} : Plug.Coord} -> {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat} ->
    {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool} -> {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}]) == input : +List<Nat>} -> {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}, 0n), U) == True{} : Bool} ->
    EAdmReady(rounds, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0) -> EAdmDone(rounds, grammar, guards, pmarks, marks, forest, items, index, prefix, dot, alts, above, span, after)

# The root's children fit its production.
law top_fit:
  for +grammar: +List<Spec.Production>
  for +q0: Nat
  for +start: Nat
  for +ch: +List<Spec.Tree>
  for +fitT: {Spec.fits([Spec.Node{q0, ch}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q0)) == True{} : Bool}

def top_fit(grammar, q0, start, ch, fitT):
  Lemma.and_true_right_side(Spec.lhsIs(grammar, q0, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q0)), Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q0, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q0))), True{}, fitT))

# An item read in a loop's rounds is a round.
law times_at:
  for n: Nat
  for +it: Spec.Item
  for j: Nat
  for +lt: {Nat.is_lt(j, n) == True{} : Bool}
  {Plug.itemAtOr(Spec.times(n, it), j) == it : Spec.Item}

def times_at(n, it, j, lt):
  match n j:
    case 0n _:
      Empty.absurd({Plug.itemAtOr([], j) == it : Spec.Item}, Lemma.lt_zero_false(j, lt))
    case 1n+m 0n:
      {==}
    case 1n+m 1n+jj:
      times_at(m, it, jj, lt)

law len_before:
  for l: +List<Spec.Tree>
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {Nat.is_lt(List.length(&2, Spec.Tree, l), List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, l, t <> ts))) == True{} : Bool}

def len_before(l, t, ts):
  match l:
    case Nil{}:
      {==}
    case Con{+u, +l2}:
      len_before(l2, t, ts)
law best_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +kd: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Leaf{kd} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Leaf{kd} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihTs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ts)
  EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after)

def best_leaf(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, kd, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{kd} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{kd} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +fitTs = Fits.fits_tail(Spec.Leaf{kd}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), Ext.extentKept(s, s, fuel, grammar, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +posTs = PG.pos_tail(Spec.Leaf{kd}, ts, after, input, k, pos)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), k0, pEq, posTs, coE, Equal.trans(Nat, 1n+k, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Leaf{kd}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}])))), Sub.end_of_one(Spec.Leaf{kd}, k), Plug.k_snoc(L, Spec.Leaf{kd}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts), List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts), Plug.app_snoc(L, Spec.Leaf{kd}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts), List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts), Plug.app_snoc(L, Spec.Leaf{kd}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts), List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts), Plug.app_snoc(L, Spec.Leaf{kd}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Leaf{kd}, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Leaf{kd}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts), List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts), Plug.app_snoc(L, Spec.Leaf{kd}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Leaf{kd}]), ts), List.append(&2, Spec.Tree, L, Spec.Leaf{kd} <> ts), Plug.app_snoc(L, Spec.Leaf{kd}, ts)), hE))))))))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law best_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Skip{} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihTs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ts)
  EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after)

def best_skip(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +posTs = PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), k0, pEq, posTs, coE, Equal.trans(Nat, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Skip{}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Skip{}])))), Sub.end_of_one(Spec.Skip{}, k), Plug.k_snoc(L, Spec.Skip{}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Skip{}, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Skip{}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Skip{}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), hE))))))))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Skip{} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +allTs = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input), allW)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +posTs = PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos)
          ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), k0, pEq, posTs, coE, Equal.trans(Nat, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Skip{}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Skip{}])))), Sub.end_of_one(Spec.Skip{}, k), Plug.k_snoc(L, Spec.Skip{}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Skip{}, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Skip{}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Skip{}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Skip{}]), ts), List.append(&2, Spec.Tree, L, Spec.Skip{} <> ts), Plug.app_snoc(L, Spec.Skip{}, ts)), hE))))))))

law best_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihCh: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ch)
  for ihTs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ts)
  EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after)

def best_node(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, q, ch, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
          +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
          +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.NodeKid{L, q, ts} <> z, ch), Plug.holeCtx(grammar, guards, Plug.NodeKid{L, q, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ch), Plug.SeqCtx{Spec.prodGuards(guards, q), Gll.seqAt(grammar, q, []), q, [], x <> Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.NodeKid{L, q, ts}, v, ch), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ctxE), Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.nodeCtx(grammar, guards, q, v, above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)), Spec.Sym{Spec.Nonterminal{x}} <> rest, iE))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.NodeKid{L, q, ts} <> z), Plug.holeCoord(Plug.NodeKid{L, q, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, q, [], 0n, k, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.NodeKid{L, q, ts}, v), Plug.coordOf(q0, z), Plug.Coord{False{}, index, prefix, 0n, i, k0}, coE), Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, q, [], 0n, v, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          +okZ = Plug.unzip_ok(Plug.NodeKid{L, q, ts} <> z, ch, grammar, q0, top_fit(grammar, q0, start, Plug.zip(Plug.NodeKid{L, q, ts} <> z, ch), fitT))
          plugIn = plug_in(grammar, guards, pmarks, start, input, fuel, U, s, q0, gotU, closed, Plug.NodeKid{L, q, ts} <> z, ch, Spec.prodGuards(guards, q), q, [], next, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), w, k, {==}, okZ, ctxE2, coE2, {==}, posCh, fitT, lvT, inT)
          (r => rival_m(Mk(grammar, marks, q, []), Ext.seqLoopy([], grammar, q), ch, fuel, grammar, marks, guards, pmarks, Spec.prodGuards(guards, q), next, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), w, input, s, okC, q, [], [], {==}, {==}, {==}, k, next, posCh, fitCh, PG.own_sub(ch, q, [], 0n, k, k, kept, allCh), plugIn, r),
            (ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, next, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), w, Spec.prodGuards(guards, q), Plug.NodeKid{L, q, ts} <> z, [], k, {==}, posCh, coE2, kE2, fitT, lvT, inT, ({==}, (fitCh, (allCh, ({==}, ({==}, (ctxE2, {==}))))))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), k0, pEq, posTs, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Node{q, ch}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}])))), Sub.end_of_one(Spec.Node{q, ch}, k), Plug.k_snoc(L, Spec.Node{q, ch}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts), Plug.app_snoc(L, Spec.Node{q, ch}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts), Plug.app_snoc(L, Spec.Node{q, ch}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts), Plug.app_snoc(L, Spec.Node{q, ch}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Node{q, ch}, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Node{q, ch}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts), Plug.app_snoc(L, Spec.Node{q, ch}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Node{q, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Node{q, ch} <> ts), Plug.app_snoc(L, Spec.Node{q, ch}, ts)), hE))))))))))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law best_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihCh: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ch)
  for ihTs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ts)
  EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after)

def best_pick(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, a, ch, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
          +rpA = {a <> dot <> rpath : +List<Nat>}
          +fitCh2 = Equal.trans(Bool, Spec.fits(ch, grammar, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ch, grammar, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), itemsEq2), fitCh)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, v, ch), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ctxE), Equal.trans(Plug.Ctx, Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ch), Plug.pickCtx(grammar, guards, a, Spec.Brack{Spec.Group{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.pickCtx(grammar, guards, a, v, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Group{}, balts} <> rest, iE), Equal.trans(Plug.Ctx, Plug.pickCtx(grammar, guards, a, Spec.Brack{Spec.Group{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.SeqCtx{Spec.altGuards(guards, index, List.append(&2, Nat, prefix, [dot]), a), Spec.altOf(balts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Nat, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, List.append(&2, Nat, prefix, [v]), a), Spec.altOf(balts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [v]), [a]), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.dotAfter(L, 0n), dot, dE), Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, path, a), v, index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Spec.altOf(balts, a), Gll.seqAt(grammar, index, rpA), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(balts, a), itemsEq2)))))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.PickKid{L, a, ts} <> z), Plug.holeCoord(Plug.PickKid{L, a, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.PickKid{L, a, ts}, v), Plug.coordOf(q0, z), Plug.Coord{False{}, index, prefix, 0n, i, k0}, coE), Equal.trans(Plug.Coord, Plug.holeCoord(Plug.PickKid{L, a, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [v, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, List.length(&2, Spec.Tree, L), dot, Equal.trans(Nat, List.length(&2, Spec.Tree, L), Plug.dotAfter(L, 0n), dot, Equal.sym(Nat, Plug.dotAfter(L, 0n), List.length(&2, Spec.Tree, L), Plug.da_len(L, 0n)), dE)), Equal.trans(Plug.Coord, Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k}, Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, v, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE)), Equal.cong(+List<Nat>, Plug.Coord, v => Plug.Coord{False{}, index, v, 0n, k, k}, List.append(&2, Nat, prefix, [dot, a]), pre2, Equal.sym(+List<Nat>, pre2, List.append(&2, Nat, prefix, [dot, a]), assoc)))))
          +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, Gll.seqAt(grammar, index, rpath), ch), Gll.seqAt(grammar, index, rpA), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, v, ch), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Gll.seqAt(grammar, index, rpath), hE), Equal.trans(+List<Spec.Item>, Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, Gll.seqAt(grammar, index, rpath), ch), Spec.altOf(balts, a), Gll.seqAt(grammar, index, rpA), Equal.cong(Spec.Item, +List<Spec.Item>, v => Gll.bracketAlt(Some{v}, a), Plug.itemAtOr(Gll.seqAt(grammar, index, rpath), List.length(&2, Spec.Tree, L)), Spec.Brack{Spec.Group{}, balts}, Plug.ia_at(L, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, iE)), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(balts, a), itemsEq2)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          +okZ = Plug.unzip_ok(Plug.PickKid{L, a, ts} <> z, ch, grammar, q0, top_fit(grammar, q0, start, Plug.zip(Plug.PickKid{L, a, ts} <> z, ch), fitT))
          plugIn = plug_in(grammar, guards, pmarks, start, input, fuel, U, s, q0, gotU, closed, Plug.PickKid{L, a, ts} <> z, ch, Spec.altGuards(guards, index, path, a), index, rpA, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, k, {==}, okZ, Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, Gll.reverseOnto(rpA, []), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, ctxE2, Equal.cong(+List<Nat>, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, v, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, pre2, Gll.reverseOnto(rpA, []), pEq2)), Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.PickKid{L, a, ts} <> z), Plug.Coord{False{}, index, pre2, 0n, k, k}, Plug.Coord{False{}, index, Gll.reverseOnto(rpA, []), 0n, k, k}, coE2, Equal.cong(+List<Nat>, Plug.Coord, v => Plug.Coord{False{}, index, v, 0n, k, k}, pre2, Gll.reverseOnto(rpA, []), pEq2)), hE2, posCh, fitT, lvT, inT)
          (r => rival_m(Mk(grammar, marks, index, rpA), Ext.seqLoopy(rpA, grammar, index), ch, fuel, grammar, marks, guards, pmarks, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, input, s, okC, index, rpA, pre2, pEq2, {==}, {==}, k, next, posCh, fitCh2, PG.own_sub(ch, index, pre2, 0n, k, k, kept, allCh2), plugIn, rival_tr(grammar, guards, pmarks, marks, Spec.altGuards(guards, index, path, a), index, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), itemsEq2, Gll.reverseOnto(rpath, [dot, a]), pre2, Equal.sym(+List<Nat>, pre2, Gll.reverseOnto(rpath, [dot, a]), pEq2), w, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, ch, r)),
            (ihCh(False{}, index, rpA, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, Spec.altGuards(guards, index, path, a), Plug.PickKid{L, a, ts} <> z, [], k, pEq2, posCh, coE2, kE2, fitT, lvT, inT, (itemsEq2, (fitCh, (allCh2, (itemsEq2, ({==}, (ctxE2, hE2))))))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), k0, pEq, posTs, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}])))), Sub.end_of_one(Spec.Pick{a, ch}, k), Plug.k_snoc(L, Spec.Pick{a, ch}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Pick{a, ch}, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Pick{a, ch}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), hE))))))))))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +w = Spec.leaves(ch)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
          +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +pre = List.append(&2, Nat, prefix, [dot, a])
          +path = List.append(&2, Nat, prefix, [dot])
          +pre2 = List.append(&2, Nat, path, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wCh, wTs), kept, allW)
          +allCh = R.in_app_left(wCh, wTs, kept, allIn2)
          +allTs = R.in_app_right(wCh, wTs, kept, allIn2)
          +posCh = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +assoc = G.nat_append_assoc(prefix, [dot], [a])
          +allCh2 = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, pre2, 0n, k, k), kept), Spec.allIn(wCh, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre2, pre, assoc), allCh)
          +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
          +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
          +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
          +rpA = {a <> dot <> rpath : +List<Nat>}
          +fitCh2 = Equal.trans(Bool, Spec.fits(ch, grammar, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ch, grammar, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), itemsEq2), fitCh)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, v, ch), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ctxE), Equal.trans(Plug.Ctx, Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ch), Plug.pickCtx(grammar, guards, a, Spec.Brack{Spec.Optional{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.pickCtx(grammar, guards, a, v, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Optional{}, balts} <> rest, iE), Equal.trans(Plug.Ctx, Plug.pickCtx(grammar, guards, a, Spec.Brack{Spec.Optional{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after), ch), Plug.SeqCtx{Spec.altGuards(guards, index, List.append(&2, Nat, prefix, [dot]), a), Spec.altOf(balts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Nat, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, List.append(&2, Nat, prefix, [v]), a), Spec.altOf(balts, a), index, List.append(&2, Nat, List.append(&2, Nat, prefix, [v]), [a]), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.dotAfter(L, 0n), dot, dE), Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, path, a), v, index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Spec.altOf(balts, a), Gll.seqAt(grammar, index, rpA), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(balts, a), itemsEq2)))))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.PickKid{L, a, ts} <> z), Plug.holeCoord(Plug.PickKid{L, a, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.PickKid{L, a, ts}, v), Plug.coordOf(q0, z), Plug.Coord{False{}, index, prefix, 0n, i, k0}, coE), Equal.trans(Plug.Coord, Plug.holeCoord(Plug.PickKid{L, a, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [v, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, List.length(&2, Spec.Tree, L), dot, Equal.trans(Nat, List.length(&2, Spec.Tree, L), Plug.dotAfter(L, 0n), dot, Equal.sym(Nat, Plug.dotAfter(L, 0n), List.length(&2, Spec.Tree, L), Plug.da_len(L, 0n)), dE)), Equal.trans(Plug.Coord, Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k}, Plug.Coord{False{}, index, pre2, 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, v, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE)), Equal.cong(+List<Nat>, Plug.Coord, v => Plug.Coord{False{}, index, v, 0n, k, k}, List.append(&2, Nat, prefix, [dot, a]), pre2, Equal.sym(+List<Nat>, pre2, List.append(&2, Nat, prefix, [dot, a]), assoc)))))
          +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, Gll.seqAt(grammar, index, rpath), ch), Gll.seqAt(grammar, index, rpA), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, v, ch), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Gll.seqAt(grammar, index, rpath), hE), Equal.trans(+List<Spec.Item>, Plug.holeItems(grammar, Plug.PickKid{L, a, ts}, Gll.seqAt(grammar, index, rpath), ch), Spec.altOf(balts, a), Gll.seqAt(grammar, index, rpA), Equal.cong(Spec.Item, +List<Spec.Item>, v => Gll.bracketAlt(Some{v}, a), Plug.itemAtOr(Gll.seqAt(grammar, index, rpath), List.length(&2, Spec.Tree, L)), Spec.Brack{Spec.Optional{}, balts}, Plug.ia_at(L, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, iE)), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(balts, a), itemsEq2)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          +okZ = Plug.unzip_ok(Plug.PickKid{L, a, ts} <> z, ch, grammar, q0, top_fit(grammar, q0, start, Plug.zip(Plug.PickKid{L, a, ts} <> z, ch), fitT))
          plugIn = plug_in(grammar, guards, pmarks, start, input, fuel, U, s, q0, gotU, closed, Plug.PickKid{L, a, ts} <> z, ch, Spec.altGuards(guards, index, path, a), index, rpA, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, k, {==}, okZ, Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.PickKid{L, a, ts} <> z, ch), Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, pre2, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, Gll.reverseOnto(rpA, []), Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, ctxE2, Equal.cong(+List<Nat>, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, path, a), Gll.seqAt(grammar, index, rpA), index, v, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ts), after)}, pre2, Gll.reverseOnto(rpA, []), pEq2)), Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.PickKid{L, a, ts} <> z), Plug.Coord{False{}, index, pre2, 0n, k, k}, Plug.Coord{False{}, index, Gll.reverseOnto(rpA, []), 0n, k, k}, coE2, Equal.cong(+List<Nat>, Plug.Coord, v => Plug.Coord{False{}, index, v, 0n, k, k}, pre2, Gll.reverseOnto(rpA, []), pEq2)), hE2, posCh, fitT, lvT, inT)
          (r => rival_m(Mk(grammar, marks, index, rpA), Ext.seqLoopy(rpA, grammar, index), ch, fuel, grammar, marks, guards, pmarks, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, input, s, okC, index, rpA, pre2, pEq2, {==}, {==}, k, next, posCh, fitCh2, PG.own_sub(ch, index, pre2, 0n, k, k, kept, allCh2), plugIn, rival_tr(grammar, guards, pmarks, marks, Spec.altGuards(guards, index, path, a), index, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), itemsEq2, Gll.reverseOnto(rpath, [dot, a]), pre2, Equal.sym(+List<Nat>, pre2, Gll.reverseOnto(rpath, [dot, a]), pEq2), w, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, ch, r)),
            (ihCh(False{}, index, rpA, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, Spec.altGuards(guards, index, path, a), Plug.PickKid{L, a, ts} <> z, [], k, pEq2, posCh, coE2, kE2, fitT, lvT, inT, (itemsEq2, (fitCh, (allCh2, (itemsEq2, ({==}, (ctxE2, hE2))))))),
              ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), k0, pEq, posTs, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}])))), Sub.end_of_one(Spec.Pick{a, ch}, k), Plug.k_snoc(L, Spec.Pick{a, ch}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Pick{a, ch}, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Pick{a, ch}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), ts), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> ts), Plug.app_snoc(L, Spec.Pick{a, ch}, ts)), hE))))))))))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law best_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{False{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihRs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, rs)
  for ihTs: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ts)
  EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after)

def best_loop(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, rs, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wRs, wTs), kept, allW)
          +allRs = R.in_app_left(wRs, wTs, kept, allIn2)
          +allTs = R.in_app_right(wRs, wTs, kept, allIn2)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.LoopKid{L, ts} <> z, rs), Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, rs), Plug.RoundCtx{balts, index, path, above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, v, rs), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ctxE), Equal.trans(Plug.Ctx, Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, rs), Plug.loopCtx(Spec.Brack{Spec.Closure{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)), Plug.RoundCtx{balts, index, path, above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.loopCtx(v, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)), Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Closure{}, balts} <> rest, iE), Equal.cong(Nat, Plug.Ctx, v => Plug.RoundCtx{balts, index, List.append(&2, Nat, prefix, [v]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.dotAfter(L, 0n), dot, dE)))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.LoopKid{L, ts} <> z), Plug.holeCoord(Plug.LoopKid{L, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.LoopKid{L, ts}, v), Plug.coordOf(q0, z), Plug.Coord{False{}, index, prefix, 0n, i, k0}, coE), Equal.trans(Plug.Coord, Plug.holeCoord(Plug.LoopKid{L, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [v]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, List.length(&2, Spec.Tree, L), dot, Equal.trans(Nat, List.length(&2, Spec.Tree, L), Plug.dotAfter(L, 0n), dot, Equal.sym(Nat, Plug.dotAfter(L, 0n), List.length(&2, Spec.Tree, L), Plug.da_len(L, 0n)), dE)), Equal.cong(Nat, Plug.Coord, v => Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, v, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE))))
          +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, Plug.LoopKid{L, ts} <> z, rs), Plug.holeItems(grammar, Plug.LoopKid{L, ts}, Gll.seqAt(grammar, index, rpath), rs), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeItems(grammar, Plug.LoopKid{L, ts}, v, rs), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Gll.seqAt(grammar, index, rpath), hE), Equal.cong(Spec.Item, +List<Spec.Item>, v => Plug.loopItems(v, List.length(&2, Spec.Tree, rs)), Plug.itemAtOr(Gll.seqAt(grammar, index, rpath), List.length(&2, Spec.Tree, L)), Spec.Brack{Spec.Closure{}, balts}, Plug.ia_at(L, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, iE)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, next, above, span, own, Plug.LoopKid{L, ts} <> z, [], k, pEqL, posRs, coE2, kE2, fitT, lvT, inT, (itemEq, ({==}, (fitRs, (allRs, (ctxE2, hE2)))))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), k0, pEq, posTs, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Loop{rs}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Loop{rs}])))), Sub.end_of_one(Spec.Loop{rs}, k), Plug.k_snoc(L, Spec.Loop{rs}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Loop{rs}, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Loop{rs}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), hE)))))))))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (iE0, (dE0, (ctxE0, hE0)))))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +iE = {iE0 : {Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +dE = {dE0 : {Plug.dotAfter(L, 0n) == dot : Nat}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)) == Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}}
          +w = Spec.leaves(rs)
          +lts = Spec.leaves(ts)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lts, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
          +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
          +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
          +path = List.append(&2, Nat, prefix, [dot])
          +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
          +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
          +allIn2 = R.in_tail(Spec.at(index, prefix, 1n+dot, i, k, end), List.append(&2, Spec.Bsr, wRs, wTs), kept, allW)
          +allRs = R.in_app_left(wRs, wTs, kept, allIn2)
          +allTs = R.in_app_right(wRs, wTs, kept, allIn2)
          +posRs = PG.pos_children(w, lts, after, input, k, pos)
          +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.LoopKid{L, ts} <> z, rs), Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, rs), Plug.RoundCtx{balts, index, path, above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, v, rs), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, ctxE), Equal.trans(Plug.Ctx, Plug.holeCtx(grammar, guards, Plug.LoopKid{L, ts}, Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, rs), Plug.loopCtx(Spec.Brack{Spec.Positive{}, balts} <> rest, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)), Plug.RoundCtx{balts, index, path, above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.loopCtx(v, index, List.append(&2, Nat, prefix, [Plug.dotAfter(L, 0n)]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)), Plug.itemsAfter(L, Gll.seqAt(grammar, index, rpath)), Spec.Brack{Spec.Positive{}, balts} <> rest, iE), Equal.cong(Nat, Plug.Ctx, v => Plug.RoundCtx{balts, index, List.append(&2, Nat, prefix, [v]), above, span, List.append(&2, Nat, Spec.leaves(ts), after)}, Plug.dotAfter(L, 0n), dot, dE)))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.LoopKid{L, ts} <> z), Plug.holeCoord(Plug.LoopKid{L, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.LoopKid{L, ts}, v), Plug.coordOf(q0, z), Plug.Coord{False{}, index, prefix, 0n, i, k0}, coE), Equal.trans(Plug.Coord, Plug.holeCoord(Plug.LoopKid{L, ts}, Plug.Coord{False{}, index, prefix, 0n, i, k0}), Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k}, Equal.cong(Nat, Plug.Coord, v => Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [v]), 0n, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(L)))}, List.length(&2, Spec.Tree, L), dot, Equal.trans(Nat, List.length(&2, Spec.Tree, L), Plug.dotAfter(L, 0n), dot, Equal.sym(Nat, Plug.dotAfter(L, 0n), List.length(&2, Spec.Tree, L), Plug.da_len(L, 0n)), dE)), Equal.cong(Nat, Plug.Coord, v => Plug.Coord{True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, v, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE))))
          +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, Plug.LoopKid{L, ts} <> z, rs), Plug.holeItems(grammar, Plug.LoopKid{L, ts}, Gll.seqAt(grammar, index, rpath), rs), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeItems(grammar, Plug.LoopKid{L, ts}, v, rs), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Gll.seqAt(grammar, index, rpath), hE), Equal.cong(Spec.Item, +List<Spec.Item>, v => Plug.loopItems(v, List.length(&2, Spec.Tree, rs)), Plug.itemAtOr(Gll.seqAt(grammar, index, rpath), List.length(&2, Spec.Tree, L)), Spec.Brack{Spec.Positive{}, balts}, Plug.ia_at(L, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, iE)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          (ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, next, above, span, own, Plug.LoopKid{L, ts} <> z, [], k, pEqL, posRs, coE2, kE2, fitT, lvT, inT, (itemEq, ({==}, (fitRs, (allRs, (ctxE2, hE2)))))),
            ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), k0, pEq, posTs, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Loop{rs}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Loop{rs}])))), Sub.end_of_one(Spec.Loop{rs}, k), Plug.k_snoc(L, Spec.Loop{rs}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), inT), (restEq, (fitTs, (allTs, (Plug.ia_snoc(L, Spec.Loop{rs}, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, iE), (Equal.trans(Nat, Plug.dotAfter(List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), 0n), 1n+Plug.dotAfter(L, 0n), 1n+dot, Plug.da_snoc(L, Spec.Loop{rs}, 0n), Equal.cong(Nat, Nat, v => 1n+v, Plug.dotAfter(L, 0n), dot, dE)), (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Plug.SeqCtx{own, Gll.seqAt(grammar, index, rpath), index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts)), Gll.seqAt(grammar, index, rpath), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Loop{rs}]), ts), List.append(&2, Spec.Tree, L, Spec.Loop{rs} <> ts), Plug.app_snoc(L, Spec.Loop{rs}, ts)), hE)))))))))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EAdmDone(False{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> ts, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

law best_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{True{}, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(True{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  for ihCh: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ch)
  for ihRest: EAdmIH(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, rest)
  EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, above, span, after)

def best_round(rpath, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0, a, ch, rest, pEq, pos, coE, kE, fitT, lvT, inT, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Pick{a, ch} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, (all0, (ctxE0, hE0))))):
          +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +ctxE = {ctxE0 : {Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)) == Plug.RoundCtx{alts, index, prefix, above, span, after} : Plug.Ctx}}
          +hE = {hE0 : {Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)) == Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}) : +List<Spec.Item>}}
          +w = Spec.leaves(ch)
          +lr = Spec.leaves(rest)
          +end = Nat.add(k, List.length(&2, Nat, w))
          +next = List.append(&2, Nat, lr, after)
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
          +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
          +pre = List.append(&2, Nat, prefix, [a])
          +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
          +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
          +allCh = R.in_app_left(wCh, wRest, kept, allW)
          +allRest = R.in_app_right(wCh, wRest, kept, allW)
          +posCh = PG.pos_children(w, lr, after, input, k, pos)
          +posRest = PG.pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
          +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
          +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
          +rpA = {a <> m <> outer : +List<Nat>}
          +lEqL = loop_seq(grammar, index, a, m, outer, kind, alts, loopIt, isL)
          +ctxE2 = Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, Plug.PickKid{L, a, rest} <> z, ch), Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, rest}, Plug.RoundCtx{alts, index, prefix, above, span, after}, ch), Plug.SeqCtx{Spec.altGuards(guards, index, prefix, a), Gll.seqAt(grammar, index, rpA), index, pre, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(rest), after)}, Equal.cong(Plug.Ctx, Plug.Ctx, v => Plug.holeCtx(grammar, guards, Plug.PickKid{L, a, rest}, v, ch), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Plug.RoundCtx{alts, index, prefix, above, span, after}, ctxE), Equal.cong(+List<Spec.Item>, Plug.Ctx, v => Plug.SeqCtx{Spec.altGuards(guards, index, prefix, a), v, index, pre, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(rest), after)}, Spec.altOf(alts, a), Gll.seqAt(grammar, index, rpA), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(alts, a), itemsEqR)))
          +coE2 = Equal.trans(Plug.Coord, Plug.coordOf(q0, Plug.PickKid{L, a, rest} <> z), Plug.holeCoord(Plug.PickKid{L, a, rest}, Plug.Coord{True{}, index, prefix, 0n, i, k0}), Plug.Coord{False{}, index, pre, 0n, i, k}, Equal.cong(Plug.Coord, Plug.Coord, v => Plug.holeCoord(Plug.PickKid{L, a, rest}, v), Plug.coordOf(q0, z), Plug.Coord{True{}, index, prefix, 0n, i, k0}, coE), Equal.cong(Nat, Plug.Coord, v => Plug.Coord{False{}, index, pre, 0n, i, v}, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), k, Equal.sym(Nat, k, Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))), kE)))
          +hE2 = Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, Plug.PickKid{L, a, rest} <> z, ch), Plug.holeItems(grammar, Plug.PickKid{L, a, rest}, Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}), ch), Gll.seqAt(grammar, index, rpA), Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Plug.holeItems(grammar, Plug.PickKid{L, a, rest}, v, ch), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}), hE), Equal.trans(+List<Spec.Item>, Plug.holeItems(grammar, Plug.PickKid{L, a, rest}, Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}), ch), Spec.altOf(alts, a), Gll.seqAt(grammar, index, rpA), Equal.cong(Spec.Item, +List<Spec.Item>, v => Gll.bracketAlt(Some{v}, a), Plug.itemAtOr(Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}), List.length(&2, Spec.Tree, L)), Spec.Brack{Spec.Group{}, alts}, times_at(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}, List.length(&2, Spec.Tree, L), len_before(L, Spec.Pick{a, ch}, rest))), Equal.sym(+List<Spec.Item>, Gll.seqAt(grammar, index, rpA), Spec.altOf(alts, a), itemsEqR)))
          +kE2 = Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
          (r => rival_loopy(Mk(grammar, marks, index, rpA), ch, fuel, grammar, marks, guards, pmarks, Spec.altGuards(guards, index, prefix, a), next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, input, s, index, rpA, pre, pEqA, {==}, lEqL, i, k, PG.own_sub(ch, index, pre, 0n, i, k, kept, allCh), rival_tr(grammar, guards, pmarks, marks, Spec.altGuards(guards, index, prefix, a), index, Gll.bracketAlt(G.loopItem(grammar, index, m <> outer), a), Gll.bracketAlt(Some{Spec.Brack{kind, alts}}, a), itemsEqR, Gll.reverseOnto(rpA, []), pre, Equal.sym(+List<Nat>, pre, Gll.reverseOnto(rpA, []), pEqA), w, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, ch, r)),
            (ihCh(False{}, index, rpA, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, next, Spec.sameAbove(above, span, Spec.leaves(ch)), w, Spec.altGuards(guards, index, prefix, a), Plug.PickKid{L, a, rest} <> z, [], k, pEqA, posCh, coE2, kE2, fitT, lvT, inT, (itemsEqR, (fitCh, (allCh, (itemsEqR, ({==}, (ctxE2, hE2))))))),
              ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, after, above, span, own, z, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), k0, pEq, posRest, coE, Equal.trans(Nat, end, Nat.add(k, List.length(&2, Nat, Spec.leaves([Spec.Pick{a, ch}]))), Nat.add(k0, List.length(&2, Nat, Spec.leaves(List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}])))), Sub.end_of_one(Spec.Pick{a, ch}, k), Plug.k_snoc(L, Spec.Pick{a, ch}, k0, k, kE)), Equal.trans(Bool, Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.fits([Spec.Node{q0, Plug.zip(z, v)}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)), fitT), Equal.trans(+List<Nat>, Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest))}]), Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}]), input, Equal.cong(+List<Spec.Tree>, +List<Nat>, v => Spec.leaves([Spec.Node{q0, Plug.zip(z, v)}]), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)), lvT), Equal.trans(Bool, Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest))}, 0n), U), Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest))}, 0n), U), True{}, Equal.cong(+List<Spec.Tree>, Bool, v => Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, v)}, 0n), U), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)), inT), (loopIt, (isL, (fitRest, (allRest, (Equal.trans(Plug.Ctx, Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest)), Plug.ctxOf(grammar, guards, start, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Plug.RoundCtx{alts, index, prefix, above, span, after}, Equal.cong(+List<Spec.Tree>, Plug.Ctx, v => Plug.ctxOf(grammar, guards, start, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)), ctxE), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest)), Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest)), Spec.Brack{Spec.Group{}, alts}), Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Plug.holeOf(grammar, q0, z, v), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)), Equal.trans(+List<Spec.Item>, Plug.holeOf(grammar, q0, z, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest)), Spec.Brack{Spec.Group{}, alts}), Spec.times(List.length(&2, Spec.Tree, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest)), Spec.Brack{Spec.Group{}, alts}), hE, Equal.cong(+List<Spec.Tree>, +List<Spec.Item>, v => Spec.times(List.length(&2, Spec.Tree, v), Spec.Brack{Spec.Group{}, alts}), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), Equal.sym(+List<Spec.Tree>, List.append(&2, Spec.Tree, List.append(&2, Spec.Tree, L, [Spec.Pick{a, ch}]), rest), List.append(&2, Spec.Tree, L, Spec.Pick{a, ch} <> rest), Plug.app_snoc(L, Spec.Pick{a, ch}, rest)))))))))))))

law best_nil:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +after: +List<Nat>
  Spec.ExtentBest(grammar, guards, pmarks, marks, [], items, index, prefix, dot, above, span, after)

def best_nil(items, grammar, guards, pmarks, marks, index, prefix, dot, above, span, after):
  match items:
    case Nil{}:
      Unit{}
    case Con{it, rest}:
      Unit{}
law best_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +q0: Nat
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +z: +List<Plug.Frame>
  for +L: +List<Spec.Tree>
  for +k0: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +coE: {Plug.coordOf(q0, z) == Plug.Coord{rounds, index, prefix, 0n, i, k0} : Plug.Coord}
  for +kE: {k == Nat.add(k0, List.length(&2, Nat, Spec.leaves(L))) : Nat}
  for +fitT: {Spec.fits([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +lvT: {Spec.leaves([Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}]) == input : +List<Nat>}
  for +inT: {Spec.allIn(Spec.steps(Spec.Node{q0, Plug.zip(z, List.append(&2, Spec.Tree, L, forest))}, 0n), U) == True{} : Bool}
  for ready: EAdmReady(rounds, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0)
  EAdmDone(rounds, grammar, guards, pmarks, marks, forest, items, index, prefix, dot, alts, above, span, after)

def best_walk(forest, rounds, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0, pEq, pos, coE, kE, fitT, lvT, inT, ready):
  match forest rounds:
    case Nil{} False{}:
      best_nil(items, grammar, guards, pmarks, marks, index, prefix, dot, above, span, after)
    case Nil{} True{}:
      Unit{}
    case Con{Spec.Leaf{+kd}, +ts} False{}:
      best_leaf(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, kd, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ts, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      best_node(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, q, ch, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ch, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ts, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      best_pick(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, a, ch, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ch, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ts, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      best_skip(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ts, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      best_loop(items, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, z, L, k0, rs, ts, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(rs, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ts, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      best_round(rpath, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, index, prefix, dot, i, k, items, kind, alts, after, above, span, own, z, L, k0, a, ch, rest, pEq, pos, coE, kE, fitT, lvT, inT, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(ch, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => zz => ll => kz => pe => po => ce => ke => ft => lt => it => rd => best_walk(rest, ri, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q0, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, zz, ll, kz, pe, po, ce, ke, ft, lt, it, rd)))
    case Con{Spec.Leaf{kd}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Leaf{kd} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Node{q, ch} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Skip{} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, more))):
          Empty.absurd(EAdmDone(True{}, grammar, guards, pmarks, marks, Spec.Loop{rs} <> rest, items, index, prefix, dot, alts, above, span, after), Lemma.false_is_not_true(fit0))

# ======== DIRECTION 2: A READING OF THE SET'S STEPS KEEPS PHASES 1 AND 2 ========

# The preference oracle keeps steps of the guard oracle's set.
law ukept_sub:
  for es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +y: Spec.Bsr
  for m: {Spec.bsrMember(y, Unb.kept(es, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  {Spec.bsrMember(y, es) == True{} : Bool}

def ukept_sub(es, fuel, grammar, guards, pmarks, input, y, m):
  match es:
    case Nil{}:
      m
    case Con{+e, +rest}:
      ekept_sub_pick(Prefer.isKeep(Unb.verdictOf(fuel, grammar, guards, pmarks, input, e)), e, rest, Unb.kept(rest, fuel, grammar, guards, pmarks, input), y, m,
        later => ukept_sub(rest, fuel, grammar, guards, pmarks, input, y, later))

law all_ukept:
  for xs: +List<Spec.Bsr>
  for +es: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +all: {Spec.allIn(xs, Unb.kept(es, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  {Spec.allIn(xs, es) == True{} : Bool}

def all_ukept(xs, es, fuel, grammar, guards, pmarks, input, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +K = Unb.kept(es, fuel, grammar, guards, pmarks, input)
      +mx = Lemma.and_true_left(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      +mr = Lemma.and_true_right_side(Spec.bsrMember(x, K), Spec.allIn(rest, K), all)
      %Equal.sym(Bool, Spec.bsrMember(x, es), True{}, ukept_sub(es, fuel, grammar, guards, pmarks, input, x, mx)) : {Bool.and(_, Spec.allIn(rest, es)) == True{} : Bool}
      %Equal.sym(Bool, Spec.allIn(rest, es), True{}, all_ukept(rest, es, fuel, grammar, guards, pmarks, input, mr)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# A forest read at i spells the tokens there.
law pos_spells:
  for +input: +List<Nat>
  for +i: Nat
  for +w: +List<Nat>
  for +after: +List<Nat>
  for +pos: {List.append(&2, Nat, w, after) == Lemma.dropN(i, input) : +List<Nat>}
  {w == Lemma.slice(input, i, List.length(&2, Nat, w)) : +List<Nat>}

def pos_spells(input, i, w, after, pos):
  +L = List.length(&2, Nat, w)
  Equal.sym(+List<Nat>, Lemma.takeN(L, Lemma.dropN(i, input)), w,
    Equal.trans(+List<Nat>, Lemma.takeN(L, Lemma.dropN(i, input)), Lemma.takeN(L, List.append(&2, Nat, w, after)), w, Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(L, v), Lemma.dropN(i, input), List.append(&2, Nat, w, after), Equal.sym(+List<Nat>, List.append(&2, Nat, w, after), Lemma.dropN(i, input), pos)), Lemma.take_append_length(w, after)))

law hold_conv:
  for +grammar: +List<Spec.Production>
  for +o: PG.Own
  for +guards: +List<Spec.GuardMark>
  for +index: Nat
  for +own: +List<Spec.Guard>
  for +S: +List<Spec.Item>
  for +f2: +List<Spec.Tree>
  for +ch: +List<Spec.Tree>
  for +after: +List<Nat>
  for +owE: {PG.ownGuards(o, guards, index) == own : +List<Spec.Guard>}
  for +itE: {PG.ownItems(o, grammar, index) == S : +List<Spec.Item>}
  for +lv: {Spec.leaves(f2) == Spec.leaves(ch) : +List<Nat>}
  for h: Spec.AllHold(grammar, PG.ownGuards(o, guards, index), PG.ownItems(o, grammar, index), f2, List.append(&2, Nat, Spec.leaves(f2), after))
  Spec.AllHold(grammar, own, S, f2, List.append(&2, Nat, Spec.leaves(ch), after))

def hold_conv(grammar, o, guards, index, own, S, f2, ch, after, owE, itE, lv, h):
  %owE : Spec.AllHold(grammar, _, S, f2, List.append(&2, Nat, Spec.leaves(ch), after))
  %itE : Spec.AllHold(grammar, PG.ownGuards(o, guards, index), _, f2, List.append(&2, Nat, Spec.leaves(ch), after))
  %lv : Spec.AllHold(grammar, PG.ownGuards(o, guards, index), PG.ownItems(o, grammar, index), f2, List.append(&2, Nat, _, after))
  h

# A reading made of the extent oracle's steps keeps phases 1 and 2 where the children of
# a node or pick stand: those steps are the preference oracle's, and so the guard
# oracle's (PROOF_GUARD.bend adm_walk and owner_holds, PROOF_PREFER.bend surv_walk).
law kept_rival:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +o: PG.Own
  for +index: Nat
  for +ofacts: PG.OwnFacts(o, grammar, index)
  for +rpath: +List<Nat>
  for +own: +List<Spec.Guard>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +i: Nat
  for +rpE: {PG.ownRpath(o) == rpath : +List<Nat>}
  for +itE: {PG.ownItems(o, grammar, index) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
  for +owE: {PG.ownGuards(o, guards, index) == own : +List<Spec.Guard>}
  for +posCh: {List.append(&2, Nat, Spec.leaves(ch), after) == Lemma.dropN(i, input) : +List<Nat>}
  RivalKept(grammar, guards, pmarks, index, rpath, own, after, above, span, ch, i, s)

def kept_rival(grammar, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, o, index, ofacts, rpath, own, after, above, span, ch, i, rpE, itE, owE, posCh):
  +f2 => +fit2 => +lv2 => +all2 =>
    +P = Gll.reverseOnto(rpath, [])
    +S = Gll.seqAt(grammar, index, rpath)
    +W = Spec.walk(f2, False{}, index, P, 0n, i, i)
    +Gr = Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input)
    +Kp = Unb.kept(sg, fuel, grammar, guards, pmarks, input)
    +Gk = Guard.guardKept(s0, fuel, grammar, guards, input)
    +allGr = Equal.trans(Bool, Spec.allIn(W, Gr), Spec.allIn(W, s), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(W, v), Gr, s, sEq), all2)
    +allU = all_grow(W, U, grammar, input, allGr)
    +allK = Equal.trans(Bool, Spec.allIn(W, Kp), Spec.allIn(W, U), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(W, v), Kp, U, uEq), allU)
    +allS = all_ukept(W, sg, fuel, grammar, guards, pmarks, input, allK)
    +allG = Equal.trans(Bool, Spec.allIn(W, Gk), Spec.allIn(W, sg), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(W, v), Gk, sg, gEq), allS)
    +pos2 = Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f2), after), List.append(&2, Nat, Spec.leaves(ch), after), Lemma.dropN(i, input), Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, after), Spec.leaves(f2), Spec.leaves(ch), lv2), posCh)
    +sp = pos_spells(input, i, Spec.leaves(f2), after, pos2)
    +pEqO = Equal.cong(+List<Nat>, +List<Nat>, v => Gll.reverseOnto(v, []), rpath, PG.ownRpath(o), Equal.sym(+List<Nat>, PG.ownRpath(o), rpath, rpE))
    +fitO = Equal.trans(Bool, Spec.fits(f2, grammar, PG.ownItems(o, grammar, index)), Spec.fits(f2, grammar, S), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f2, grammar, v), PG.ownItems(o, grammar, index), S, itE), fit2)
    (hold_conv(grammar, o, guards, index, own, S, f2, ch, after, owE, itE, lv2, PG.owner_holds(o, fuel, grammar, guards, input, index, P, pEqO, ofacts, s0, f2, i, after, pos2, fitO, allG)),
      (PG.adm_walk(f2, False{}, grammar, guards, input, fuel, s0, index, rpath, P, 0n, i, i, S, Spec.Group{}, [], after, {==}, pos2, ({==}, (fit2, allG))),
        PP.surv_walk(f2, False{}, grammar, guards, pmarks, input, fuel, sg, okAll, index, rpath, P, 0n, i, i, S, Spec.Group{}, [], above, span, after, {==}, sp, pos2, ({==}, (fit2, allK)))))

# ======== DIRECTION 2: A BEST TREE USES ONLY KEPT STEPS ========

def EKeepReady(rounds: Bool, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +after: +List<Nat>, +above: +List<Nat>, +span: +List<Nat>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, False{}, index, prefix, dot, i, k), s) == True{} : Bool} & {Spec.allIn(PG.ownSteps(forest, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool} & Spec.ExtentBest(grammar, guards, pmarks, marks, forest, items, index, prefix, dot, above, span, after)
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.allIn(Spec.walk(forest, True{}, index, prefix, dot, i, k), s) == True{} : Bool} & Spec.RoundsBest(grammar, guards, pmarks, marks, forest, alts, index, prefix, above, span, after)

def EKeepDone(rounds: Bool, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Data:
  {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def EKeepIH(+grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +input: +List<Nat>, +fuel: Nat, +s: +List<Spec.Bsr>, +U: +List<Spec.Bsr>, +sg: +List<Spec.Bsr>, +s0: +List<Spec.Bsr>, +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}, +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}, +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}, +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @after: +List<Nat> -> @above: +List<Nat> -> @span: +List<Nat> -> @own: +List<Spec.Guard> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>} -> {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool} -> EKeepReady(rounds, grammar, marks, guards, pmarks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span) -> EKeepDone(rounds, grammar, marks, input, fuel, s, forest, index, prefix, dot, i, k)

# A node or pick: its own step, the steps inside it, and the rest.
law ekeep_join:
  for +x: Spec.Bsr
  for +wCh: +List<Spec.Bsr>
  for +wTs: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +mx: {Spec.bsrMember(x, set) == True{} : Bool}
  for +hc: {Spec.allIn(wCh, set) == True{} : Bool}
  for +ht: {Spec.allIn(wTs, set) == True{} : Bool}
  {Spec.allIn(x <> List.append(&2, Spec.Bsr, wCh, wTs), set) == True{} : Bool}

def ekeep_join(x, wCh, wTs, set, mx, hc, ht):
  Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, wCh, wTs), set), mx, G.all_in_app(wCh, wTs, set, hc, ht))

law ekeep_node:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Node{q, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(False{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Node{q, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihCh: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ch)
  for ihTs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ts)
  EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k)

def ekeep_node(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, q, ch, ts, pEq, pos, kb, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hN, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Node{q, ch}, ts, grammar, Spec.Sym{Spec.Nonterminal{x}}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
              +wCh = Spec.walk(ch, False{}, q, [], 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = PG.pos_children(w, lts, after, input, k, pos)
              +posTs = PG.pos_tail(Spec.Node{q, ch}, ts, after, input, k, pos)
              +bndCh = drop_bound(k, input, w, next, kb, posCh)
              +ownCh = owner_m(Mk(grammar, marks, q, []), Ext.seqLoopy([], grammar, q), fuel, grammar, marks, guards, pmarks, Spec.prodGuards(guards, q), next, {x <> Spec.sameAbove(above, span, w) : +List<Nat>}, w, input, s, okK, q, [], [], {==}, {==}, {==}, ch, k, next, posCh, bndCh, fitCh, PG.own_sub(ch, q, [], 0n, k, k, s, allCh), kept_rival(grammar, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, PG.OProd{}, q, {==}, [], Spec.prodGuards(guards, q), next, {x <> Spec.sameAbove(above, span, w) : +List<Nat>}, w, ch, k, {==}, {==}, {==}, posCh), hN)
              +kCh = ihCh(False{}, q, [], [], 0n, k, k, Spec.rhsOf(grammar, q), kind, alts, next, {x <> Spec.sameAbove(above, span, w) : +List<Nat>}, w, Spec.prodGuards(guards, q), {==}, posCh, kb, ({==}, (fitCh, (allCh, (ownCh, admCh)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, pEq, posTs, drop_bound(k, input, w, next, kb, posCh), (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              ekeep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law ekeep_pick:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(False{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihCh: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ch)
  for ihTs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ts)
  EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k)

def ekeep_pick(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, a, ch, ts, pEq, pos, kb, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hP, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Group{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
              +pre = List.append(&2, Nat, prefix, [dot, a])
              +path = List.append(&2, Nat, prefix, [dot])
              +pre2 = List.append(&2, Nat, path, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
              +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = PG.pos_children(w, lts, after, input, k, pos)
              +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
              +assoc = G.nat_append_assoc(prefix, [dot], [a])
              +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), allCh)
              +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
              +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
              +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Group{}, balts}}, itemEq)
              +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
              +rpA = {a <> dot <> rpath : +List<Nat>}
              +bndCh = drop_bound(k, input, w, next, kb, posCh)
              +fitCh2 = Equal.trans(Bool, Spec.fits(ch, grammar, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ch, grammar, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), itemsEq2), fitCh)
              +ownCh = owner_m(Mk(grammar, marks, index, rpA), Ext.seqLoopy(rpA, grammar, index), fuel, grammar, marks, guards, pmarks, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, w), w, input, s, okK, index, rpA, pre2, pEq2, {==}, {==}, ch, k, next, posCh, bndCh, fitCh2, PG.own_sub(ch, index, pre2, 0n, k, k, s, allCh2), kept_rival(grammar, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, PG.OAlt{rpath, dot, a, Spec.Group{}, balts}, index, itemEq, rpA, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, w), w, ch, k, {==}, Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), itemsEq2), Equal.cong(+List<Nat>, +List<Spec.Guard>, v => Spec.altGuards(guards, index, v, a), Gll.reverseOnto(rpath, [dot]), path, Equal.sym(+List<Nat>, path, Gll.reverseOnto(rpath, [dot]), pathEq)), posCh), r => hP(rival_tr(grammar, guards, pmarks, marks, Spec.altGuards(guards, index, path, a), index, Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Group{}, balts}}, a), itemsEq2), pre2, Gll.reverseOnto(rpath, [dot, a]), pEq2, w, next, Spec.sameAbove(above, span, w), w, ch, r)))
              +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, Spec.sameAbove(above, span, w), w, Spec.altGuards(guards, index, path, a), pEq2, posCh, kb, (itemsEq2, (fitCh, (allCh2, (ownCh, admCh)))))
              +kCh = Equal.trans(Bool, Spec.allIn(wCh, kept), Spec.allIn(wCh2, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, pEq, posTs, drop_bound(k, input, w, next, kb, posCh), (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              ekeep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (hP, (admCh, admTs)):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
              +w = Spec.leaves(ch)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hh)
              +pre = List.append(&2, Nat, prefix, [dot, a])
              +path = List.append(&2, Nat, prefix, [dot])
              +pre2 = List.append(&2, Nat, path, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, k, k)
              +wCh2 = Spec.walk(ch, False{}, index, pre2, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wCh, wTs), s, allW)
              +allCh = R.in_app_left(wCh, wTs, s, allIn2)
              +allTs = R.in_app_right(wCh, wTs, s, allIn2)
              +posCh = PG.pos_children(w, lts, after, input, k, pos)
              +posTs = PG.pos_tail(Spec.Pick{a, ch}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
              +assoc = G.nat_append_assoc(prefix, [dot], [a])
              +allCh2 = Equal.trans(Bool, Spec.allIn(wCh2, s), Spec.allIn(wCh, s), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), s), pre2, pre, assoc), allCh)
              +pEqA = G.prefix_ext(rpath, prefix, [dot, a], pEq)
              +pEq2 = Equal.trans(+List<Nat>, pre2, pre, Gll.reverseOnto(rpath, [dot, a]), assoc, pEqA)
              +itemsEq2 = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{Spec.Optional{}, balts}}, itemEq)
              +pathEq = G.prefix_ext(rpath, prefix, [dot], pEq)
              +rpA = {a <> dot <> rpath : +List<Nat>}
              +bndCh = drop_bound(k, input, w, next, kb, posCh)
              +fitCh2 = Equal.trans(Bool, Spec.fits(ch, grammar, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ch, grammar, v), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), itemsEq2), fitCh)
              +ownCh = owner_m(Mk(grammar, marks, index, rpA), Ext.seqLoopy(rpA, grammar, index), fuel, grammar, marks, guards, pmarks, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, w), w, input, s, okK, index, rpA, pre2, pEq2, {==}, {==}, ch, k, next, posCh, bndCh, fitCh2, PG.own_sub(ch, index, pre2, 0n, k, k, s, allCh2), kept_rival(grammar, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, PG.OAlt{rpath, dot, a, Spec.Optional{}, balts}, index, itemEq, rpA, Spec.altGuards(guards, index, path, a), next, Spec.sameAbove(above, span, w), w, ch, k, {==}, Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), itemsEq2), Equal.cong(+List<Nat>, +List<Spec.Guard>, v => Spec.altGuards(guards, index, v, a), Gll.reverseOnto(rpath, [dot]), path, Equal.sym(+List<Nat>, path, Gll.reverseOnto(rpath, [dot]), pathEq)), posCh), r => hP(rival_tr(grammar, guards, pmarks, marks, Spec.altGuards(guards, index, path, a), index, Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), a), Gll.bracketAlt(Some{Spec.Brack{Spec.Optional{}, balts}}, a), itemsEq2), pre2, Gll.reverseOnto(rpath, [dot, a]), pEq2, w, next, Spec.sameAbove(above, span, w), w, ch, r)))
              +kCh2 = ihCh(False{}, index, a <> dot <> rpath, pre2, 0n, k, k, Spec.altOf(balts, a), kind, alts, next, Spec.sameAbove(above, span, w), w, Spec.altGuards(guards, index, path, a), pEq2, posCh, kb, (itemsEq2, (fitCh, (allCh2, (ownCh, admCh)))))
              +kCh = Equal.trans(Bool, Spec.allIn(wCh, kept), Spec.allIn(wCh2, kept), True{}, Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, k, k), kept), pre, pre2, Equal.sym(+List<Nat>, pre2, pre, assoc)), kCh2)
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, pEq, posTs, drop_bound(k, input, w, next, kb, posCh), (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              ekeep_join(hx, wCh, wTs, kept, mx, kCh, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law ekeep_leaf:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Leaf{k0} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(False{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Leaf{k0} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihTs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ts)
  EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k)

def ekeep_leaf(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, k0, ts, pEq, pos, kb, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t0}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t0}} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, 1n+k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, 1n+k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, 1n+k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t0}}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t0}}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, 1n+k, rest, kind, alts, after, above, span, own, pEq, PG.pos_tail(Spec.Leaf{k0}, ts, after, input, k, pos), drop_cons_bound(k, input, k0, List.append(&2, Nat, Spec.leaves(ts), after), pos), (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), kept), mx, kTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law ekeep_skip:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Skip{} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(False{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Skip{} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihTs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ts)
  EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k)

def ekeep_skip(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, ts, pEq, pos, kb, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Skip{} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Brack{Spec.Optional{}, balts}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, above, span, own, pEq, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), kb, (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), kept), mx, kTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Skip{} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
          +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Skip{} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
          +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
          +hx = Spec.at(index, prefix, 1n+dot, i, k, k)
          +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, k), kept), ownW)
          +fitTs = Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, rest, fit)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +allTs = R.in_tail(hx, Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), s, allW)
          +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, k, rest, kind, alts, after, above, span, own, pEq, PG.pos_tail(Spec.Skip{}, ts, after, input, k, pos), kb, (restEq, (fitTs, (allTs, (ownTs, adm0)))))
          Lemma.and_true_intro(Spec.bsrMember(hx, kept), Spec.allIn(Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), kept), mx, kTs)

law ekeep_loop:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Loop{rs} <> ts), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(False{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Loop{rs} <> ts, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihRs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, rs)
  for ihTs: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ts)
  EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k)

def ekeep_loop(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, rs, ts, pEq, pos, kb, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t0}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (admRs, admTs):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
              +w = Spec.leaves(rs)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Closure{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
              +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
              +path = List.append(&2, Nat, prefix, [dot])
              +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), s, allW)
              +allRs = R.in_app_left(wRs, wTs, s, allIn2)
              +allTs = R.in_app_right(wRs, wTs, s, allIn2)
              +posRs = PG.pos_children(w, lts, after, input, k, pos)
              +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
              +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
              +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Closure{}, balts, next, above, span, own, pEqL, posRs, kb, (itemEq, ({==}, (fitRs, (allRs, admRs)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, pEq, posTs, drop_bound(k, input, w, next, kb, posRs), (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              ekeep_join(hx, wRs, wTs, kept, mx, kRs, kTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          match adm0:
            case (admRs, admTs):
              +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
              +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +ownW = {own0 : {Spec.allIn(PG.ownSteps(Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +hx = Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))
              +mx = Lemma.and_true_left(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +ownTs = Lemma.and_true_right_side(Spec.bsrMember(hx, kept), Spec.allIn(PG.ownSteps(ts, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), kept), ownW)
              +fitTs = Fits.fits_tail(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
              +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
              +w = Spec.leaves(rs)
              +lts = Spec.leaves(ts)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lts, after)
              +headFit = Fits.fits_head(Spec.Loop{rs}, ts, grammar, Spec.Brack{Spec.Positive{}, balts}, rest, fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts}))), True{}, headFit)
              +fitRs = Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})), hh)
              +path = List.append(&2, Nat, prefix, [dot])
              +wRs = Spec.walk(rs, True{}, index, path, 0n, k, k)
              +wTs = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, end)
              +allIn2 = R.in_tail(hx, List.append(&2, Spec.Bsr, wRs, wTs), s, allW)
              +allRs = R.in_app_left(wRs, wTs, s, allIn2)
              +allTs = R.in_app_right(wRs, wTs, s, allIn2)
              +posRs = PG.pos_children(w, lts, after, input, k, pos)
              +posTs = PG.pos_tail(Spec.Loop{rs}, ts, after, input, k, pos)
              +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
              +pEqL = G.prefix_ext(rpath, prefix, [dot], pEq)
              +kRs = ihRs(True{}, index, dot <> rpath, path, 0n, k, k, rest, Spec.Positive{}, balts, next, above, span, own, pEqL, posRs, kb, (itemEq, ({==}, (fitRs, (allRs, admRs)))))
              +kTs = ihTs(False{}, index, rpath, prefix, 1n+dot, i, end, rest, kind, alts, after, above, span, own, pEq, posTs, drop_bound(k, input, w, next, kb, posRs), (restEq, (fitTs, (allTs, (ownTs, admTs)))))
              ekeep_join(hx, wRs, wTs, kept, mx, kRs, kTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, rest0)):
          Empty.absurd(EKeepDone(False{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> ts, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

law ekeep_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> rest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(True{}, grammar, marks, guards, pmarks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  for ihCh: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, ch)
  for ihRest: EKeepIH(grammar, marks, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, rest)
  EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k)

def ekeep_round(rpath, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, prefix, dot, i, k, items, kind, alts, after, above, span, own, a, ch, rest, pEq, pos, kb, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (loopIt, more):
          Empty.absurd(EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Pick{a, ch} <> rest, index, prefix, dot, i, k), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Sub.isNoneItem(v), None{}, Some{Spec.Brack{kind, alts}}, loopIt)))
    case Con{+m, +outer}:
      match ready:
        case (loopIt0, (isL0, (fit0, (all0, adm0)))):
          match adm0:
            case (hR, (admCh, admRest)):
              +loopIt = {loopIt0 : {G.loopItem(grammar, index, m <> outer) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
              +isL = {isL0 : {Gll.isLoop(kind) == True{} : Bool}}
              +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
              +allW = {all0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, i, k), s) == True{} : Bool}}
              +w = Spec.leaves(ch)
              +lr = Spec.leaves(rest)
              +end = Nat.add(k, List.length(&2, Nat, w))
              +next = List.append(&2, Nat, lr, after)
              +kept = Ext.extentKept(s, s, fuel, grammar, marks, input)
              +headFit = Fits.fits_head(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
              +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), True{}, headFit)
              +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh)
              +fitRest = Fits.fits_tail(Spec.Pick{a, ch}, rest, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}), fit)
              +pre = List.append(&2, Nat, prefix, [a])
              +wCh = Spec.walk(ch, False{}, index, pre, 0n, i, k)
              +wRest = Spec.walk(rest, True{}, index, prefix, 0n, i, end)
              +allCh = R.in_app_left(wCh, wRest, s, allW)
              +allRest = R.in_app_right(wCh, wRest, s, allW)
              +posCh = PG.pos_children(w, lr, after, input, k, pos)
              +posRest = PG.pos_tail(Spec.Pick{a, ch}, rest, after, input, k, pos)
              +pEqA = G.prefix_ext(m <> outer, prefix, [a], pEq)
              +itemsEqR = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), G.loopItem(grammar, index, m <> outer), Some{Spec.Brack{kind, alts}}, loopIt)
              +rpA = {a <> m <> outer : +List<Nat>}
              +ownS = PG.own_sub(ch, index, pre, 0n, i, k, s, allCh)
              +ownCh = owner_loopy(Mk(grammar, marks, index, rpA), ch, fuel, grammar, marks, input, s, okK, index, rpA, pre, pEqA, {==}, loop_seq(grammar, index, a, m, outer, kind, alts, loopIt, isL), i, k, ownS)
              +kCh = ihCh(False{}, index, a <> m <> outer, pre, 0n, i, k, Spec.altOf(alts, a), kind, alts, next, Spec.sameAbove(above, span, w), w, Spec.altGuards(guards, index, prefix, a), pEqA, posCh, kb, (itemsEqR, (fitCh, (allCh, (ownCh, admCh)))))
              +kRest = ihRest(True{}, index, m <> outer, prefix, 0n, i, end, items, kind, alts, after, above, span, own, pEq, posRest, drop_bound(k, input, w, next, kb, posCh), (loopIt, (isL, (fitRest, (allRest, admRest)))))
              G.all_in_app(wCh, wRest, kept, kCh, kRest)

law ekeep_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +after: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +own: +List<Spec.Guard>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +pos: {List.append(&2, Nat, Spec.leaves(forest), after) == Lemma.dropN(k, input) : +List<Nat>}
  for +kb: {Nat.is_le(k, List.length(&2, Nat, input)) == True{} : Bool}
  for ready: EKeepReady(rounds, grammar, marks, guards, pmarks, input, fuel, s, forest, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span)
  EKeepDone(rounds, grammar, marks, input, fuel, s, forest, index, prefix, dot, i, k)

def ekeep_walk(forest, rounds, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, items, kind, alts, after, above, span, own, pEq, pos, kb, ready):
  match forest rounds:
    case Nil{} False{}:
      match ready:
        case (rem0, (fit0, (all0, (own0, adm0)))):
          own0
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      ekeep_leaf(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, k0, ts, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ts, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      ekeep_node(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, q, ch, ts, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ch, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ts, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      ekeep_pick(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, a, ch, ts, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ch, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ts, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      ekeep_skip(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, ts, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ts, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      ekeep_loop(items, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, rpath, prefix, dot, i, k, kind, alts, after, above, span, own, rs, ts, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(rs, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ts, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      ekeep_round(rpath, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, index, prefix, dot, i, k, items, kind, alts, after, above, span, own, a, ch, rest, pEq, pos, kb, ready, (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(ch, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)), (ri => ix => rx => px => dx => cx => kx => its => kd => ax => af => ab => sp => ow => pe => po => kq => rd => ekeep_walk(rest, ri, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, ix, rx, px, dx, cx, kx, its, kd, ax, af, ab, sp, ow, pe, po, kq, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Leaf{k0} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Node{q, ch} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Skip{} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (loopIt, (isL, (fit0, rest0))):
          Empty.absurd(EKeepDone(True{}, grammar, marks, input, fuel, s, Spec.Loop{rs} <> rest, index, prefix, dot, i, k), Lemma.false_is_not_true(fit0))

# ======== WHAT THE ORACLE'S ANSWER SAYS ========

# The extent oracle answered from a set s: its decisions are known and checked, and it
# kept `set`.
def PFacts(+found: Maybe<&2, +List<Spec.Bsr>>, +fuel: Nat, +grammar: +List<Spec.Production>, +marks: +List<Spec.ExtentMark>, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Type:
  &s: +List<Spec.Bsr> -> {found == Some{s} : Maybe<&2, +List<Spec.Bsr>>} & {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool} & {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool} & {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}

law pf_both:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for facts: {Bool.and(Ext.allKnown(s, s, fuel, grammar, marks, input), Ext.allChecked(s, s, fuel, grammar, marks, input)) == True{} : Bool} & {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}
  PFacts(Some{s}, fuel, grammar, marks, input, set)

def pf_both(fuel, grammar, marks, input, set, s, facts):
  match facts:
    case (ok0, same):
      +ok = {ok0 : {Bool.and(Ext.allKnown(s, s, fuel, grammar, marks, input), Ext.allChecked(s, s, fuel, grammar, marks, input)) == True{} : Bool}}
      (s, ({==}, (Lemma.and_true_left(Ext.allKnown(s, s, fuel, grammar, marks, input), Ext.allChecked(s, s, fuel, grammar, marks, input), ok), (Lemma.and_true_right_side(Ext.allKnown(s, s, fuel, grammar, marks, input), Ext.allChecked(s, s, fuel, grammar, marks, input), ok), same))))

law pf_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +marks: +List<Spec.ExtentMark>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Ext.extentFrom(found, fuel, grammar, marks, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  PFacts(found, fuel, grammar, marks, input, set)

def pf_found(found, fuel, grammar, marks, input, set, got):
  match found:
    case Some{+s}:
      pf_both(fuel, grammar, marks, input, set, s, Sub.prefer_pick_facts(Bool.and(Ext.allKnown(s, s, fuel, grammar, marks, input), Ext.allChecked(s, s, fuel, grammar, marks, input)), Ext.extentKept(s, s, fuel, grammar, marks, input), set, got))
    case None{}:
      Empty.absurd(PFacts(None{}, fuel, grammar, marks, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# The whole chain: the preference oracle's set U, pruned to s, and what was kept from s.
def ExtFacts(+fuel: Nat, +grammar: +List<Spec.Production>, +guards: +List<Spec.GuardMark>, +pmarks: +List<Spec.Mark>, +marks: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +set: +List<Spec.Bsr>) -> Type:
  &U: +List<Spec.Bsr> -> &s: +List<Spec.Bsr> -> {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>} & {Unb.closedOver(U, s, grammar, input) == True{} : Bool} & {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>} & {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool} & {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool} & {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}

law ext_pruned:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +kEq: {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}
  for pr: Sup.PrunedIs(Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input), grammar, input, s)
  ExtFacts(fuel, grammar, guards, pmarks, marks, start, input, set)

def ext_pruned(fuel, grammar, guards, pmarks, marks, start, input, set, s, okK, okC, kEq, pr):
  match pr:
    case (U0, (uEq0, (closed0, gEq0))):
      +U = {U0 : +List<Spec.Bsr>}
      +G = Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input)
      +uEq = {uEq0 : {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}}
      +gEq = {gEq0 : {G == s : +List<Spec.Bsr>}}
      +closedG = {closed0 : {Unb.closedOver(U, G, grammar, input) == True{} : Bool}}
      +closed = Equal.trans(Bool, Unb.closedOver(U, s, grammar, input), Unb.closedOver(U, G, grammar, input), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Unb.closedOver(U, v, grammar, input), s, G, Equal.sym(+List<Spec.Bsr>, G, s, gEq)), closedG)
      (U, (s, (uEq, (closed, (gEq, (okK, (okC, kEq)))))))

law ext_of_pf:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for pf: PFacts(Unb.prunedFrom(Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input), grammar, input), fuel, grammar, marks, input, set)
  ExtFacts(fuel, grammar, guards, pmarks, marks, start, input, set)

def ext_of_pf(fuel, grammar, guards, pmarks, marks, start, input, set, pf):
  match pf:
    case (s0, (pEq0, (okK0, (okC0, kEq0)))):
      +s = {s0 : +List<Spec.Bsr>}
      +found = Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input)
      +pEq = {pEq0 : {Unb.prunedFrom(found, grammar, input) == Some{s} : Maybe<&2, +List<Spec.Bsr>>}}
      +okK = {okK0 : {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}}
      +okC = {okC0 : {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}}
      +kEq = {kEq0 : {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}}
      ext_pruned(fuel, grammar, guards, pmarks, marks, start, input, set, s, okK, okC, kEq, Sup.pruned_some(found, grammar, input, s, pEq))

# ======== THE LAW ========

# A parse tree that uses only kept steps is admissible and unbeaten (its steps are the
# preference oracle's), and has the best extent.
law au_of:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +start: Nat
  for +set: +List<Spec.Bsr>
  for +t: Spec.Tree
  for +inT: {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool}
  for both: ({Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool} -> Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])) & (Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) -> {Spec.allIn(Spec.steps(t, 0n), set) == True{} : Bool})
  Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])

def au_of(grammar, guards, pmarks, start, set, t, inT, both):
  match both:
    case (to, frm):
      to(inT)

law sel_mk:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +t: Spec.Tree
  for au: Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  for best: Spec.ExtentBest(grammar, guards, pmarks, marks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  Spec.Admissible(grammar, guards, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [t], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])

def sel_mk(grammar, guards, pmarks, marks, start, t, au, best):
  match au:
    case (a, u):
      (a, (u, best))

law best_of_kept:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for tree: Spec.Tree
  for +fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for +allT: {Spec.allIn(Spec.steps(tree, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}
  Spec.Admissible(grammar, guards, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])

def best_of_kept(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, sEq, tree, fitting, spelled, allT):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd(Spec.Admissible(grammar, guards, [Spec.Leaf{k}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [Spec.Leaf{k}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [Spec.Leaf{k}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      +K = Ext.extentKept(s, s, fuel, grammar, marks, input)
      +T = {Spec.Node{q, ch} : Spec.Tree}
      +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, fitting)
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +all = {allT : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), K) == True{} : Bool}}
      +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
      +allS = all_ekept(Spec.steps(T, 0n), s, fuel, grammar, marks, input, s, allT)
      +allG = Equal.trans(Bool, Spec.allIn(Spec.steps(T, 0n), Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input)), Spec.allIn(Spec.steps(T, 0n), s), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.allIn(Spec.steps(T, 0n), v), Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input), s, sEq), allS)
      +inT = all_grow(Spec.steps(T, 0n), U, grammar, input, allG)
      +w = Spec.leaves(ch)
      +xs = {start <> Spec.sameAbove([], [], w) : +List<Nat>}
      +own = Spec.prodGuards(guards, q)
      plugIn = plug_in(grammar, guards, pmarks, start, input, fuel, U, s, q, gotU, closed, [], ch, own, q, [], [], xs, w, 0n, {==}, fitCh, {==}, {==}, {==}, pos, fitting, spelled, inT)
      sel_mk(grammar, guards, pmarks, marks, start, T, au_of(grammar, guards, pmarks, start, U, T, inT, Laws.prefer_avoid_exact(fuel, grammar, guards, pmarks, start, input, U, gotU)(T, fitting, spelled)),
        (r => rival_m(Mk(grammar, marks, q, []), Ext.seqLoopy([], grammar, q), ch, fuel, grammar, marks, guards, pmarks, own, [], xs, w, input, s, okC, q, [], [], {==}, {==}, {==}, 0n, [], pos, fitCh, PG.own_sub(ch, q, [], 0n, 0n, 0n, K, all), plugIn, r),
          (best_walk(ch, False{}, grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, q, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], [], xs, w, own, [], [], 0n, {==}, pos, {==}, {==}, fitting, spelled, inT, ({==}, (fitCh, (all, ({==}, ({==}, ({==}, {==}))))))), Unit{})))
    case Spec.Pick{a, ch}:
      Empty.absurd(Spec.Admissible(grammar, guards, [Spec.Pick{a, ch}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [Spec.Pick{a, ch}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [Spec.Pick{a, ch}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd(Spec.Admissible(grammar, guards, [Spec.Skip{}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [Spec.Skip{}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [Spec.Skip{}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd(Spec.Admissible(grammar, guards, [Spec.Loop{rs}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [Spec.Loop{rs}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [Spec.Loop{rs}], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []), Lemma.false_is_not_true(fitting))

# A selected tree uses only kept steps.
law kept_of_best:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +fuel: Nat
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +sg: +List<Spec.Bsr>
  for +s0: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for +gEq: {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for tree: Spec.Tree
  for +fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  for sel: Spec.Admissible(grammar, guards, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, []) & Spec.Unbeaten(grammar, guards, pmarks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], []) & Spec.ExtentBest(grammar, guards, pmarks, marks, [tree], [Spec.Sym{Spec.Nonterminal{start}}], 0n, [], 0n, [], [], [])
  {Spec.allIn(Spec.steps(tree, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}

def kept_of_best(grammar, guards, pmarks, marks, start, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, gotU, closed, tree, fitting, spelled, sel):
  match tree:
    case Spec.Leaf{k}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Leaf{k}, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Node{+q, +ch}:
      match sel:
        case (adm, (unb, best)):
          match best:
            case (hN, (bestCh, unit)):
              +T = {Spec.Node{q, ch} : Spec.Tree}
              +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), True{}, fitting)
              +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
              +pos = {spelled : {List.append(&2, Nat, Spec.leaves(ch), []) == Lemma.dropN(0n, input) : +List<Nat>}}
              +kb = Lemma.zero_le(List.length(&2, Nat, input))
              +bnd = drop_bound(0n, input, Spec.leaves(ch), [], kb, pos)
              +inU = {back_of(grammar, guards, pmarks, start, U, T, Laws.prefer_avoid_exact(fuel, grammar, guards, pmarks, start, input, U, gotU)(T, fitting, spelled), adm, unb) : {Spec.allIn(Spec.walk(ch, False{}, q, [], 0n, 0n, 0n), U) == True{} : Bool}}
              +bef = Lemma.or_true_left_intro(Nat.is_eq(0n, 0n), Unb.roundBefore([], s, grammar, q, 0n, 0n), Lemma.nat_eq_refl(0n))
              +allS = Sup.sw_walk(ch, False{}, grammar, input, U, s, closed, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], [], {==}, pos, ({==}, (fitCh, (inU, bef))))
              +w = Spec.leaves(ch)
              +xs = {start <> Spec.sameAbove([], [], w) : +List<Nat>}
              +own = Spec.prodGuards(guards, q)
              keep0 = kept_rival(grammar, guards, pmarks, input, fuel, s, U, sg, s0, okAll, uEq, gEq, sEq, PG.OProd{}, q, {==}, [], own, [], xs, w, ch, 0n, {==}, {==}, {==}, pos)
              +ownCh = owner_m(Mk(grammar, marks, q, []), Ext.seqLoopy([], grammar, q), fuel, grammar, marks, guards, pmarks, own, [], xs, w, input, s, okK, q, [], [], {==}, {==}, {==}, ch, 0n, [], pos, bnd, fitCh, PG.own_sub(ch, q, [], 0n, 0n, 0n, s, allS), keep0, hN)
              ekeep_walk(ch, False{}, grammar, marks, guards, pmarks, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], [], xs, w, own, {==}, pos, kb, ({==}, (fitCh, (allS, (ownCh, bestCh)))))
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Pick{a, ch}, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Skip{}, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.allIn(Spec.steps(Spec.Loop{rs}, 0n), Ext.extentKept(s, s, fuel, grammar, marks, input)) == True{} : Bool}, Lemma.false_is_not_true(fitting))

law embeds_go:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for +sg: +List<Spec.Bsr>
  for +okAll: {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}
  for +uEq: {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}
  for gf: PG.GuardFacts(fuel, grammar, guards, start, input, sg)
  Spec.EmbedsExtentBest(grammar, guards, pmarks, marks, start, input, Ext.extentKept(s, s, fuel, grammar, marks, input))

def embeds_go(fuel, grammar, guards, pmarks, marks, start, input, s, okK, okC, U, gotU, closed, sEq, sg, okAll, uEq, gf):
  match gf:
    case (s00, (eqE0, (okG0, gEq0))):
      +s0 = {s00 : +List<Spec.Bsr>}
      +gEq = {gEq0 : {Guard.guardKept(s0, fuel, grammar, guards, input) == sg : +List<Spec.Bsr>}}
      +tree => +fitting => +spelled =>
        (allK => best_of_kept(grammar, guards, pmarks, marks, start, input, fuel, s, okC, U, gotU, closed, sEq, tree, fitting, spelled, allK),
          sel => kept_of_best(grammar, guards, pmarks, marks, start, input, fuel, s, okK, U, sg, s0, okAll, uEq, gEq, sEq, gotU, closed, tree, fitting, spelled, sel))

law embeds_pf:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +s: +List<Spec.Bsr>
  for +okK: {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +okC: {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}
  for +U: +List<Spec.Bsr>
  for +gotU: {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}
  for +closed: {Unb.closedOver(U, s, grammar, input) == True{} : Bool}
  for +sEq: {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}
  for pf: PP.PreferFacts(fuel, grammar, guards, pmarks, start, input, U)
  Spec.EmbedsExtentBest(grammar, guards, pmarks, marks, start, input, Ext.extentKept(s, s, fuel, grammar, marks, input))

def embeds_pf(fuel, grammar, guards, pmarks, marks, start, input, s, okK, okC, U, gotU, closed, sEq, pf):
  match pf:
    case (sg0, (eqG0, (okAll0, uEq0))):
      +sg = {sg0 : +List<Spec.Bsr>}
      +eqG = {eqG0 : {Guard.guardSteps(fuel, grammar, guards, start, input) == Some{sg} : Maybe<&2, +List<Spec.Bsr>>}}
      +okAll = {okAll0 : {Unb.allStepsOk(sg, fuel, grammar, guards, pmarks, input, sg, Unb.kept(sg, fuel, grammar, guards, pmarks, input)) == True{} : Bool}}
      +uEq = {uEq0 : {Unb.kept(sg, fuel, grammar, guards, pmarks, input) == U : +List<Spec.Bsr>}}
      embeds_go(fuel, grammar, guards, pmarks, marks, start, input, s, okK, okC, U, gotU, closed, sEq, sg, okAll, uEq, PG.guard_found(Exact.exactSteps(fuel, grammar, start, input), fuel, grammar, guards, start, input, sg, {==}, eqG))

law embeds_extent:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +pmarks: +List<Spec.Mark>
  for +marks: +List<Spec.ExtentMark>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for facts: ExtFacts(fuel, grammar, guards, pmarks, marks, start, input, set)
  Spec.EmbedsExtentBest(grammar, guards, pmarks, marks, start, input, set)

def embeds_extent(fuel, grammar, guards, pmarks, marks, start, input, set, facts):
  match facts:
    case (U0, (s0, (gotU0, (closed0, (sEq0, (okK0, (okC0, keptEq0))))))):
      +U = {U0 : +List<Spec.Bsr>}
      +s = {s0 : +List<Spec.Bsr>}
      +gotU = {gotU0 : {Unb.unbeatenSteps(fuel, grammar, guards, pmarks, start, input) == Some{U} : Maybe<&2, +List<Spec.Bsr>>}}
      +closed = {closed0 : {Unb.closedOver(U, s, grammar, input) == True{} : Bool}}
      +sEq = {sEq0 : {Unb.grow(1n+List.length(&2, Spec.Bsr, U), U, [], grammar, input) == s : +List<Spec.Bsr>}}
      +okK = {okK0 : {Ext.allKnown(s, s, fuel, grammar, marks, input) == True{} : Bool}}
      +okC = {okC0 : {Ext.allChecked(s, s, fuel, grammar, marks, input) == True{} : Bool}}
      +keptEq = {keptEq0 : {Ext.extentKept(s, s, fuel, grammar, marks, input) == set : +List<Spec.Bsr>}}
      %keptEq : Spec.EmbedsExtentBest(grammar, guards, pmarks, marks, start, input, _)
      embeds_pf(fuel, grammar, guards, pmarks, marks, start, input, s, okK, okC, U, gotU, closed, sEq, PP.prefer_found(Guard.guardSteps(fuel, grammar, guards, start, input), fuel, grammar, guards, pmarks, start, input, U, {==}, gotU))

# The law extent_exact.
def Laws.extent_exact(fuel, grammar, guards, pmarks, marks, start, input, set, got):
  +f = fuel
  embeds_extent(f, grammar, guards, pmarks, marks, start, input, set, ext_of_pf(f, grammar, guards, pmarks, marks, start, input, set, pf_found(Unb.prunedFrom(Unb.unbeatenSteps(f, grammar, guards, pmarks, start, input), grammar, input), f, grammar, marks, input, set, got)))
