import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./FIRST.bend as First
import ./LEMMAS.bend as Lemma
import ./PROOF_SETS.bend as Sets
import ./PROOF_TABLES.bend as Tab

# A DESCRIPTOR OF A PARSE TREE IS ADMITTED. At the slot after `dot` items of a sequence,
# the forest for the rest of the sequence spells the input from pos to fin, and the token
# at fin is one that may come after the sequence. Then the token at pos is in the slot's
# predict set: it is the forest's first token, or, when the forest reads nothing, the
# token at fin.

def Spells(+forest: +List<Spec.Tree>, +input: +List<Nat>, +pos: Nat) -> Data:
  {Spec.leaves(forest) == Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(forest))) : +List<Nat>}

law split_slice:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp: {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}
  {Lemma.slice(input, pos, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))) == List.append(&2, Nat, w1, w2) : +List<Nat>}

def split_slice(input, pos, w1, w2, sp):
  Equal.trans(+List<Nat>, Lemma.slice(input, pos, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2))), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))), List.append(&2, Nat, w1, w2),
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, pos, v), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), Lemma.length_append(w1, w2))),
    Equal.sym(+List<Nat>, List.append(&2, Nat, w1, w2), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))), sp))

law spells_first:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp: {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}
  {w1 == Lemma.slice(input, pos, List.length(&2, Nat, w1)) : +List<Nat>}

def spells_first(input, pos, w1, w2, sp):
  Equal.sym(+List<Nat>, Lemma.slice(input, pos, List.length(&2, Nat, w1)), w1, Lemma.slice_left(input, pos, w1, w2, split_slice(input, pos, w1, w2, sp)))

law leaf_token:
  for +input: +List<Nat>
  for +pos: Nat
  for +kind: Nat
  for +rest: +List<Nat>
  for sp: {kind <> rest == Lemma.slice(input, pos, List.length(&2, Nat, kind <> rest)) : +List<Nat>}
  {List.get(&2, Nat, input, pos) == Some{kind} : Maybe<&2, Nat>}

def leaf_token(input, pos, kind, rest, sp):
  Lemma.slice_get(input, pos, kind, Equal.sym(+List<Nat>, [kind], Lemma.slice(input, pos, 1n), spells_first(input, pos, [kind], rest, sp)))

law admit_split:
  for lv: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +after: Gll.LSet
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +fin: Nat
  for +lvEq: {Spec.leaves(forest) == lv : +List<Nat>}
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +finEq: {Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ctx: {Gll.lsHas(List.get(&2, Nat, input, fin), after) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, pos), Gll.restOr(Gll.infoItems(items, t), after)) == True{} : Bool}

def admit_split(lv, grammar, t, pc, input, items, after, forest, pos, fin, lvEq, fit, sp, finEq, ctx):
  match lv:
    case Nil{}:
      +len0 = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Spec.leaves(forest), [], lvEq)
      +posFin = Equal.trans(Nat, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))), fin,
        Equal.trans(Nat, pos, Nat.add(pos, 0n), Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))), Equal.sym(Nat, Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos)), Equal.cong(Nat, Nat, v => Nat.add(pos, v), 0n, List.length(&2, Nat, Spec.leaves(forest)), Equal.sym(Nat, List.length(&2, Nat, Spec.leaves(forest)), 0n, len0))),
        finEq)
      +ctxPos = Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, pos), after), Gll.lsHas(List.get(&2, Nat, input, fin), after), True{}, Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), after), pos, fin, posFin), ctx)
      Sets.rest_or_after(List.get(&2, Nat, input, pos), Gll.infoItems(items, t), after, Tab.nul_sound(forest, Gll.nestFuel(), items, grammar, t, pc, fit, lvEq), ctxPos)
    case Con{+k0, +w}:
      +spK = Equal.trans(+List<Nat>, k0 <> w, Spec.leaves(forest), Lemma.slice(input, pos, List.length(&2, Nat, k0 <> w)), Equal.sym(+List<Nat>, Spec.leaves(forest), k0 <> w, lvEq),
        Equal.trans(+List<Nat>, Spec.leaves(forest), Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(forest))), Lemma.slice(input, pos, List.length(&2, Nat, k0 <> w)), sp,
          Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.slice(input, pos, List.length(&2, Nat, v)), Spec.leaves(forest), k0 <> w, lvEq)))
      +getK = leaf_token(input, pos, k0, w, spK)
      +firstK = Tab.first_sound(forest, Gll.nestFuel(), items, grammar, t, pc, fit, k0, w, lvEq)
      +hasK = Sets.rest_or_first(Some{k0}, Gll.infoItems(items, t), after, firstK)
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, pos), Gll.restOr(Gll.infoItems(items, t), after)), Gll.lsHas(Some{k0}, Gll.restOr(Gll.infoItems(items, t), after)), True{},
        Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.restOr(Gll.infoItems(items, t), after)), List.get(&2, Nat, input, pos), Some{k0}, getK), hasK)

# The descriptor at (index, rpath, dot) is admitted.
law admit_core:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +dot: Nat
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +fin: Nat
  for +fit: {Spec.fits(forest, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +finEq: {Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ctx: {Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, pos), Gll.predictAt(grammar, t, index, rpath, dot)) == True{} : Bool}

def admit_core(grammar, t, pc, input, index, rpath, dot, forest, pos, fin, fit, sp, finEq, ctx):
  admit_split(Spec.leaves(forest), grammar, t, pc, input, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath)), Gll.contextAfter(grammar, t, index, rpath), forest, pos, fin, {==}, fit, sp, finEq, ctx)

# Is the descriptor the start of a round that must read something (Gll.roundReads)?
def seedReads(+grammar: +List<Spec.Production>, +index: Nat, dot: Nat, rpath: +List<Nat>, +k: Nat, +i: Nat) -> Bool:
  match dot rpath:
    case 0n Con{+a, Con{+m, +outer}}:
      Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, i)
    case 0n Con{a, Nil{}}:
      False{}
    case 0n Nil{}:
      False{}
    case 1n+d _:
      False{}

# A round that must read something, and does: its first token is in FIRST of the round.
law admit_first:
  for lv: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +items: +List<Spec.Item>
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +lvEq: {Spec.leaves(forest) == lv : +List<Nat>}
  for +fit: {Spec.fits(forest, grammar, items) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +reads: {Bool.not(List.is_empty(&2, Nat, lv)) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, pos), Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}

def admit_first(lv, grammar, t, pc, input, items, forest, pos, lvEq, fit, sp, reads):
  match lv:
    case Nil{}:
      Empty.absurd({Gll.lsHas(List.get(&2, Nat, input, pos), Gll.firstOf(Gll.infoItems(items, t))) == True{} : Bool}, Lemma.false_is_not_true(reads))
    case Con{+k0, +w}:
      +spK = Equal.trans(+List<Nat>, k0 <> w, Spec.leaves(forest), Lemma.slice(input, pos, List.length(&2, Nat, k0 <> w)), Equal.sym(+List<Nat>, Spec.leaves(forest), k0 <> w, lvEq),
        Equal.trans(+List<Nat>, Spec.leaves(forest), Lemma.slice(input, pos, List.length(&2, Nat, Spec.leaves(forest))), Lemma.slice(input, pos, List.length(&2, Nat, k0 <> w)), sp,
          Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.slice(input, pos, List.length(&2, Nat, v)), Spec.leaves(forest), k0 <> w, lvEq)))
      +getK = leaf_token(input, pos, k0, w, spK)
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, pos), Gll.firstOf(Gll.infoItems(items, t))), Gll.lsHas(Some{k0}, Gll.firstOf(Gll.infoItems(items, t))), True{},
        Equal.cong(Maybe<&2, Nat>, Bool, v => Gll.lsHas(v, Gll.firstOf(Gll.infoItems(items, t))), List.get(&2, Nat, input, pos), Some{k0}, getK),
        Tab.first_sound(forest, Gll.nestFuel(), items, grammar, t, pc, fit, k0, w, lvEq))

law admit_round:
  for b: Bool
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +fin: Nat
  for +fit: {Spec.fits(forest, grammar, Gll.dropFrom(0n, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +finEq: {Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ctx: {Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}
  for +reads: {Bool.or(Bool.not(b), Bool.not(List.is_empty(&2, Nat, Spec.leaves(forest)))) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, pos), Gll.roundPick(b, grammar, t, index, rpath)) == True{} : Bool}

def admit_round(b, grammar, t, pc, input, index, rpath, forest, pos, fin, fit, sp, finEq, ctx, reads):
  match b:
    case True{}:
      admit_first(Spec.leaves(forest), grammar, t, pc, input, Gll.seqAt(grammar, index, rpath), forest, pos, {==}, fit, sp, reads)
    case False{}:
      admit_core(grammar, t, pc, input, index, rpath, 0n, forest, pos, fin, fit, sp, finEq, ctx)

# The descriptor at (index, rpath, dot), started at k, is admitted: at the start of a round
# that must read something, the forest does.
law admit_for:
  for dot: Nat
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +pc: {First.prodsOk(grammar, grammar, t, 0n) == True{} : Bool}
  for +input: +List<Nat>
  for +index: Nat
  for +k: Nat
  for +forest: +List<Spec.Tree>
  for +pos: Nat
  for +fin: Nat
  for +fit: {Spec.fits(forest, grammar, Gll.dropFrom(dot, Gll.seqAt(grammar, index, rpath))) == True{} : Bool}
  for +sp: Spells(forest, input, pos)
  for +finEq: {Nat.add(pos, List.length(&2, Nat, Spec.leaves(forest))) == fin : Nat}
  for +ctx: {Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)) == True{} : Bool}
  for +reads: {Bool.or(Bool.not(seedReads(grammar, index, dot, rpath, k, pos)), Bool.not(List.is_empty(&2, Nat, Spec.leaves(forest)))) == True{} : Bool}
  {Gll.lsHas(List.get(&2, Nat, input, pos), Gll.predictFor(grammar, t, index, dot, rpath, k, pos)) == True{} : Bool}

def admit_for(dot, rpath, grammar, t, pc, input, index, k, forest, pos, fin, fit, sp, finEq, ctx, reads):
  match dot rpath:
    case 0n Con{+a, Con{+m, +outer}}:
      admit_round(Gll.roundReads(Gll.nthItem(Gll.seqAt(grammar, index, outer), m), k, pos), grammar, t, pc, input, index, a <> (m <> outer), forest, pos, fin, fit, sp, finEq, ctx, reads)
    case 0n Con{+a, Nil{}}:
      admit_core(grammar, t, pc, input, index, [a], 0n, forest, pos, fin, fit, sp, finEq, ctx)
    case 0n Nil{}:
      admit_core(grammar, t, pc, input, index, [], 0n, forest, pos, fin, fit, sp, finEq, ctx)
    case 1n+(+d) _:
      admit_core(grammar, t, pc, input, index, rpath, 1n+d, forest, pos, fin, fit, sp, finEq, ctx)

# ---- FOLLOW, from the check: the slot after a nonterminal y predicts no more than FOLLOW(y) ----

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      m

def pred2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      pred(m)

# Tell items apart.
def ntOf(m: Maybe<&2, Spec.Item>) -> Nat:
  match m:
    case Some{Spec.Sym{Spec.Nonterminal{y}}}:
      y
    case _:
      0n

def isNt(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{Spec.Sym{Spec.Nonterminal{y}}}:
      True{}
    case _:
      False{}

def isSome(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

law some_nt_eq:
  for +y2: Nat
  for +y: Nat
  for e: {Some{Spec.Sym{Spec.Nonterminal{y2}}} == Some{Spec.Sym{Spec.Nonterminal{y}}} : Maybe<&2, Spec.Item>}
  {y2 == y : Nat}

def some_nt_eq(y2, y, e):
  Equal.cong(Maybe<&2, Spec.Item>, Nat, v => ntOf(v), Some{Spec.Sym{Spec.Nonterminal{y2}}}, Some{Spec.Sym{Spec.Nonterminal{y}}}, e)

law not_nt:
  for +it: Spec.Item
  for +y: Nat
  for no: {isNt(Some{it}) == False{} : Bool}
  for e: {Some{it} == Some{Spec.Sym{Spec.Nonterminal{y}}} : Maybe<&2, Spec.Item>}
  Empty

def not_nt(it, y, no, e):
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, isNt(Some{it}), False{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isNt(v), Some{Spec.Sym{Spec.Nonterminal{y}}}, Some{it}, Equal.sym(Maybe<&2, Spec.Item>, Some{it}, Some{Spec.Sym{Spec.Nonterminal{y}}}, e)), no))

law none_not_some:
  for +it: Spec.Item
  for e: {None{} == Some{it} : Maybe<&2, Spec.Item>}
  Empty

def none_not_some(it, e):
  Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isSome(v), None{}, Some{it}, e))

# The check of the rest of the items, from the check of all of them.
law fo_rest:
  for it: Spec.Item
  for +rest: +List<Spec.Item>
  for +f: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rpath: +List<Nat>
  for +d: Nat
  for ok: {First.followsOk(1n+f, Gll.MItems{}, it <> rest, [], grammar, t, index, rpath, d) == True{} : Bool}
  {First.followsOk(1n+f, Gll.MItems{}, rest, [], grammar, t, index, rpath, 1n+d) == True{} : Bool}

def fo_rest(it, rest, f, grammar, t, index, rpath, d, ok):
  match it:
    case Spec.Sym{Spec.Nonterminal{+y}}:
      Lemma.and_true_right_side(First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y)), First.followsOk(1n+f, Gll.MItems{}, rest, [], grammar, t, index, rpath, 1n+d), ok)
    case Spec.Sym{Spec.Terminal{k}}:
      ok
    case Spec.Brack{kind, +inner}:
      Lemma.and_true_right_side(First.followsOk(f, Gll.MAlts{}, [], inner, grammar, t, index, d <> rpath, 0n), First.followsOk(1n+f, Gll.MItems{}, rest, [], grammar, t, index, rpath, 1n+d), ok)
    case Spec.Eps{}:
      ok

law fo_item_nt:
  for items: +List<Spec.Item>
  for j: Nat
  for +ff: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rpath: +List<Nat>
  for +d: Nat
  for +y: Nat
  for ok: {First.followsOk(ff, Gll.MItems{}, items, [], grammar, t, index, rpath, d) == True{} : Bool}
  for itemEq: {Gll.nthItem(items, j) == Some{Spec.Sym{Spec.Nonterminal{y}}} : Maybe<&2, Spec.Item>}
  {First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+Nat.add(j, d)), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}

def fo_item_nt(items, j, ff, grammar, t, index, rpath, d, y, ok, itemEq):
  match items j ff:
    case Nil{} _ _:
      Empty.absurd({First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+Nat.add(j, d)), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}, none_not_some(Spec.Sym{Spec.Nonterminal{y}}, itemEq))
    case Con{it, rest} _ 0n:
      Empty.absurd({First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+Nat.add(j, d)), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}, Lemma.false_is_not_true(ok))
    case Con{Spec.Sym{Spec.Nonterminal{+y2}}, +rest} 0n 1n+(+f):
      +ey = some_nt_eq(y2, y, itemEq)
      +here = Lemma.and_true_left(First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y2)), First.followsOk(1n+f, Gll.MItems{}, rest, [], grammar, t, index, rpath, 1n+d), ok)
      Equal.trans(Bool, First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y)), First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y2)), True{},
        Equal.cong(Nat, Bool, v => First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), v)), y, y2, Equal.sym(Nat, y2, y, ey)), here)
    case Con{Spec.Sym{Spec.Terminal{+k}}, rest} 0n 1n+(+f):
      Empty.absurd({First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}, not_nt(Spec.Sym{Spec.Terminal{k}}, y, {==}, itemEq))
    case Con{Spec.Brack{+kind, +inner}, rest} 0n 1n+(+f):
      Empty.absurd({First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}, not_nt(Spec.Brack{kind, inner}, y, {==}, itemEq))
    case Con{Spec.Eps{}, rest} 0n 1n+(+f):
      Empty.absurd({First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+d), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}, not_nt(Spec.Eps{}, y, {==}, itemEq))
    case Con{it, +rest} 1n+(+i) 1n+(+f):
      +r = fo_item_nt(rest, i, 1n+f, grammar, t, index, rpath, 1n+d, y, fo_rest(it, rest, f, grammar, t, index, rpath, d, ok), itemEq)
      %Lemma.add_succ_right(i, d) : {First.lsSub(Gll.predictAt(grammar, t, index, rpath, 1n+_), Gll.lsAt(Gll.folTab(t), y)) == True{} : Bool}
      r

# ---- The check of a bracket's alternative, from the check of the sequence around it ----

def altsOf(m: Maybe<&2, Spec.Item>) -> +List<+List<Spec.Item>>:
  match m:
    case Some{Spec.Brack{kind, alts}}:
      alts
    case _:
      []

def isBrack(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{Spec.Brack{kind, alts}}:
      True{}
    case _:
      False{}

law not_brack:
  for +it: Spec.Item
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for no: {isBrack(Some{it}) == False{} : Bool}
  for e: {Some{it} == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  Empty

def not_brack(it, kind, alts, no, e):
  Lemma.true_is_not_false(Equal.trans(Bool, True{}, isBrack(Some{it}), False{}, Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrack(v), Some{Spec.Brack{kind, alts}}, Some{it}, Equal.sym(Maybe<&2, Spec.Item>, Some{it}, Some{Spec.Brack{kind, alts}}, e)), no))

law fo_alt:
  for alts: +List<+List<Spec.Item>>
  for a: Nat
  for +f: Nat
  for +items0: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rp: +List<Nat>
  for +c: Nat
  for ok: {First.followsOk(f, Gll.MAlts{}, items0, alts, grammar, t, index, rp, c) == True{} : Bool}
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  {First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, Nat.add(a, c) <> rp, 0n) == True{} : Bool}

def fo_alt(alts, a, f, items0, grammar, t, index, rp, c, ok, isA):
  match alts a f:
    case _ _ 0n:
      Empty.absurd({First.followsOk(0n, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, Nat.add(a, c) <> rp, 0n) == True{} : Bool}, Lemma.false_is_not_true(ok))
    case Nil{} 0n 1n+(+f2):
      Empty.absurd({First.followsOk(f2, Gll.MItems{}, [], [], grammar, t, index, c <> rp, 0n) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Nil{} 1n+b 1n+(+f2):
      Empty.absurd({First.followsOk(f2, Gll.MItems{}, [], [], grammar, t, index, Nat.add(1n+b, c) <> rp, 0n) == True{} : Bool}, Lemma.false_is_not_true(isA))
    case Con{+alt, +rest} 0n 1n+(+f2):
      Lemma.and_true_left(First.followsOk(f2, Gll.MItems{}, alt, [], grammar, t, index, c <> rp, 0n), First.followsOk(1n+f2, Gll.MAlts{}, items0, rest, grammar, t, index, rp, 1n+c), ok)
    case Con{+alt, +rest} 1n+(+b) 1n+(+f2):
      +later = Lemma.and_true_right_side(First.followsOk(f2, Gll.MItems{}, alt, [], grammar, t, index, c <> rp, 0n), First.followsOk(1n+f2, Gll.MAlts{}, items0, rest, grammar, t, index, rp, 1n+c), ok)
      +r = fo_alt(rest, b, 1n+f2, items0, grammar, t, index, rp, 1n+c, later, isA)
      %Lemma.add_succ_right(b, c) : {First.followsOk(f2, Gll.MItems{}, Spec.altOf(rest, b), [], grammar, t, index, _ <> rp, 0n) == True{} : Bool}
      r

law fo_item_br:
  for items: +List<Spec.Item>
  for j: Nat
  for +ff: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +rpath: +List<Nat>
  for +d: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for ok: {First.followsOk(ff, Gll.MItems{}, items, [], grammar, t, index, rpath, d) == True{} : Bool}
  for itemEq: {Gll.nthItem(items, j) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  {First.followsOk(pred2(ff), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (Nat.add(j, d) <> rpath), 0n) == True{} : Bool}

def fo_item_br(items, j, ff, grammar, t, index, rpath, d, kind, alts, a, ok, itemEq, isA):
  match items j ff:
    case Nil{} _ _:
      Empty.absurd({First.followsOk(pred2(ff), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (Nat.add(j, d) <> rpath), 0n) == True{} : Bool}, none_not_some(Spec.Brack{kind, alts}, itemEq))
    case Con{it, rest} _ 0n:
      Empty.absurd({First.followsOk(0n, Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (Nat.add(j, d) <> rpath), 0n) == True{} : Bool}, Lemma.false_is_not_true(ok))
    case Con{Spec.Brack{+kind2, +inner}, +rest} 0n 1n+(+f):
      +eAlts = Equal.cong(Maybe<&2, Spec.Item>, +List<+List<Spec.Item>>, v => altsOf(v), Some{Spec.Brack{kind2, inner}}, Some{Spec.Brack{kind, alts}}, itemEq)
      +inOk = Lemma.and_true_left(First.followsOk(f, Gll.MAlts{}, [], inner, grammar, t, index, d <> rpath, 0n), First.followsOk(1n+f, Gll.MItems{}, rest, [], grammar, t, index, rpath, 1n+d), ok)
      +isA2 = Equal.trans(Bool, Spec.isAlt(inner, a), Spec.isAlt(alts, a), True{}, Equal.cong(+List<+List<Spec.Item>>, Bool, v => Spec.isAlt(v, a), inner, alts, eAlts), isA)
      +r = fo_alt(inner, a, f, [], grammar, t, index, d <> rpath, 0n, inOk, isA2)
      +r1 = Equal.trans(Bool, First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(inner, a), [], grammar, t, index, a <> (d <> rpath), 0n), First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(inner, a), [], grammar, t, index, Nat.add(a, 0n) <> (d <> rpath), 0n), True{},
        Equal.cong(Nat, Bool, v => First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(inner, a), [], grammar, t, index, v <> (d <> rpath), 0n), a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, Lemma.add_zero_right(a))), r)
      Equal.trans(Bool, First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (d <> rpath), 0n), First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(inner, a), [], grammar, t, index, a <> (d <> rpath), 0n), True{},
        Equal.cong(+List<+List<Spec.Item>>, Bool, v => First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(v, a), [], grammar, t, index, a <> (d <> rpath), 0n), alts, inner, Equal.sym(+List<+List<Spec.Item>>, inner, alts, eAlts)), r1)
    case Con{Spec.Sym{+sy}, rest} 0n 1n+(+f):
      Empty.absurd({First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (d <> rpath), 0n) == True{} : Bool}, not_brack(Spec.Sym{sy}, kind, alts, {==}, itemEq))
    case Con{Spec.Eps{}, rest} 0n 1n+(+f):
      Empty.absurd({First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (d <> rpath), 0n) == True{} : Bool}, not_brack(Spec.Eps{}, kind, alts, {==}, itemEq))
    case Con{it, +rest} 1n+(+i) 1n+(+f):
      +r = fo_item_br(rest, i, 1n+f, grammar, t, index, rpath, 1n+d, kind, alts, a, fo_rest(it, rest, f, grammar, t, index, rpath, d, ok), itemEq, isA)
      %Lemma.add_succ_right(i, d) : {First.followsOk(pred(f), Gll.MItems{}, Spec.altOf(alts, a), [], grammar, t, index, a <> (_ <> rpath), 0n) == True{} : Bool}
      r
