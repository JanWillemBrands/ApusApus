import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_PRUNE.bend as P
import ./PROOF_EXACT.bend as PE
import ./LEMMAS.bend as Lemma

# A TREE BUILT FROM THE EXACT SET SPELLS THE INPUT.
#
# Every leaf of a tree has its step in the tree's steps; if those are in the exact
# set, the token check says the leaf's terminal is the input token at its position.
# The proof walks the tree like the others, building the slice of the input that the
# leaves spell.

# ---- The token at a terminal's step ----

law tok_pick:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for -rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +xOk: {Exact.tokenOk(grammar, input, x) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Exact.tokenOk(grammar, input, e) == True{} : Bool}
  {Exact.tokenOk(grammar, input, e) == True{} : Bool}

def tok_pick(grammar, input, e, x, rest, cases, xOk, searchRest):
  match cases:
    case Inl{same}:
      Equal.trans(Bool, Exact.tokenOk(grammar, input, e), Exact.tokenOk(grammar, input, x), True{}, Equal.cong(Spec.Bsr, Bool, v => Exact.tokenOk(grammar, input, v), e, x, same), xOk)
    case Inr{later}:
      searchRest(later)

law tok_member:
  for ps: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +e: Spec.Bsr
  for all: {Exact.allTokensOk(ps, grammar, input) == True{} : Bool}
  for m: {Spec.bsrMember(e, ps) == True{} : Bool}
  {Exact.tokenOk(grammar, input, e) == True{} : Bool}

def tok_member(ps, grammar, input, e, all, m):
  match ps:
    case Nil{}:
      Empty.absurd({Exact.tokenOk(grammar, input, e) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      +both = all
      tok_pick(grammar, input, e, x, rest, G.ebnf_member_cases(e, x, rest, m),
        Lemma.and_true_left(Exact.tokenOk(grammar, input, x), Exact.allTokensOk(rest, grammar, input), both),
        later => tok_member(rest, grammar, input, e, Lemma.and_true_right_side(Exact.tokenOk(grammar, input, x), Exact.allTokensOk(rest, grammar, input), both), later))

law token_is_sound:
  for m: Maybe<&2, Nat>
  for +t: Nat
  for e: {Gll.tokenIs(m, t) == True{} : Bool}
  {m == Some{t} : Maybe<&2, Nat>}

def token_is_sound(m, t, e):
  match m:
    case None{}:
      Empty.absurd({None{} == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(e))
    case Some{+x}:
      Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, x, t, Lemma.nat_eq_sound(x, t, e))

# The token under the step of a terminal t at pos.
law leaf_token_from:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +t: Nat
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Terminal{t}}} : Maybe<&2, Spec.Item>}
  for ok: {Exact.tokenOk(grammar, input, Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos)) == True{} : Bool}
  {List.get(&2, Nat, input, pos) == Some{t} : Maybe<&2, Nat>}

def leaf_token_from(grammar, input, index, rpath, prefix, dot, ctx, pos, t, pEq, itemEq, ok):
  +item = Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot)
  +get = List.get(&2, Nat, input, pos)
  ok1 = Equal.trans(Bool, Exact.tokenOkAt((1n+dot) <> rpath, grammar, input, index, pos, 1n+pos), Exact.tokenOk(grammar, input, Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos)), True{},
    Equal.cong(+List<Nat>, Bool, v => Exact.tokenOkAt(v, grammar, input, index, pos, 1n+pos), (1n+dot) <> rpath, Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+dot]), []),
      Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+dot]), []), (1n+dot) <> rpath, R.step_rev(rpath, prefix, 1n+dot, pEq))),
    ok)
  ok2 = Equal.trans(Bool, Exact.tokenItemOk(Some{Spec.Sym{Spec.Terminal{t}}}, input, pos, 1n+pos), Exact.tokenItemOk(item, input, pos, 1n+pos), True{},
    Equal.cong(Maybe<&2, Spec.Item>, Bool, v => Exact.tokenItemOk(v, input, pos, 1n+pos), Some{Spec.Sym{Spec.Terminal{t}}}, item, Equal.sym(Maybe<&2, Spec.Item>, item, Some{Spec.Sym{Spec.Terminal{t}}}, itemEq)),
    ok1)
  token_is_sound(get, t, Lemma.and_true_left(Gll.tokenIs(get, t), Nat.is_eq(1n+pos, 1n+pos), ok2))

# ---- Joining slices ----

law join_leaf:
  for +input: +List<Nat>
  for +pos: Nat
  for +kind: Nat
  for +rest: +List<Nat>
  for getEq: {List.get(&2, Nat, input, pos) == Some{kind} : Maybe<&2, Nat>}
  for sp: {rest == Lemma.slice(input, 1n+pos, List.length(&2, Nat, rest)) : +List<Nat>}
  {kind <> rest == Lemma.slice(input, pos, 1n+List.length(&2, Nat, rest)) : +List<Nat>}

def join_leaf(input, pos, kind, rest, getEq, sp):
  +n = List.length(&2, Nat, rest)
  +one = Lemma.get_slice(input, pos, kind, getEq)
  sp1 = Equal.trans(+List<Nat>, rest, Lemma.slice(input, 1n+pos, n), Lemma.slice(input, Nat.add(pos, 1n), n), sp,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, n), 1n+pos, Nat.add(pos, 1n), Equal.sym(Nat, Nat.add(pos, 1n), 1n+pos, Lemma.add_one_right(pos))))
  Equal.trans(+List<Nat>, kind <> rest, List.append(&2, Nat, Lemma.slice(input, pos, 1n), Lemma.slice(input, Nat.add(pos, 1n), n)), Lemma.slice(input, pos, 1n+n),
    Lemma.append_congr([kind], rest, Lemma.slice(input, pos, 1n), Lemma.slice(input, Nat.add(pos, 1n), n), Equal.sym(+List<Nat>, Lemma.slice(input, pos, 1n), [kind], one), sp1),
    Lemma.slice_split(input, pos, 1n, n))

law join_spells:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp1: {w1 == Lemma.slice(input, pos, List.length(&2, Nat, w1)) : +List<Nat>}
  for sp2: {w2 == Lemma.slice(input, Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)) : +List<Nat>}
  {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}

def join_spells(input, pos, w1, w2, sp1, sp2):
  +l1 = List.length(&2, Nat, w1)
  +l2 = List.length(&2, Nat, w2)
  Equal.trans(+List<Nat>, List.append(&2, Nat, w1, w2), List.append(&2, Nat, Lemma.slice(input, pos, l1), Lemma.slice(input, Nat.add(pos, l1), l2)), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))),
    Lemma.append_congr(w1, w2, Lemma.slice(input, pos, l1), Lemma.slice(input, Nat.add(pos, l1), l2), sp1, sp2),
    Equal.trans(+List<Nat>, List.append(&2, Nat, Lemma.slice(input, pos, l1), Lemma.slice(input, Nat.add(pos, l1), l2)), Lemma.slice(input, pos, Nat.add(l1, l2)), Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))),
      Lemma.slice_split(input, pos, l1, l2),
      Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, pos, v), Nat.add(l1, l2), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(l1, l2), Lemma.length_append(w1, w2)))))

# ======== THE WALK ========

def SReady(rounds: Bool, +grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}

def SpellIH(+grammar: +List<Spec.Production>, +input: +List<Nat>, +set: +List<Spec.Bsr>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @ctx: Nat -> @pos: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, ctx, pos), set) == True{} : Bool} -> SReady(rounds, grammar, forest, index, rpath, dot, items, kind, alts) -> G.Spells(forest, input, pos)

law s_leaf:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Nat
  for +ts: +List<Spec.Tree>
  for +t: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Leaf{kind} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Sym{Spec.Terminal{t}}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Leaf{kind} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Leaf{kind} <> ts, input, pos)

def s_leaf(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, ts, t, rest, pEq, inS, itemEq, restEq, fit, ihTs):
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, 1n+pos)
  getT = leaf_token_from(grammar, input, index, rpath, prefix, dot, ctx, pos, t, pEq, itemEq, tok_member(set, grammar, input, step, tok, R.in_head(step, later, set, inS)))
  kt = Lemma.nat_eq_sound(kind, t, Lemma.and_true_left(Nat.is_eq(kind, t), Spec.fits(ts, grammar, rest), fit))
  getK = Equal.trans(Maybe<&2, Nat>, List.get(&2, Nat, input, pos), Some{t}, Some{kind}, getT, Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, t, kind, Equal.sym(Nat, kind, t, kt)))
  join_leaf(input, pos, kind, Spec.leaves(ts), getK,
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, 1n+pos, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, set, inS), (restEq, Lemma.and_true_right_side(Nat.is_eq(kind, t), Spec.fits(ts, grammar, rest), fit))))

law s_join:
  for +input: +List<Nat>
  for +pos: Nat
  for +w1: +List<Nat>
  for +w2: +List<Nat>
  for sp1: {w1 == Lemma.slice(input, pos, List.length(&2, Nat, w1)) : +List<Nat>}
  for sp2: {w2 == Lemma.slice(input, Nat.add(pos, List.length(&2, Nat, w1)), List.length(&2, Nat, w2)) : +List<Nat>}
  {List.append(&2, Nat, w1, w2) == Lemma.slice(input, pos, List.length(&2, Nat, List.append(&2, Nat, w1, w2))) : +List<Nat>}

def s_join(input, pos, w1, w2, sp1, sp2):
  join_spells(input, pos, w1, w2, sp1, sp2)

law s_node:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Node{q, ch} <> ts, input, pos)

def s_node(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, inS, restEq, fit, ihCh, ihTs):
  +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
  +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
  +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +inner = Spec.walk(ch, False{}, q, [], 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, inner, later), set, inS)
  s_join(input, pos, Spec.leaves(ch), Spec.leaves(ts),
    ihCh(False{}, q, [], [], 0n, pos, pos, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, R.in_app_left(inner, later, set, inRest), ({==}, Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk))),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(inner, later, set, inRest), (restEq, Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit))))

law s_pick:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Pick{a, ch} <> ts, input, pos)

def s_pick(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, rest, pEq, inS, itemEq, restEq, fitCh, fitTs, ihCh, ihTs):
  +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +inner = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, inner, later), set, inS)
  s_join(input, pos, Spec.leaves(ch), Spec.leaves(ts),
    ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos, Spec.altOf(balts, a), Spec.Group{}, [], G.prefix_ext(rpath, prefix, [dot, a], pEq), R.in_app_left(inner, later, set, inRest), (G.alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq), fitCh)),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(inner, later, set, inRest), (restEq, fitTs)))

law s_skip:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Skip{} <> ts, input, pos)

def s_skip(grammar, input, set, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inS, restEq, fitTs, ihTs):
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, pos)
  ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, pos, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, set, inS), (restEq, fitTs))

law s_loop0:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Loop{[]} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Loop{[]} <> ts, input, pos)

def s_loop0(grammar, input, set, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inS, restEq, fitTs, ihTs):
  +p0 = Nat.add(pos, 0n)
  +lts = Spec.leaves(ts)
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, p0)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, p0)
  sp0 = ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, p0, rest, Spec.Group{}, [], pEq, R.in_tail(step, later, set, inS), (restEq, fitTs))
  Equal.trans(+List<Nat>, lts, Lemma.slice(input, p0, List.length(&2, Nat, lts)), Lemma.slice(input, pos, List.length(&2, Nat, lts)), sp0,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(input, v, List.length(&2, Nat, lts)), p0, pos, Lemma.add_zero_right(pos)))

law s_loop:
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for ihRs: SpellIH(grammar, input, set, rs)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Loop{rs} <> ts, input, pos)

def s_loop(grammar, input, set, index, rpath, prefix, dot, ctx, pos, rs, ts, bkind, balts, rest, pEq, inS, itemEq, restEq, fitRs, fitTs, ihRs, ihTs):
  +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))
  +step = Spec.at(index, prefix, 1n+dot, ctx, pos, e1)
  +inner = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, e1)
  +inRest = R.in_tail(step, List.append(&2, Spec.Bsr, inner, later), set, inS)
  s_join(input, pos, Spec.leaves(rs), Spec.leaves(ts),
    ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos, [], bkind, balts, G.prefix_ext(rpath, prefix, [dot], pEq), R.in_app_left(inner, later, set, inRest), (itemEq, fitRs)),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, e1, rest, Spec.Group{}, [], pEq, R.in_app_right(inner, later, set, inRest), (restEq, fitTs)))

law s_round:
  for rpath: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inS: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for +itemEq: {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihRest: SpellIH(grammar, input, set, rest)
  G.Spells(Spec.Pick{a, ch} <> rest, input, pos)

def s_round(rpath, grammar, input, set, index, prefix, dot, ctx, pos, a, ch, rest, kind, alts, pEq, inS, itemEq, fitCh, fitRest, ihCh, ihRest):
  match rpath:
    case Nil{}:
      Empty.absurd(G.Spells(Spec.Pick{a, ch} <> rest, input, pos), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      +e1 = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
      +inner = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos)
      +later = Spec.walk(rest, True{}, index, prefix, 0n, ctx, e1)
      remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
      s_join(input, pos, Spec.leaves(ch), Spec.leaves(rest),
        ihCh(False{}, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos, Spec.altOf(alts, a), Spec.Group{}, [], G.prefix_ext(m <> outer, prefix, [a], pEq), R.in_app_left(inner, later, set, inS), (remCh, fitCh)),
        ihRest(True{}, index, m <> outer, prefix, 0n, ctx, e1, [], kind, alts, pEq, R.in_app_right(inner, later, set, inS), (itemEq, fitRest)))

law zleaf_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Leaf{k0} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Leaf{k0} <> ts, index, rpath, dot, items, kind, alts)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Leaf{k0} <> ts, input, pos)

def zleaf_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          s_leaf(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, k0, ts, t, rest, pEq, inY, itemEq, restEq, fit, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> ts, input, pos), Lemma.false_is_not_true(fit0))

law znode_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Node{q, ch} <> ts, index, rpath, dot, items, kind, alts)
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Node{q, ch} <> ts, input, pos)

def znode_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, inY, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          s_node(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, q, ch, ts, x, rest, pEq, inY, restEq, fit, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))

law zpick_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Pick{a, ch} <> ts, index, rpath, dot, items, kind, alts)
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Pick{a, ch} <> ts, input, pos)

def zpick_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, inY, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +hOk = Lemma.and_true_left(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          s_pick(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Group{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit), ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +hOk = Lemma.and_true_left(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit)
          +altOk = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          s_pick(grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Optional{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk),
            Lemma.and_true_right_side(Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a))), Spec.fits(ts, grammar, rest), fit), ihCh, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Pick{a, ch} <> ts, input, pos), Lemma.false_is_not_true(fit0))

law zskip_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Skip{} <> ts, index, rpath, dot, items, kind, alts)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Skip{} <> ts, input, pos)

def zskip_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          s_skip(grammar, input, set, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Skip{} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          s_skip(grammar, input, set, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, ihTs)

law zloop0_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{[]} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Loop{[]} <> ts, index, rpath, dot, items, kind, alts)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Loop{[]} <> ts, input, pos)

def zloop0_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{[]} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          s_loop0(grammar, input, set, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, inY, restEq, fit, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{[]} <> ts, input, pos), Lemma.false_is_not_true(fit0))

law zloop_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +r: Spec.Tree
  for +rr: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Loop{r <> rr} <> ts, False{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(False{}, grammar, Spec.Loop{r <> rr} <> ts, index, rpath, dot, items, kind, alts)
  for ihRs: SpellIH(grammar, input, set, r <> rr)
  for ihTs: SpellIH(grammar, input, set, ts)
  G.Spells(Spec.Loop{r <> rr} <> ts, input, pos)

def zloop_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, inY, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem, fit):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Closure{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          s_loop(grammar, input, set, index, rpath, prefix, dot, ctx, pos, r <> rr, ts, Spec.Closure{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, fit0):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{r <> rr} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +okR = Spec.roundsOk(Spec.Positive{}, r <> rr)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit)
          s_loop(grammar, input, set, index, rpath, prefix, dot, ctx, pos, r <> rr, ts, Spec.Positive{}, balts, rest, pEq, inY, itemEq, restEq,
            Lemma.and_true_right_side(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts})), both),
            Lemma.and_true_right_side(Bool.and(okR, Spec.fits(r <> rr, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rr), Spec.Brack{Spec.Group{}, balts}))), Spec.fits(ts, grammar, rest), fit), ihRs, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, fit0):
          Empty.absurd(G.Spells(Spec.Loop{r <> rr} <> ts, input, pos), Lemma.false_is_not_true(fit0))

law zround_disp:
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> rest, True{}, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(True{}, grammar, Spec.Pick{a, ch} <> rest, index, rpath, dot, [], kind, alts)
  for ihCh: SpellIH(grammar, input, set, ch)
  for ihRest: SpellIH(grammar, input, set, rest)
  G.Spells(Spec.Pick{a, ch} <> rest, input, pos)

def zround_disp(a, ch, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, rest, pEq, inY, ready, ihCh, ihRest):
  match ready:
    case (itemEq0, fit0):
      +itemEq = {itemEq0 : {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
      +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +R = Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}))
      +hOk = Lemma.and_true_left(h, R, fit)
      s_round(rpath, grammar, input, set, index, prefix, dot, ctx, pos, a, ch, rest, kind, alts, pEq, inY, itemEq,
        Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(h, R, fit), ihCh, ihRest)

# The leaves of a forest whose steps are in a set with good tokens spell the input.
law spell_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +inY: {Spec.allIn(Spec.walk(forest, rounds, index, prefix, dot, ctx, pos), set) == True{} : Bool}
  for ready: SReady(rounds, grammar, forest, index, rpath, dot, items, kind, alts)
  G.Spells(forest, input, pos)

def spell_walk(forest, rounds, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, items, kind, alts, pEq, inY, ready):
  match forest rounds:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      zleaf_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, k0, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      znode_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, q, ch, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ch, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      zpick_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, a, ch, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ch, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      zskip_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Loop{Nil{}}, +ts} False{}:
      zloop0_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Loop{Con{+r, +rr}}, +ts} False{}:
      zloop_disp(items, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, r, rr, ts, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(r <> rr, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ts, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      zround_disp(a, ch, grammar, input, set, tok, index, rpath, prefix, dot, ctx, pos, kind, alts, rest, pEq, inY, ready, (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(ch, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)), (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => iny => rd => spell_walk(rest, ri, grammar, input, set, tok, ix, rx, px, dx, cx, qx, its, kx, ax, pe, iny, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (ie, fit):
          Empty.absurd(G.Spells(Spec.Leaf{k0} <> rest, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (ie, fit):
          Empty.absurd(G.Spells(Spec.Node{q, ch} <> rest, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (ie, fit):
          Empty.absurd(G.Spells(Spec.Skip{} <> rest, input, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (ie, fit):
          Empty.absurd(G.Spells(Spec.Loop{rs} <> rest, input, pos), Lemma.false_is_not_true(fit))

law tokens_facts:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +ws: +List<Spec.Tree>
  for facts: {Bool.and(Exact.witnessed(grammar, start, input, ps, ws), Exact.allTokensOk(ps, grammar, input)) == True{} : Bool} & {ps == set : +List<Spec.Bsr>}
  {Exact.allTokensOk(set, grammar, input) == True{} : Bool}

def tokens_facts(grammar, start, input, ps, set, ws, facts):
  match facts:
    case (ok, same):
      %same : {Exact.allTokensOk(_, grammar, input) == True{} : Bool}
      Lemma.and_true_right_side(Exact.witnessed(grammar, start, input, ps, ws), Exact.allTokensOk(ps, grammar, input), ok)

# ======== THE LAW ========

law tokens_from:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Exact.exactFrom(found, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {Exact.allTokensOk(set, grammar, input) == True{} : Bool}

def tokens_from(found, fuel, grammar, start, input, set, got):
  match found:
    case Some{+ps}:
      tokens_facts(grammar, start, input, ps, set, Witness.witnesses(fuel, grammar, start, input, ps), PE.exact_pick_facts(Bool.and(Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)), Exact.allTokensOk(ps, grammar, input)), ps, set, got))
    case None{}:
      Empty.absurd({Exact.allTokensOk(set, grammar, input) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law spell_root:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +tok: {Exact.allTokensOk(set, grammar, input) == True{} : Bool}
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for inSet: {Spec.allIn(Spec.steps(tree, 0n), set) == True{} : Bool}
  for long: {List.length(&2, Nat, Spec.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Spec.leaves([tree]) == input : +List<Nat>}

def spell_root(grammar, start, input, set, tok, tree, fitting, inSet, long):
  match tree:
    case Spec.Node{+q, +ch}:
      +fit = fitting
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, fit)
      +lch = Spec.leaves(ch)
      sp = spell_walk(ch, False{}, grammar, input, set, tok, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, inSet,
        ({==}, Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)))
      +nil = Lemma.append_nil_right(lch)
      lenEq = Equal.trans(Nat, List.length(&2, Nat, lch), List.length(&2, Nat, List.append(&2, Nat, lch, [])), List.length(&2, Nat, input),
        Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), lch, List.append(&2, Nat, lch, []), Equal.sym(+List<Nat>, List.append(&2, Nat, lch, []), lch, nil)), long)
      Equal.trans(+List<Nat>, List.append(&2, Nat, lch, []), lch, input, nil,
        Equal.trans(+List<Nat>, lch, Lemma.takeN(List.length(&2, Nat, lch), input), input, sp,
          Equal.trans(+List<Nat>, Lemma.takeN(List.length(&2, Nat, lch), input), Lemma.takeN(List.length(&2, Nat, input), input), input,
            Equal.cong(Nat, +List<Nat>, v => Lemma.takeN(v, input), List.length(&2, Nat, lch), List.length(&2, Nat, input), lenEq),
            Lemma.take_length(input))))
    case Spec.Leaf{k}:
      Empty.absurd({Spec.leaves([Spec.Leaf{k}]) == input : +List<Nat>}, Lemma.false_is_not_true(fitting))
    case Spec.Pick{a, ch}:
      Empty.absurd({Spec.leaves([Spec.Pick{a, ch}]) == input : +List<Nat>}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({Spec.leaves([Spec.Skip{}]) == input : +List<Nat>}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({Spec.leaves([Spec.Loop{rs}]) == input : +List<Nat>}, Lemma.false_is_not_true(fitting))

def Laws.exact_trees_spell(fuel, grammar, start, input, set, got, tree, fitting, inSet, long):
  +f = fuel
  +tok = tokens_from(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input, set, got)
  spell_root(grammar, start, input, set, tok, tree, fitting, inSet, long)