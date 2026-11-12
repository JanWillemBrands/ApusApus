import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./LEMMAS.bend as Lemma
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_PREFER.bend as Pf
import ./PROOF_LL1.bend as L
import ./PROOF_UNAMBIGUOUS.bend as U
import ./FITS.bend as Fits

# LL(1) AT ONE CHOICE POINT DECIDES IT. Walk one parse tree: every choice it makes (SPEC's
# choicesMade) predicts the token where it is made, by the same reasoning as in
# PROOF_UNAMBIGUOUS (FIRST when the chosen part reads something, else nullable and FOLLOW
# from the tree's own steps). Two trees choosing at one point and position, with the same
# token there, then choose the same, or LL1At at that point would be broken.

# ======== CHOICES THAT PREDICT ========

# The choice predicts the token where it is made.
def Ok(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, m: Spec.Made) -> Type:
  match m:
    case Spec.Made{+point, +pos, +choice}:
      Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, choice), List.get(&2, Nat, input, pos))

def AllOk(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, ms: +List<Spec.Made>) -> Type:
  match ms:
    case Nil{}:
      {0n == 0n : Nat}
    case Con{+m, rest}:
      Ok(grammar, start, input, m) & AllOk(grammar, start, input, rest)

law ok_append:
  for xs: +List<Spec.Made>
  for +ys: +List<Spec.Made>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for hx: AllOk(grammar, start, input, xs)
  for hy: AllOk(grammar, start, input, ys)
  AllOk(grammar, start, input, List.append(&2, Spec.Made, xs, ys))

def ok_append(xs, ys, grammar, start, input, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      match hx:
        case (h, t):
          (h, ok_append(rest, ys, grammar, start, input, t, hy))

law among_ok:
  for xs: +List<Spec.Made>
  for +x: Spec.Made
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for am: Spec.Among(x, xs)
  for all: AllOk(grammar, start, input, xs)
  Ok(grammar, start, input, x)

def among_ok(xs, x, grammar, start, input, am, all):
  match xs:
    case Nil{}:
      Empty.absurd(Ok(grammar, start, input, x), am)
    case Con{+y, +rest}:
      match am:
        case Inl{e}:
          match all:
            case (h, t):
              +ye = Equal.sym(Spec.Made, x, y, e)
              %ye : Ok(grammar, start, input, _)
              h
        case Inr{later}:
          match all:
            case (h, t):
              among_ok(rest, x, grammar, start, input, later, t)

# What the walk knows of a forest. In a sequence: it fits the items from the dot, spells the
# input from k, and walks inside the root's steps. In the rounds of a loop (the bracket at
# the dot): rounds of its body from k that read as they must, ending at E, where leaving
# the loop predicts the token.
def Ready(rounds: Bool, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root: Spec.Tree, +f: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +restO: +List<Spec.Item>, +later: Bool, +E: Nat) -> Type:
  match rounds:
    case False{}:
      {Spec.fits(f, grammar, items) == True{} : Bool} & G.Spells(f, input, k) & {Spec.allIn(Spec.walk(f, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool} &
        {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == items : +List<Spec.Item>} & {L.evenLength(prefix) == True{} : Bool}
    case True{}:
      {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>} &
        {Gll.isLoop(kind) == True{} : Bool} & {L.evenLength(prefix) == True{} : Bool} &
        {Spec.fits(f, grammar, Spec.times(List.length(&2, Spec.Tree, f), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {U.roundsFine(kind, later, f) == True{} : Bool} &
        G.Spells(f, input, k) & {Spec.allIn(Spec.walk(f, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool} &
        {Nat.add(k, List.length(&2, Nat, Spec.leaves(f))) == E : Nat} & Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E))

def IH(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root: Spec.Tree, +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp: {Spec.leaves([root]) == input : +List<Nat>}, +f: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @later: Bool -> @items: +List<Spec.Item> -> @index: Nat -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @restO: +List<Spec.Item> -> @E: Nat ->
    Ready(rounds, grammar, start, input, root, f, items, index, prefix, dot, i, k, kind, alts, restO, later, E) -> AllOk(grammar, start, input, Spec.madeIn(grammar, f, rounds, later, index, prefix, dot, k))

law leaf_ok:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
  for +a: Nat
  for +ts: +List<Spec.Tree>
  for ready: Ready(False{}, grammar, start, input, root, Spec.Leaf{a} <> ts, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihTs: IH(grammar, start, input, root, rootFit, rootSp, ts)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k))

def leaf_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ts, ready, ihTs):
  match items:
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Leaf{a} <> ts, grammar, Spec.Sym{Spec.Terminal{term}} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Leaf{a} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Leaf{a} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Sym{Spec.Terminal{term}} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Sym{Spec.Terminal{term}}, restI, itemsEq)
          ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, 1n+k, kind, alts, restO, E,
            (Fits.fits_tail(Spec.Leaf{a}, ts, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit), (G.leaf_rest(input, k, a, Spec.leaves(ts), sp), (U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k), Spec.steps(root, 0n), inW), (itT, even)))))
    case Nil{}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Nonterminal{x0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Group{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Optional{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Closure{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Positive{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Eps{}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Leaf{a} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))

law skip_ok:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
  for +ts: +List<Spec.Tree>
  for ready: Ready(False{}, grammar, start, input, root, Spec.Skip{} <> ts, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihTs: IH(grammar, start, input, root, rootFit, rootSp, ts)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k))

def skip_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, ts, ready, ihTs):
  match items:
    case Con{Spec.Eps{}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Skip{} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Eps{} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Eps{}, restI, itemsEq)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Eps{}}, U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Eps{}, restI, itemsEq))
          %itS : AllOk(grammar, start, input, List.append(&2, Spec.Made, Spec.skipMade(_, index, prefix, dot, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, k)))
          ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, k, kind, alts, restO, E, (Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, restI, fit), (sp, (U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Spec.steps(root, 0n), inW), (itT, even)))))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Skip{} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Optional{}, balts} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +it = {Spec.Brack{Spec.Optional{}, balts} : Spec.Item}
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{it}, itAt)
          +next = List.get(&2, Nat, input, k)
          +n = List.length(&2, +List<Spec.Item>, balts)
          cpL = U.bracket_cp(grammar, start, index, prefix, dot, n, Spec.Optional{}, balts, restI, next, itAt, itT,
            U.leave_cp(Spec.isAlt(balts, n), grammar, start, balts, index, prefix, dot, False{}, True{}, restI, next, Pf.lt_irrefl(n), {==},
              U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ts, restI, index, prefix, prefix, k, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts))), Spec.walk(Spec.Skip{} <> ts, False{}, index, prefix, dot, i, k), Fits.fits_tail(Spec.Skip{}, ts, grammar, it, restI, fit), sp, {==}, {==}, {==},
                U.end_walk(Spec.Skip{} <> ts, it <> restI, dot, grammar, index, prefix, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts))), fit, itemsEq, {==}, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Skip{} <> ts)), {==})), inW)))
          %itS : AllOk(grammar, start, input, List.append(&2, Spec.Made, Spec.skipMade(_, index, prefix, dot, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, k)))
          (cpL, ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, k, kind, alts, restO, E, (Fits.fits_tail(Spec.Skip{}, ts, grammar, it, restI, fit), (sp, (U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k), Spec.steps(root, 0n), inW), (itT, even))))))
    case Nil{}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{t0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Nonterminal{x0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Group{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Closure{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Positive{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Skip{} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))

law node_ok:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: Ready(False{}, grammar, start, input, root, Spec.Node{q, ch} <> ts, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihCh: IH(grammar, start, input, root, rootFit, rootSp, ch)
  for ihTs: IH(grammar, start, input, root, rootFit, rootSp, ts)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k))

def node_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, q, ch, ts, ready, ihCh, ihTs):
  match items:
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Node{q, ch} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Node{q, ch} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Sym{Spec.Nonterminal{x}} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +lhs = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fC = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
          +lc = Spec.leaves(ch)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lt, sp)
          +spT = G.spells_second(input, k, lc, lt, sp)
          +wC = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wT = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wC, wT), Spec.steps(root, 0n), inW)
          +inC = U.all_in_left(wC, wT, Spec.steps(root, 0n), inA)
          +inT = U.all_in_right(wC, wT, Spec.steps(root, 0n), inA)
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Sym{Spec.Nonterminal{x}}, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), Spec.Sym{Spec.Nonterminal{x}}, restI, itemsEq)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Sym{Spec.Nonterminal{x}}}, itAt)
          +next = List.get(&2, Nat, input, k)
          cp = U.nt_cp(Spec.lhsIs(grammar, q, x), grammar, start, q, next, lhs,
            U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.rhsOf(grammar, q), q, [], [], k, k, e, wC, fC, spC, {==}, {==}, {==},
              U.end_walk(ch, Spec.rhsOf(grammar, q), 0n, grammar, q, [], k, k, e, fC, {==}, {==}, {==}), inC))
          okC = ihCh(False{}, False{}, Spec.rhsOf(grammar, q), q, [], 0n, k, k, kind, alts, restO, E, (fC, (spC, (inC, ({==}, {==})))))
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, (fT, (spT, (inT, (itT, even)))))
          %itS : AllOk(grammar, start, input, Spec.Made{Spec.NonterminalAt{Spec.nonterminalOf(_)}, k, q} <> List.append(&2, Spec.Made, Spec.madeIn(grammar, ch, False{}, False{}, q, [], 0n, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e)))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, q, [], 0n, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e), grammar, start, input, okC, okT))
    case Nil{}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{t0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Group{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Optional{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Closure{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Positive{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Eps{}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Node{q, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))

law pick_ok:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: Ready(False{}, grammar, start, input, root, Spec.Pick{a, ch} <> ts, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihCh: IH(grammar, start, input, root, rootFit, rootSp, ch)
  for ihTs: IH(grammar, start, input, root, rootFit, rootSp, ts)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k))

def pick_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ch, ts, ready, ihCh, ihTs):
  match items:
    case Con{Spec.Brack{Spec.Group{}, +balts}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Group{}, balts} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +it = {Spec.Brack{Spec.Group{}, balts} : Spec.Item}
          +h = Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +isA = Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
          +lc = Spec.leaves(ch)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lt, sp)
          +spT = G.spells_second(input, k, lc, lt, sp)
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
          +wT = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wC, wT), Spec.steps(root, 0n), inW)
          +inC = U.all_in_left(wC, wT, Spec.steps(root, 0n), inA)
          +inT = U.all_in_right(wC, wT, Spec.steps(root, 0n), inA)
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +cEq = U.seq_child(grammar, index, prefix, dot, a, Spec.Group{}, balts, even, itAt)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +next = List.get(&2, Nat, input, k)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, Spec.Group{}, balts, restI, next, itAt, itT,
            U.alt_cp(Spec.isAlt(balts, a), grammar, start, balts, a, index, prefix, dot, True{}, False{}, restI, next, isA,
              U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.altOf(balts, a), index, List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, prefix, [dot, a]), k, k, e, wC, fC, spC, {==}, {==}, {==},
                U.end_walk(ch, Spec.altOf(balts, a), 0n, grammar, index, List.append(&2, Nat, prefix, [dot, a]), k, k, e, fC, cEq, {==}, {==}), inC)))
          okC = ihCh(False{}, False{}, Spec.altOf(balts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k, kind, alts, restO, E, (fC, (spC, (inC, (cEq, evenC)))))
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, (fT, (spT, (inT, (itT, even)))))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e), grammar, start, input, okC, okT))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Optional{}, balts} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +it = {Spec.Brack{Spec.Optional{}, balts} : Spec.Item}
          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +h = Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +h2 = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +reads = U.optional_consume(a, ch, Lemma.and_true_left(okR, Spec.isAlt(balts, a), h2))
          +isA = Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), h2)
          +fC = Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
          +lc = Spec.leaves(ch)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lt, sp)
          +spT = G.spells_second(input, k, lc, lt, sp)
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
          +wT = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wC, wT), Spec.steps(root, 0n), inW)
          +inC = U.all_in_left(wC, wT, Spec.steps(root, 0n), inA)
          +inT = U.all_in_right(wC, wT, Spec.steps(root, 0n), inA)
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +cEq = U.seq_child(grammar, index, prefix, dot, a, Spec.Optional{}, balts, even, itAt)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +next = List.get(&2, Nat, input, k)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, Spec.Optional{}, balts, restI, next, itAt, itT,
            U.alt_cp(Spec.isAlt(balts, a), grammar, start, balts, a, index, prefix, dot, False{}, True{}, restI, next, isA,
              U.first_from(lc, next, grammar, input, ch, Spec.altOf(balts, a), k, fC, {==}, spC, {==}, reads)))
          okC = ihCh(False{}, False{}, Spec.altOf(balts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k, kind, alts, restO, E, (fC, (spC, (inC, (cEq, evenC)))))
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, (fT, (spT, (inT, (itT, even)))))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e), grammar, start, input, okC, okT))
    case Nil{}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{t0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Nonterminal{x0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Closure{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Positive{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Eps{}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))

law loop_ok:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +later: Bool
  for +E: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: Ready(False{}, grammar, start, input, root, Spec.Loop{rs} <> ts, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihRs: IH(grammar, start, input, root, rootFit, rootSp, rs)
  for ihTs: IH(grammar, start, input, root, rootFit, rootSp, ts)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k))

def loop_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, rs, ts, ready, ihRs, ihTs):
  match items:
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Loop{rs} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Closure{}, balts} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +it = {Spec.Brack{Spec.Closure{}, balts} : Spec.Item}
          +okR = Spec.roundsOk(Spec.Closure{}, rs)
          +tm = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})
          +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fR = Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, tm), hOk)
          +fT = Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fine = U.closure_consume(rs, Lemma.and_true_left(okR, Spec.fits(rs, grammar, tm), hOk))
          +lr = Spec.leaves(rs)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lr))
          +spR = G.spells_first(input, k, lr, lt, sp)
          +spT = G.spells_second(input, k, lr, lt, sp)
          +wR = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
          +wT = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wR, wT), Spec.steps(root, 0n), inW)
          +inR = U.all_in_left(wR, wT, Spec.steps(root, 0n), inA)
          +inT = U.all_in_right(wR, wT, Spec.steps(root, 0n), inA)
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          LP = U.predicts_in(List.get(&2, Nat, input, e), grammar, start, input, root, rootFit, rootSp, ts, restI, index, prefix, prefix, e, i, Nat.add(e, List.length(&2, Nat, lt)), Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), fT, spT, {==}, {==}, {==},
            U.end_walk(Spec.Loop{rs} <> ts, it <> restI, dot, grammar, index, prefix, i, k, Nat.add(e, List.length(&2, Nat, lt)), fit, itemsEq,
              Equal.sym(Nat, Nat.add(e, List.length(&2, Nat, lt)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr, lt))), G.end_split(k, lr, lt)),
              Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs} <> ts)), {==})), inW)
          okRs = ihRs(True{}, False{}, [], index, prefix, dot, k, k, Spec.Closure{}, balts, restI, e, (itAt, (itT, ({==}, (even, (fR, (fine, (spR, (inR, ({==}, LP))))))))))
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, (fT, (spT, (inT, (itT, even)))))
          ok_append(Spec.madeIn(grammar, rs, True{}, False{}, index, prefix, dot, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e), grammar, start, input, okRs, okT)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +restI}:
      match ready:
        case (fit0, (sp0, (inW0, (itemsEq0, even0)))):
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> restI) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Loop{rs} <> ts, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +itemsEq = {itemsEq0 : {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == Spec.Brack{Spec.Positive{}, balts} <> restI : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +it = {Spec.Brack{Spec.Positive{}, balts} : Spec.Item}
          +okR = Spec.roundsOk(Spec.Positive{}, rs)
          +tm = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})
          +hOk = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fR = Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, tm), hOk)
          +fT = Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, restI), fit)
          +fine = Lemma.and_true_left(okR, Spec.fits(rs, grammar, tm), hOk)
          +lr = Spec.leaves(rs)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lr))
          +spR = G.spells_first(input, k, lr, lt, sp)
          +spT = G.spells_second(input, k, lr, lt, sp)
          +wR = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)
          +wT = Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e)
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wR, wT), Spec.steps(root, 0n), inW)
          +inR = U.all_in_left(wR, wT, Spec.steps(root, 0n), inA)
          +inT = U.all_in_right(wR, wT, Spec.steps(root, 0n), inA)
          +itAt = U.items_from_head(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          +itT = U.items_from_tail(dot, Spec.sequenceAt(grammar, index, prefix), it, restI, itemsEq)
          LP = U.predicts_in(List.get(&2, Nat, input, e), grammar, start, input, root, rootFit, rootSp, ts, restI, index, prefix, prefix, e, i, Nat.add(e, List.length(&2, Nat, lt)), Spec.walk(Spec.Loop{rs} <> ts, False{}, index, prefix, dot, i, k), fT, spT, {==}, {==}, {==},
            U.end_walk(Spec.Loop{rs} <> ts, it <> restI, dot, grammar, index, prefix, i, k, Nat.add(e, List.length(&2, Nat, lt)), fit, itemsEq,
              Equal.sym(Nat, Nat.add(e, List.length(&2, Nat, lt)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lr, lt))), G.end_split(k, lr, lt)),
              Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Loop{rs} <> ts)), {==})), inW)
          okRs = ihRs(True{}, False{}, [], index, prefix, dot, k, k, Spec.Positive{}, balts, restI, e, (itAt, (itT, ({==}, (even, (fR, (fine, (spR, (inR, ({==}, LP))))))))))
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, (fT, (spT, (inT, (itT, even)))))
          ok_append(Spec.madeIn(grammar, rs, True{}, False{}, index, prefix, dot, k), Spec.madeIn(grammar, ts, False{}, False{}, index, prefix, 1n+dot, e), grammar, start, input, okRs, okT)
    case Nil{}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Terminal{t0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Sym{Spec.Nonterminal{x0}}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Group{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Brack{Spec.Optional{}, b0}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))
    case Con{Spec.Eps{}, r0}:
      match ready:
        case (fit, rest):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Loop{rs} <> ts, False{}, later, index, prefix, dot, k)), Lemma.false_is_not_true(fit))

law rounds_nil_ok:
  for kind: Spec.Bracket
  for later: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E: Nat
  for ready: Ready(True{}, grammar, start, input, root, [], [], index, prefix, dot, i, k, kind, alts, restO, later, E)
  AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, later, index, prefix, dot, k))

def rounds_nil_ok(kind, later, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, alts, restO, E, ready):
  match kind later:
    case Spec.Group{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, True{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Group{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, False{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Optional{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, True{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Optional{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, False{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Closure{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Closure{}, True{}, []) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells([], input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E : Nat}}
          +n = List.length(&2, +List<Spec.Item>, alts)
          +next = List.get(&2, Nat, input, E)
          +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), fin)
          +ek = Equal.sym(Nat, k, E, nk)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Closure{}, alts}}, itAt)
          cpL = U.bracket_cp(grammar, start, index, prefix, dot, n, Spec.Closure{}, alts, restO, next, itAt, restAt,
            U.leave_cp(Spec.isAlt(alts, n), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(n), {==}, LP))
          %itS : AllOk(grammar, start, input, [Spec.Made{Spec.roundPoint(True{}, _, index, prefix, dot), k, Spec.alternateCount(_)}])
          %ek : AllOk(grammar, start, input, [Spec.Made{Spec.BracketAt{index, prefix, dot}, _, n}])
          (cpL, {==})
    case Spec.Closure{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Closure{}, False{}, []) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells([], input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E : Nat}}
          +n = List.length(&2, +List<Spec.Item>, alts)
          +next = List.get(&2, Nat, input, E)
          +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), fin)
          +ek = Equal.sym(Nat, k, E, nk)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Closure{}, alts}}, itAt)
          cpL = U.bracket_cp(grammar, start, index, prefix, dot, n, Spec.Closure{}, alts, restO, next, itAt, restAt,
            U.leave_cp(Spec.isAlt(alts, n), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(n), {==}, LP))
          %itS : AllOk(grammar, start, input, [Spec.Made{Spec.roundPoint(False{}, _, index, prefix, dot), k, Spec.alternateCount(_)}])
          %ek : AllOk(grammar, start, input, [Spec.Made{Spec.BracketAt{index, prefix, dot}, _, n}])
          (cpL, {==})
    case Spec.Positive{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Positive{}, True{}, []) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits([], grammar, Spec.times(List.length(&2, Spec.Tree, []), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells([], input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk([], True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == E : Nat}}
          +n = List.length(&2, +List<Spec.Item>, alts)
          +next = List.get(&2, Nat, input, E)
          +nk = Equal.trans(Nat, k, Nat.add(k, 0n), E, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), fin)
          +ek = Equal.sym(Nat, k, E, nk)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Positive{}, alts}}, itAt)
          cpL = U.after_cp(grammar, start, index, prefix, dot, n, Spec.Positive{}, alts, restO, next, itAt, restAt,
            U.leave_cp(Spec.isAlt(alts, n), grammar, start, alts, index, prefix, dot, False{}, True{}, restO, next, Pf.lt_irrefl(n), {==}, LP))
          %itS : AllOk(grammar, start, input, [Spec.Made{Spec.roundPoint(True{}, _, index, prefix, dot), k, Spec.alternateCount(_)}])
          %ek : AllOk(grammar, start, input, [Spec.Made{Spec.AfterRoundAt{index, prefix, dot}, _, n}])
          (cpL, {==})
    case Spec.Positive{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine, rest)))))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, [], True{}, False{}, index, prefix, dot, k)), Lemma.false_is_not_true(fine))

law rounds_pick_ok:
  for kind: Spec.Bracket
  for later: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +r: +List<Spec.Tree>
  for ready: Ready(True{}, grammar, start, input, root, Spec.Pick{a, ch} <> r, [], index, prefix, dot, i, k, kind, alts, restO, later, E)
  for ihCh: IH(grammar, start, input, root, rootFit, rootSp, ch)
  for ihR: IH(grammar, start, input, root, rootFit, rootSp, r)
  AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> r, True{}, later, index, prefix, dot, k))

def rounds_pick_ok(kind, later, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, alts, restO, E, a, ch, r, ready, ihCh, ihR):
  match kind later:
    case Spec.Group{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, rest))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> r, True{}, True{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Group{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, rest))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> r, True{}, False{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Optional{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, rest))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> r, True{}, True{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Optional{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, rest))):
          Empty.absurd(AllOk(grammar, start, input, Spec.madeIn(grammar, Spec.Pick{a, ch} <> r, True{}, False{}, index, prefix, dot, k)), Lemma.false_is_not_true(isL))
    case Spec.Closure{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Closure{}, True{}, Spec.Pick{a, ch} <> r) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits(Spec.Pick{a, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> r, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> r))) == E : Nat}}
          +tmR = Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(r, grammar, tmR), fR)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fRest = Lemma.and_true_right_side(h, Spec.fits(r, grammar, tmR), fR)
          +lc = Spec.leaves(ch)
          +lr = Spec.leaves(r)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lr, sp)
          +spR = G.spells_second(input, k, lc, lr, sp)
          +asc = G.nat_append_assoc(prefix, [dot], [a])
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, i, k)
          +wR = Spec.walk(r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, e)
          +inC = U.all_in_left(wC, wR, Spec.steps(root, 0n), inW)
          +inRr = U.all_in_right(wC, wR, Spec.steps(root, 0n), inW)
          +inCN = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k), Spec.steps(root, 0n)), Spec.allIn(wC, Spec.steps(root, 0n)), True{},
            Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, i, k), Spec.steps(root, 0n)), List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc)), inC)
          +cEqN = U.seq_child(grammar, index, prefix, dot, a, Spec.Closure{}, alts, even, itAt)
          +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])), Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])), Spec.altOf(alts, a),
            Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc), cEqN)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +finRr = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lr)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc, lr))), E, G.end_split(k, lc, lr), fin)
          +next = List.get(&2, Nat, input, k)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Closure{}, alts}}, itAt)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, Spec.Closure{}, alts, restO, next, itAt, restAt,
            U.alt_cp(Spec.isAlt(alts, a), grammar, start, alts, a, index, prefix, dot, False{}, True{}, restO, next, isA,
              U.first_from(lc, next, grammar, input, ch, Spec.altOf(alts, a), k, fC, {==}, spC, {==}, U.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine)))))
          okC = ihCh(False{}, False{}, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k, Spec.Closure{}, alts, restO, E, (fC, (spC, (inCN, (cEqN, evenC)))))
          okR = ihR(True{}, True{}, [], index, prefix, dot, i, e, Spec.Closure{}, alts, restO, E, (itAt, (restAt, (isL, (even, (fRest, (Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine), (spR, (inRr, (finRr, LP))))))))))
          %itS : AllOk(grammar, start, input, Spec.Made{Spec.roundPoint(True{}, _, index, prefix, dot), k, a} <> List.append(&2, Spec.Made, Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e)))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e), grammar, start, input, okC, okR))
    case Spec.Closure{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Closure{}, False{}, Spec.Pick{a, ch} <> r) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Closure{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits(Spec.Pick{a, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> r, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> r))) == E : Nat}}
          +tmR = Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(r, grammar, tmR), fR)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fRest = Lemma.and_true_right_side(h, Spec.fits(r, grammar, tmR), fR)
          +lc = Spec.leaves(ch)
          +lr = Spec.leaves(r)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lr, sp)
          +spR = G.spells_second(input, k, lc, lr, sp)
          +asc = G.nat_append_assoc(prefix, [dot], [a])
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, i, k)
          +wR = Spec.walk(r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, e)
          +inC = U.all_in_left(wC, wR, Spec.steps(root, 0n), inW)
          +inRr = U.all_in_right(wC, wR, Spec.steps(root, 0n), inW)
          +inCN = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k), Spec.steps(root, 0n)), Spec.allIn(wC, Spec.steps(root, 0n)), True{},
            Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, i, k), Spec.steps(root, 0n)), List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc)), inC)
          +cEqN = U.seq_child(grammar, index, prefix, dot, a, Spec.Closure{}, alts, even, itAt)
          +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])), Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])), Spec.altOf(alts, a),
            Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc), cEqN)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +finRr = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lr)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc, lr))), E, G.end_split(k, lc, lr), fin)
          +next = List.get(&2, Nat, input, k)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Closure{}, alts}}, itAt)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, Spec.Closure{}, alts, restO, next, itAt, restAt,
            U.alt_cp(Spec.isAlt(alts, a), grammar, start, alts, a, index, prefix, dot, False{}, True{}, restO, next, isA,
              U.first_from(lc, next, grammar, input, ch, Spec.altOf(alts, a), k, fC, {==}, spC, {==}, U.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine)))))
          okC = ihCh(False{}, False{}, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k, Spec.Closure{}, alts, restO, E, (fC, (spC, (inCN, (cEqN, evenC)))))
          okR = ihR(True{}, True{}, [], index, prefix, dot, i, e, Spec.Closure{}, alts, restO, E, (itAt, (restAt, (isL, (even, (fRest, (Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine), (spR, (inRr, (finRr, LP))))))))))
          %itS : AllOk(grammar, start, input, Spec.Made{Spec.roundPoint(False{}, _, index, prefix, dot), k, a} <> List.append(&2, Spec.Made, Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e)))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e), grammar, start, input, okC, okR))
    case Spec.Positive{} True{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Positive{}, True{}, Spec.Pick{a, ch} <> r) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits(Spec.Pick{a, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> r, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> r))) == E : Nat}}
          +tmR = Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(r, grammar, tmR), fR)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fRest = Lemma.and_true_right_side(h, Spec.fits(r, grammar, tmR), fR)
          +lc = Spec.leaves(ch)
          +lr = Spec.leaves(r)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lr, sp)
          +spR = G.spells_second(input, k, lc, lr, sp)
          +asc = G.nat_append_assoc(prefix, [dot], [a])
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, i, k)
          +wR = Spec.walk(r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, e)
          +inC = U.all_in_left(wC, wR, Spec.steps(root, 0n), inW)
          +inRr = U.all_in_right(wC, wR, Spec.steps(root, 0n), inW)
          +inCN = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k), Spec.steps(root, 0n)), Spec.allIn(wC, Spec.steps(root, 0n)), True{},
            Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, i, k), Spec.steps(root, 0n)), List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc)), inC)
          +cEqN = U.seq_child(grammar, index, prefix, dot, a, Spec.Positive{}, alts, even, itAt)
          +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])), Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])), Spec.altOf(alts, a),
            Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc), cEqN)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +finRr = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lr)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc, lr))), E, G.end_split(k, lc, lr), fin)
          +next = List.get(&2, Nat, input, k)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Positive{}, alts}}, itAt)
          cp = U.after_cp(grammar, start, index, prefix, dot, a, Spec.Positive{}, alts, restO, next, itAt, restAt,
            U.alt_cp(Spec.isAlt(alts, a), grammar, start, alts, a, index, prefix, dot, False{}, True{}, restO, next, isA,
              U.first_from(lc, next, grammar, input, ch, Spec.altOf(alts, a), k, fC, {==}, spC, {==}, U.consumes_child(a, ch, Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine)))))
          okC = ihCh(False{}, False{}, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k, Spec.Positive{}, alts, restO, E, (fC, (spC, (inCN, (cEqN, evenC)))))
          okR = ihR(True{}, True{}, [], index, prefix, dot, i, e, Spec.Positive{}, alts, restO, E, (itAt, (restAt, (isL, (even, (fRest, (Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(r), fine), (spR, (inRr, (finRr, LP))))))))))
          %itS : AllOk(grammar, start, input, Spec.Made{Spec.roundPoint(True{}, _, index, prefix, dot), k, a} <> List.append(&2, Spec.Made, Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e)))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e), grammar, start, input, okC, okR))
    case Spec.Positive{} False{}:
      match ready:
        case (itAt0, (restAt0, (isL, (even0, (fR0, (fine0, (sp0, (inW0, (fin0, LP))))))))):
          +fine = {fine0 : {U.roundsFine(Spec.Positive{}, False{}, Spec.Pick{a, ch} <> r) == True{} : Bool}}
          +itAt = {itAt0 : {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{Spec.Positive{}, alts}} : Maybe<&2, Spec.Item>}}
          +restAt = {restAt0 : {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>}}
          +even = {even0 : {L.evenLength(prefix) == True{} : Bool}}
          +fR = {fR0 : {Spec.fits(Spec.Pick{a, ch} <> r, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> r), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +sp = {sp0 : G.Spells(Spec.Pick{a, ch} <> r, input, k)}
          +inW = {inW0 : {Spec.allIn(Spec.walk(Spec.Pick{a, ch} <> r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool}}
          +fin = {fin0 : {Nat.add(k, List.length(&2, Nat, Spec.leaves(Spec.Pick{a, ch} <> r))) == E : Nat}}
          +tmR = Spec.times(List.length(&2, Spec.Tree, r), Spec.Brack{Spec.Group{}, alts})
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +hOk = Lemma.and_true_left(h, Spec.fits(r, grammar, tmR), fR)
          +isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fC = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
          +fRest = Lemma.and_true_right_side(h, Spec.fits(r, grammar, tmR), fR)
          +lc = Spec.leaves(ch)
          +lr = Spec.leaves(r)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lr, sp)
          +spR = G.spells_second(input, k, lc, lr, sp)
          +asc = G.nat_append_assoc(prefix, [dot], [a])
          +wC = Spec.walk(ch, False{}, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), 0n, i, k)
          +wR = Spec.walk(r, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, e)
          +inC = U.all_in_left(wC, wR, Spec.steps(root, 0n), inW)
          +inRr = U.all_in_right(wC, wR, Spec.steps(root, 0n), inW)
          +inCN = Equal.trans(Bool, Spec.allIn(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k), Spec.steps(root, 0n)), Spec.allIn(wC, Spec.steps(root, 0n)), True{},
            Equal.cong(+List<Nat>, Bool, v => Spec.allIn(Spec.walk(ch, False{}, index, v, 0n, i, k), Spec.steps(root, 0n)), List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc)), inC)
          +cEqN = U.seq_child(grammar, index, prefix, dot, a, Spec.Positive{}, alts, even, itAt)
          +cEq1 = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a])), Spec.sequenceAt(grammar, index, List.append(&2, Nat, prefix, [dot, a])), Spec.altOf(alts, a),
            Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), List.append(&2, Nat, prefix, [dot, a]), asc), cEqN)
          +evenC = Equal.trans(Bool, L.evenLength(List.append(&2, Nat, prefix, [dot, a])), L.evenLength(prefix), True{}, L.even_snoc(prefix, dot, a), even)
          +finRr = Equal.trans(Nat, Nat.add(e, List.length(&2, Nat, lr)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lc, lr))), E, G.end_split(k, lc, lr), fin)
          +next = List.get(&2, Nat, input, k)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot), Some{Spec.Brack{Spec.Positive{}, alts}}, itAt)
          cp = U.bracket_cp(grammar, start, index, prefix, dot, a, Spec.Positive{}, alts, restO, next, itAt, restAt,
            U.alt_cp(Spec.isAlt(alts, a), grammar, start, alts, a, index, prefix, dot, True{}, False{}, restO, next, isA,
              U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), k, i, e, wC, fC, spC, {==}, {==}, asc,
                U.end_walk(ch, Spec.altOf(alts, a), 0n, grammar, index, List.append(&2, Nat, List.append(&2, Nat, prefix, [dot]), [a]), i, k, e, fC, cEq1, {==}, {==}), inC)))
          okC = ihCh(False{}, False{}, Spec.altOf(alts, a), index, List.append(&2, Nat, prefix, [dot, a]), 0n, i, k, Spec.Positive{}, alts, restO, E, (fC, (spC, (inCN, (cEqN, evenC)))))
          okR = ihR(True{}, True{}, [], index, prefix, dot, i, e, Spec.Positive{}, alts, restO, E, (itAt, (restAt, (isL, (even, (fRest, (U.positive_rest(Spec.Pick{a, ch}, r, fine), (spR, (inRr, (finRr, LP))))))))))
          %itS : AllOk(grammar, start, input, Spec.Made{Spec.roundPoint(False{}, _, index, prefix, dot), k, a} <> List.append(&2, Spec.Made, Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e)))
          (cp, ok_append(Spec.madeIn(grammar, ch, False{}, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k), Spec.madeIn(grammar, r, True{}, True{}, index, prefix, dot, e), grammar, start, input, okC, okR))

# ======== EVERY CHOICE OF A FOREST PREDICTS ========

law made_ok:
  for f: +List<Spec.Tree>
  for rounds: Bool
  for later: Bool
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +rootSp: {Spec.leaves([root]) == input : +List<Nat>}
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +restO: +List<Spec.Item>
  for +E: Nat
  for ready: Ready(rounds, grammar, start, input, root, f, items, index, prefix, dot, i, k, kind, alts, restO, later, E)
  AllOk(grammar, start, input, Spec.madeIn(grammar, f, rounds, later, index, prefix, dot, k))

def made_ok(f, rounds, later, items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, E, ready):
  match f rounds:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      rounds_nil_ok(kind, later, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, alts, restO, E, ready)
    case Con{Spec.Leaf{+a}, +ts} False{}:
      leaf_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ts, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ts, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      node_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, q, ch, ts, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ch, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)), (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ts, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      pick_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, a, ch, ts, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ch, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)), (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ts, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      skip_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, ts, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ts, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      loop_ok(items, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, kind, alts, restO, later, E, rs, ts, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(rs, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)), (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ts, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Pick{+a, +ch}, +r} True{}:
      rounds_pick_ok(kind, later, grammar, start, input, root, rootFit, rootSp, index, prefix, dot, i, k, alts, restO, E, a, ch, r, ready, (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(ch, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)), (ro => la => it => ix => px => dx => ii => kx => kd => al => rO => ex => rd => made_ok(r, ro, la, it, grammar, start, input, root, rootFit, rootSp, ix, px, dx, ii, kx, kd, al, rO, ex, rd)))
    case Con{Spec.Leaf{x}, r} True{}:
      {==}
    case Con{Spec.Node{q, ch}, r} True{}:
      {==}
    case Con{Spec.Skip{}, r} True{}:
      {==}
    case Con{Spec.Loop{rs}, r} True{}:
      {==}

# Every choice a parse tree makes predicts the token where it is made.
law choices_ok:
  for tree: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  AllOk(grammar, start, input, Spec.choicesMade(grammar, start, tree))

def choices_ok(tree, grammar, start, input, fit, sp):
  match tree:
    case Spec.Node{+q, +ch}:
      +root = {Spec.Node{q, ch} : Spec.Tree}
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +hOk = Lemma.and_true_left(h, True{}, fit)
      +lhs = Lemma.and_true_left(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +fC = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
      +spC = G.root_spells(input, q, ch, sp)
      +wC = Spec.walk(ch, False{}, q, [], 0n, 0n, 0n)
      +inC = U.all_in_refl(wC)
      +e = Nat.add(0n, List.length(&2, Nat, Spec.leaves(ch)))
      +next = List.get(&2, Nat, input, 0n)
      cp = U.nt_cp(Spec.lhsIs(grammar, q, start), grammar, start, q, next, lhs,
        U.predicts_in(next, grammar, start, input, root, fit, sp, ch, Spec.rhsOf(grammar, q), q, [], [], 0n, 0n, e, wC, fC, spC, {==}, {==}, {==},
          U.end_walk(ch, Spec.rhsOf(grammar, q), 0n, grammar, q, [], 0n, 0n, e, fC, {==}, {==}, {==}), inC))
      (cp, made_ok(ch, False{}, False{}, Spec.rhsOf(grammar, q), grammar, start, input, root, fit, sp, q, [], 0n, 0n, 0n, Spec.Group{}, [], [], 0n, (fC, (spC, (inC, ({==}, {==}))))))
    case Spec.Leaf{kind}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Pick{a, ch}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Skip{}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))
    case Spec.Loop{rs}:
      Empty.absurd(AllOk(grammar, start, input, []), Lemma.false_is_not_true(fit))

law transport_cp:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +c: Maybe<&2, Spec.Choice>
  for +n1: Maybe<&2, Nat>
  for +n2: Maybe<&2, Nat>
  for +e: {n1 == n2 : Maybe<&2, Nat>}
  for cp: Spec.ChoicePredicts(grammar, start, c, n1)
  Spec.ChoicePredicts(grammar, start, c, n2)

def transport_cp(grammar, start, c, n1, n2, e, cp):
  %e : Spec.ChoicePredicts(grammar, start, c, _)
  cp

# ======== THE LAW ========

law ll1_at:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input1: +List<Nat>
  for +input2: +List<Nat>
  for +tree1: Spec.Tree
  for +tree2: Spec.Tree
  for +point: Spec.ChoicePoint
  for +pos: Nat
  for +choice1: Nat
  for +choice2: Nat
  for ll1: Spec.LL1At(grammar, start, point)
  for +fit1: {Spec.fits([tree1], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp1: {Spec.leaves([tree1]) == input1 : +List<Nat>}
  for +fit2: {Spec.fits([tree2], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp2: {Spec.leaves([tree2]) == input2 : +List<Nat>}
  for +next: {List.get(&2, Nat, input1, pos) == List.get(&2, Nat, input2, pos) : Maybe<&2, Nat>}
  for made1: Spec.Among(Spec.Made{point, pos, choice1}, Spec.choicesMade(grammar, start, tree1))
  for made2: Spec.Among(Spec.Made{point, pos, choice2}, Spec.choicesMade(grammar, start, tree2))
  {choice1 == choice2 : Nat}

def ll1_at(grammar, start, input1, input2, tree1, tree2, point, pos, choice1, choice2, ll1, fit1, sp1, fit2, sp2, next, made1, made2):
  +n1 = List.get(&2, Nat, input1, pos)
  +n2 = List.get(&2, Nat, input2, pos)
  ok1 = among_ok(Spec.choicesMade(grammar, start, tree1), Spec.Made{point, pos, choice1}, grammar, start, input1, made1, choices_ok(tree1, grammar, start, input1, fit1, sp1))
  ok2 = among_ok(Spec.choicesMade(grammar, start, tree2), Spec.Made{point, pos, choice2}, grammar, start, input2, made2, choices_ok(tree2, grammar, start, input2, fit2, sp2))
  L.either_case({choice1 == choice2 : Nat}, {Nat.is_eq(choice1, choice2) == False{} : Bool}, {choice1 == choice2 : Nat}, U.decide(Nat.is_eq(choice1, choice2), choice1, choice2, {==}),
    same => same,
    neq => Empty.absurd({choice1 == choice2 : Nat}, ll1(choice1, choice2, n1, neq, ok1, transport_cp(grammar, start, Spec.choiceOf(grammar, point, choice2), n2, n1, Equal.sym(Maybe<&2, Nat>, n1, n2, next), ok2))))

# The law ll1_at.
def Laws.ll1_at(grammar, start, input1, input2, tree1, tree2, point, pos, choice1, choice2, ll1, fit1, sp1, fit2, sp2, next, made1, made2):
  ll1_at(grammar, start, input1, input2, tree1, tree2, point, pos, choice1, choice2, ll1, fit1, sp1, fit2, sp2, next, made1, made2)
