import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_PRUNE.bend as P
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# WHAT A SUB-PARSE AND THE EXACT SET SAY ABOUT TREES: facts shared by the oracle proofs
# (PROOF_PREFER, PROOF_GUARD, PROOF_EXTENT). A sub-parse that finds no end for its extra
# production leaves no forest for its items over those tokens; every parse tree's steps
# are in the exact set; where a walk goes on after a tree; the step that ends a sequence.

# @prefer AND @avoid CHOOSE EXACTLY THE SELECTED TREES: prefer_avoid_exact.
#
# Both halves walk a parse tree the way `Spec.walk` lists its steps, next to
# `Spec.Unbeaten`, which walks it the same way.
#
# A tree that uses only kept steps is unbeaten. At every node (and every pick) the
# step that completes it is kept, so the oracle's verdict on it was Keep: for every
# sibling of higher rank, the checked parser found no tree over the node's tokens. A
# rival would be such a tree, and `gll_every_parse_step` says the parser misses none.
#
# A unbeaten tree uses only kept steps. A step that completes no choice is always kept.
# One that completes a node is in the exact set; were it removed, its certificate would
# be a rival of the node, which a unbeaten tree has not. The certificate's forest avoids
# the set C; the nonterminals above the node over the same tokens are in C, because each
# of them has a step in the exact set that the rule growing C fires on, and C is closed.

# ======== SMALL FACTS ========

law nats_eq_refl:
  for xs: +List<Nat>
  {Gll.natsEq(xs, xs) == True{} : Bool}

def nats_eq_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Nat.is_eq(x, x), Gll.natsEq(rest, rest), Lemma.nat_eq_refl(x), nats_eq_refl(rest))

# The tokens from k to the end of what is spelled at k are what is spelled.
law tokens_spelled:
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  {Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w))) == w : +List<Nat>}

def tokens_spelled(input, k, w, sp):
  %Equal.sym(Nat, Nat.sub(Nat.add(k, List.length(&2, Nat, w)), k), List.length(&2, Nat, w), Lemma.sub_add_left(k, List.length(&2, Nat, w))) : {Lemma.slice(input, k, _) == w : +List<Nat>}
  Equal.sym(+List<Nat>, w, Lemma.slice(input, k, List.length(&2, Nat, w)), sp)

law member_app_right:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  {Spec.bsrMember(e, List.append(&2, Spec.Bsr, xs, ys)) == True{} : Bool}

def member_app_right(xs, ys, e, m):
  match xs:
    case Nil{}:
      m
    case Con{+x, +rest}:
      R.bsr_member_cons(e, x, List.append(&2, Spec.Bsr, rest, ys), member_app_right(rest, ys, e, m))

# ======== WHAT THE ORACLE'S ANSWER SAYS ========

law prefer_pick_facts:
  for ok: Bool
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for got: {Prefer.preferPick(ok, ys) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  {ok == True{} : Bool} & {ys == set : +List<Spec.Bsr>}

def prefer_pick_facts(ok, ys, set, got):
  match ok:
    case True{}:
      ({==}, Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{ys}, Some{set}, got))
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {ys == set : +List<Spec.Bsr>}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

def boolOr(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case Some{+b}:
      b
    case None{}:
      False{}

def isNoneB(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case Some{b}:
      False{}
    case None{}:
      True{}

# ======== WHAT A SUB-PARSE SAYS ========

# The parser handed out a set without the end of production idx over all len tokens.
def NoEnd(+found: Maybe<&2, +List<Spec.Bsr>>, +idx: Nat, +n: Nat, +len: Nat) -> Type:
  &set: +List<Spec.Bsr> -> {found == Some{set} : Maybe<&2, +List<Spec.Bsr>>} & {Prefer.anyEndsAll(set, idx, n, len) == False{} : Bool}

law derived_in_false:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +idx: Nat
  for +n: Nat
  for +len: Nat
  for e: {Prefer.derivedIn(found, idx, n, len) == Some{False{}} : Maybe<&2, Bool>}
  NoEnd(found, idx, n, len)

def derived_in_false(found, idx, n, len, e):
  match found:
    case Some{+set}:
      (set, ({==}, Equal.cong(Maybe<&2, Bool>, Bool, v => boolOr(v), Some{Prefer.anyEndsAll(set, idx, n, len)}, Some{False{}}, e)))
    case None{}:
      Empty.absurd(NoEnd(None{}, idx, n, len), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Bool>, Bool, v => isNoneB(v), None{}, Some{False{}}, e)))

# A no from the sub-parse: the checked parser handed out a set without the end of the
# extra production over all the tokens.
law derives_false:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +input: +List<Nat>
  for +k: Nat
  for +j: Nat
  for e: {Prefer.derivesHere(fuel, grammar, items, input, k, j) == Some{False{}} : Maybe<&2, Bool>}
  NoEnd(Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, j)), List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, Prefer.tokensFrom(input, k, j)))

def derives_false(fuel, grammar, items, input, k, j, e):
  +w = Prefer.tokensFrom(input, k, j)
  derived_in_false(Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), w), List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, w), e)

law ends_all_at:
  for +idx: Nat
  for +n: Nat
  for +len: Nat
  for +p: Nat
  {Prefer.endsAll(idx, n, len, Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}) == True{} : Bool}

def ends_all_at(idx, n, len, p):
  Lemma.and_true_intro(Nat.is_eq(idx, idx), Bool.and(Gll.natsEq([n], [n]), Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(len, len))), Lemma.nat_eq_refl(idx),
    Lemma.and_true_intro(Gll.natsEq([n], [n]), Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(len, len)), nats_eq_refl([n]),
      Lemma.and_true_intro(Nat.is_eq(0n, 0n), Nat.is_eq(len, len), {==}, Lemma.nat_eq_refl(len))))

law ends_pick:
  for +idx: Nat
  for +n: Nat
  for +len: Nat
  for +p: Nat
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for cases: Either<{Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len} == x : Spec.Bsr}, {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}, rest) == True{} : Bool}>
  for searchRest: {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}, rest) == True{} : Bool} -> {Prefer.anyEndsAll(rest, idx, n, len) == True{} : Bool}
  {Prefer.anyEndsAll(x <> rest, idx, n, len) == True{} : Bool}

def ends_pick(idx, n, len, p, x, rest, cases, searchRest):
  match cases:
    case Inl{same}:
      %same : {Bool.or(Prefer.endsAll(idx, n, len, _), Prefer.anyEndsAll(rest, idx, n, len)) == True{} : Bool}
      Lemma.or_true_left_intro(Prefer.endsAll(idx, n, len, Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}), Prefer.anyEndsAll(rest, idx, n, len), ends_all_at(idx, n, len, p))
    case Inr{later}:
      Lemma.or_true_right_intro(Prefer.endsAll(idx, n, len, x), Prefer.anyEndsAll(rest, idx, n, len), searchRest(later))

# A set with the end of production idx over all the tokens has it, by `anyEndsAll`.
law ends_of_member:
  for set: +List<Spec.Bsr>
  for +idx: Nat
  for +n: Nat
  for +len: Nat
  for +p: Nat
  for m: {Spec.bsrMember(Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}, set) == True{} : Bool}
  {Prefer.anyEndsAll(set, idx, n, len) == True{} : Bool}

def ends_of_member(set, idx, n, len, p, m):
  match set:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, G.ebnf_not_in_empty(Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}, m))
    case Con{+x, +rest}:
      ends_pick(idx, n, len, p, x, rest, G.ebnf_member_cases(Spec.Bsr{Spec.Slot{idx, [n]}, 0n, p, len}, x, rest, m),
        later => ends_of_member(rest, idx, n, len, p, later))

# Every step of every parse tree is in a set that a FoundSteps answer handed out.
law steps_in_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for every: R.FoundSteps(found, grammar, start, input)
  for got: {found == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def steps_in_found(found, grammar, start, input, set, every, got):
  match found:
    case Some{+ys}:
      %Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{ys}, Some{set}, got) : R.StepsIn(grammar, start, input, _)
      every
    case None{}:
      Empty.absurd(R.StepsIn(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# ======== ONE MORE PRODUCTION ========

law lhs_is_ext:
  for +grammar: +List<Spec.Production>
  for +extra: +List<Spec.Production>
  for q: Nat
  for +x: Nat
  for e: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {Spec.lhsIs(List.append(&2, Spec.Production, grammar, extra), q, x) == True{} : Bool}

def lhs_is_ext(grammar, extra, q, x, e):
  match grammar q:
    case Nil{} _:
      Empty.absurd({Spec.lhsIs(extra, q, x) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      e
    case Con{Spec.Production{+pl, +pr}, +rest} 1n+i:
      lhs_is_ext(rest, extra, i, x, e)

law rhs_of_ext:
  for +grammar: +List<Spec.Production>
  for +extra: +List<Spec.Production>
  for q: Nat
  for +x: Nat
  for e: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {Spec.rhsOf(List.append(&2, Spec.Production, grammar, extra), q) == Spec.rhsOf(grammar, q) : +List<Spec.Item>}

def rhs_of_ext(grammar, extra, q, x, e):
  match grammar q:
    case Nil{} _:
      Empty.absurd({Spec.rhsOf(extra, q) == [] : +List<Spec.Item>}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      {==}
    case Con{Spec.Production{+pl, +pr}, +rest} 1n+i:
      rhs_of_ext(rest, extra, i, x, e)

law lhs_is_last:
  for grammar: +List<Spec.Production>
  for +l: Nat
  for +r: +List<Spec.Item>
  {Spec.lhsIs(List.append(&2, Spec.Production, grammar, [Spec.Production{l, r}]), List.length(&2, Spec.Production, grammar), l) == True{} : Bool}

def lhs_is_last(grammar, l, r):
  match grammar:
    case Nil{}:
      Lemma.nat_eq_refl(l)
    case Con{Spec.Production{+pl, +pr}, +rest}:
      lhs_is_last(rest, l, r)

law rhs_of_last:
  for grammar: +List<Spec.Production>
  for +l: Nat
  for +r: +List<Spec.Item>
  {Spec.rhsOf(List.append(&2, Spec.Production, grammar, [Spec.Production{l, r}]), List.length(&2, Spec.Production, grammar)) == r : +List<Spec.Item>}

def rhs_of_last(grammar, l, r):
  match grammar:
    case Nil{}:
      {==}
    case Con{Spec.Production{+pl, +pr}, +rest}:
      rhs_of_last(rest, l, r)

# A forest that fits under the grammar still fits with more productions after it.
law fits_ext:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +extra: +List<Spec.Production>
  for items: +List<Spec.Item>
  for e: {Spec.fits(forest, grammar, items) == True{} : Bool}
  {Spec.fits(forest, List.append(&2, Spec.Production, grammar, extra), items) == True{} : Bool}

def fits_ext(forest, grammar, extra, items, e):
  match forest items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{it, rest}:
      Empty.absurd({Spec.fits([], List.append(&2, Spec.Production, grammar, extra), it <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{t, ts} Nil{}:
      Empty.absurd({Spec.fits(t <> ts, List.append(&2, Spec.Production, grammar, extra), []) == True{} : Bool}, Fits.fits_cons_nil(t, ts, grammar, e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      +both = e
      Lemma.and_true_intro(Nat.is_eq(kind, k), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Leaf{+kind}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({Spec.fits(Spec.Leaf{kind} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Eps{} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)
      +l = Lemma.and_true_left(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)
      +rEq = rhs_of_ext(grammar, extra, q, id, l)
      +chOk = Equal.trans(Bool, Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.rhsOf(List.append(&2, Spec.Production, grammar, extra), q)), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.rhsOf(grammar, q)), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), v), Spec.rhsOf(List.append(&2, Spec.Production, grammar, extra), q), Spec.rhsOf(grammar, q), rEq), fits_ext(ch, grammar, extra, Spec.rhsOf(grammar, q), Lemma.and_true_right_side(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hh)))
      Lemma.and_true_intro(Bool.and(Spec.lhsIs(List.append(&2, Spec.Production, grammar, extra), q, id), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.rhsOf(List.append(&2, Spec.Production, grammar, extra), q))), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_intro(Spec.lhsIs(List.append(&2, Spec.Production, grammar, extra), q, id), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.rhsOf(List.append(&2, Spec.Production, grammar, extra), q)), lhs_is_ext(grammar, extra, q, id, l), chOk), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Bool.and(Spec.lhsIs(grammar, q, id), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q))), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Node{+q, +ch}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({Spec.fits(Spec.Node{q, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Eps{} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.altOf(alts, a))), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.altOf(alts, a)), Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh), fits_ext(ch, grammar, extra, Spec.altOf(alts, a), Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh))), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)
      Lemma.and_true_intro(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.altOf(alts, a))), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, List.append(&2, Spec.Production, grammar, extra), Spec.altOf(alts, a)), Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh), fits_ext(ch, grammar, extra, Spec.altOf(alts, a), Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hh))), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Bool.and(Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Pick{+a, +ch}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({Spec.fits(Spec.Pick{a, ch} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Eps{} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      fits_ext(ts, grammar, extra, rest, e)
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Skip{} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Positive{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Skip{}, +ts} Con{Spec.Eps{}, +rest}:
      fits_ext(ts, grammar, extra, rest, e)
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Sym{Spec.Terminal{+k}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Terminal{k}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Sym{Spec.Nonterminal{+id}}, +rest}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Sym{Spec.Nonterminal{id}} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Group{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Optional{}, +alts}, +rest}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Brack{Spec.Optional{}, alts} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Closure{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, List.append(&2, Spec.Production, grammar, extra), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, List.append(&2, Spec.Production, grammar, extra), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh), fits_ext(rs, grammar, extra, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh))), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Brack{Spec.Positive{}, +alts}, +rest}:
      +both = e
      +hh = Lemma.and_true_left(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)
      Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, List.append(&2, Spec.Production, grammar, extra), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, List.append(&2, Spec.Production, grammar, extra), rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, List.append(&2, Spec.Production, grammar, extra), Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh), fits_ext(rs, grammar, extra, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}), Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts})), hh))), fits_ext(ts, grammar, extra, rest, Lemma.and_true_right_side(Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, alts}))), Spec.fits(ts, grammar, rest), both)))
    case Con{Spec.Loop{+rs}, +ts} Con{Spec.Eps{}, +rest}:
      Empty.absurd({Spec.fits(Spec.Loop{rs} <> ts, List.append(&2, Spec.Production, grammar, extra), Spec.Eps{} <> rest) == True{} : Bool}, Lemma.false_is_not_true(e))

# ======== THE STEP THAT ENDS A SEQUENCE ========

# The walk of a forest has a step for the slot after its last tree, ending where the
# forest ends, from some pivot.
def LastIn(+forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat) -> Type:
  &piv: Nat -> {Spec.bsrMember(Spec.at(index, prefix, Nat.add(dot, List.length(&2, Spec.Tree, forest)), i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(forest)))), Spec.walk(forest, False{}, index, prefix, dot, i, k)) == True{} : Bool}

# Where the walk goes on after a tree.
def endOf(t: Spec.Tree, +k: Nat) -> Nat:
  match t:
    case Spec.Leaf{kind}:
      1n+k
    case Spec.Node{q, ch}:
      Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
    case Spec.Pick{a, ch}:
      Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))
    case Spec.Skip{}:
      k
    case Spec.Loop{rs}:
      Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))

law last_one_mem:
  for t: Spec.Tree
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  {Spec.bsrMember(Spec.at(index, prefix, Nat.add(dot, 1n), i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves([t])))), Spec.walk([t], False{}, index, prefix, dot, i, k)) == True{} : Bool}

def last_one_mem(t, index, prefix, dot, i, k):
  match t:
    case Spec.Leaf{+kind}:
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Spec.bsrMember(Spec.at(index, prefix, _, i, k, Nat.add(k, 1n)), Spec.walk([Spec.Leaf{kind}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k)) : {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, _), Spec.walk([Spec.Leaf{kind}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_head(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), [])
    case Spec.Node{+q, +ch}:
      +lch = Spec.leaves(ch)
      +rest = List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, lch))))
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Spec.bsrMember(Spec.at(index, prefix, _, i, k, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, [])))), Spec.walk([Spec.Node{q, ch}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_alone(k, lch) : {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, _), Spec.walk([Spec.Node{q, ch}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_head(Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, lch))), rest)
    case Spec.Pick{+a, +ch}:
      +lch = Spec.leaves(ch)
      +rest = List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, lch))))
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Spec.bsrMember(Spec.at(index, prefix, _, i, k, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, [])))), Spec.walk([Spec.Pick{a, ch}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_alone(k, lch) : {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, _), Spec.walk([Spec.Pick{a, ch}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_head(Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, lch))), rest)
    case Spec.Skip{}:
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Spec.bsrMember(Spec.at(index, prefix, _, i, k, Nat.add(k, 0n)), Spec.walk([Spec.Skip{}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)) : {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, _), Spec.walk([Spec.Skip{}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_head(Spec.at(index, prefix, 1n+dot, i, k, k), [])
    case Spec.Loop{+rs}:
      +lrs = Spec.leaves(rs)
      +rest = List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk([], False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, lrs))))
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Spec.bsrMember(Spec.at(index, prefix, _, i, k, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lrs, [])))), Spec.walk([Spec.Loop{rs}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_alone(k, lrs) : {Spec.bsrMember(Spec.at(index, prefix, 1n+dot, i, k, _), Spec.walk([Spec.Loop{rs}], False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_head(Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, lrs))), rest)

law last_nil_mem:
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  {Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, Nat.add(k, 0n)), Spec.walk([], False{}, index, prefix, 0n, i, k)) == True{} : Bool}

def last_nil_mem(index, prefix, i, k):
  %Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)) : {Spec.bsrMember(Spec.at(index, prefix, 0n, i, k, _), Spec.walk([], False{}, index, prefix, 0n, i, k)) == True{} : Bool}
  R.bsr_member_head(Spec.at(index, prefix, 0n, i, k, k), [])

law last_more_mem:
  for t: Spec.Tree
  for +t2: Spec.Tree
  for +ts2: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +piv: Nat
  for ih: {Spec.bsrMember(Spec.at(index, prefix, Nat.add(1n+dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(endOf(t, k), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, endOf(t, k))) == True{} : Bool}
  {Spec.bsrMember(Spec.at(index, prefix, Nat.add(dot, List.length(&2, Spec.Tree, t <> t2 <> ts2)), i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(t <> t2 <> ts2)))), Spec.walk(t <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}

def last_more_mem(t, t2, ts2, index, prefix, dot, i, k, piv, ih):
  match t:
    case Spec.Leaf{+kind}:
      %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, t2 <> ts2)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, t2 <> ts2))) : {Spec.bsrMember(Spec.at(index, prefix, _, i, piv, Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.walk(Spec.Leaf{kind} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, Spec.leaves(t2 <> ts2))), 1n+Nat.add(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2))), Lemma.add_succ_right(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2)))) : {Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, _), Spec.walk(Spec.Leaf{kind} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_cons(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, 1n+Nat.add(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.at(index, prefix, 1n+dot, i, k, 1n+k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, 1n+k), ih)
    case Spec.Node{+q, +ch}:
      %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, t2 <> ts2)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, t2 <> ts2))) : {Spec.bsrMember(Spec.at(index, prefix, _, i, piv, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(t2 <> ts2))))), Spec.walk(Spec.Node{q, ch} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_split(k, Spec.leaves(ch), Spec.leaves(t2 <> ts2)) : {Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, _), Spec.walk(Spec.Node{q, ch} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_cons(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), member_app_right(Spec.walk(ch, False{}, q, [], 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), ih))
    case Spec.Pick{+a, +ch}:
      %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, t2 <> ts2)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, t2 <> ts2))) : {Spec.bsrMember(Spec.at(index, prefix, _, i, piv, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(t2 <> ts2))))), Spec.walk(Spec.Pick{a, ch} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_split(k, Spec.leaves(ch), Spec.leaves(t2 <> ts2)) : {Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, _), Spec.walk(Spec.Pick{a, ch} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_cons(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), List.append(&2, Spec.Bsr, Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))))), member_app_right(Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ch)))), Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(ch))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), ih))
    case Spec.Skip{}:
      %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, t2 <> ts2)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, t2 <> ts2))) : {Spec.bsrMember(Spec.at(index, prefix, _, i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.walk(Spec.Skip{} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_cons(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(k, List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.at(index, prefix, 1n+dot, i, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, k), ih)
    case Spec.Loop{+rs}:
      %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Spec.Tree, t2 <> ts2)), 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), Lemma.add_succ_right(dot, List.length(&2, Spec.Tree, t2 <> ts2))) : {Spec.bsrMember(Spec.at(index, prefix, _, i, piv, Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, Spec.leaves(rs), Spec.leaves(t2 <> ts2))))), Spec.walk(Spec.Loop{rs} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      %G.end_split(k, Spec.leaves(rs), Spec.leaves(t2 <> ts2)) : {Spec.bsrMember(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, _), Spec.walk(Spec.Loop{rs} <> t2 <> ts2, False{}, index, prefix, dot, i, k)) == True{} : Bool}
      R.bsr_member_cons(Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), Spec.at(index, prefix, 1n+dot, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), List.append(&2, Spec.Bsr, Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))))), member_app_right(Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k), Spec.walk(t2 <> ts2, False{}, index, prefix, 1n+dot, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(rs)))), Spec.at(index, prefix, 1n+Nat.add(dot, List.length(&2, Spec.Tree, t2 <> ts2)), i, piv, Nat.add(Nat.add(k, List.length(&2, Nat, Spec.leaves(rs))), List.length(&2, Nat, Spec.leaves(t2 <> ts2)))), ih))

law last_more:
  for t: Spec.Tree
  for +t2: Spec.Tree
  for +ts2: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for ih: LastIn(t2 <> ts2, index, prefix, 1n+dot, i, endOf(t, k))
  LastIn(t <> t2 <> ts2, index, prefix, dot, i, k)

def last_more(t, t2, ts2, index, prefix, dot, i, k, ih):
  match ih:
    case (piv0, m):
      +piv = {piv0 : Nat}
      (piv, last_more_mem(t, t2, ts2, index, prefix, dot, i, k, piv, m))

law last_step:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  LastIn(t <> ts, index, prefix, dot, i, k)

def last_step(ts, t, index, prefix, dot, i, k):
  match ts:
    case Nil{}:
      (k, last_one_mem(t, index, prefix, dot, i, k))
    case Con{+t2, +ts2}:
      last_more(t, t2, ts2, index, prefix, dot, i, k, last_step(ts2, t2, index, prefix, 1n+dot, i, endOf(t, k)))

# The step that ends a whole sequence, read from its start.
law last_any:
  for forest: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  LastIn(forest, index, prefix, 0n, i, k)

def last_any(forest, index, prefix, i, k):
  match forest:
    case Nil{}:
      (k, last_nil_mem(index, prefix, i, k))
    case Con{+t, +ts}:
      last_step(ts, t, index, prefix, 0n, i, k)

law refute_last:
  for +set: +List<Spec.Bsr>
  for +lg: Nat
  for +f: +List<Spec.Tree>
  for +n: Nat
  for +len: Nat
  for +countEq: {List.length(&2, Spec.Tree, f) == n : Nat}
  for +lenEq: {List.length(&2, Nat, Spec.leaves(f)) == len : Nat}
  for +allT: {Spec.allIn(Spec.walk(f, False{}, lg, [], 0n, 0n, 0n), set) == True{} : Bool}
  for +noEnd: {Prefer.anyEndsAll(set, lg, n, len) == False{} : Bool}
  for last: LastIn(f, lg, [], 0n, 0n, 0n)
  Empty

def refute_last(set, lg, f, n, len, countEq, lenEq, allT, noEnd, last):
  match last:
    case (piv0, m):
      +piv = {piv0 : Nat}
      +nf = List.length(&2, Spec.Tree, f)
      +lf = List.length(&2, Nat, Spec.leaves(f))
      +mS = G.ebnf_all_in_member(Spec.walk(f, False{}, lg, [], 0n, 0n, 0n), set, Spec.at(lg, [], nf, 0n, piv, lf), allT, m)
      +ends = ends_of_member(set, lg, nf, lf, piv, mS)
      +e1 = Equal.cong(Nat, Bool, v => Prefer.anyEndsAll(set, lg, v, lf), nf, n, countEq)
      +e2 = Equal.cong(Nat, Bool, v => Prefer.anyEndsAll(set, lg, n, v), lf, len, lenEq)
      +isT = Equal.trans(Bool, Prefer.anyEndsAll(set, lg, n, len), Prefer.anyEndsAll(set, lg, nf, lf), True{}, Equal.sym(Bool, Prefer.anyEndsAll(set, lg, nf, lf), Prefer.anyEndsAll(set, lg, n, len), Equal.trans(Bool, Prefer.anyEndsAll(set, lg, nf, lf), Prefer.anyEndsAll(set, lg, n, lf), Prefer.anyEndsAll(set, lg, n, len), e1, e2)), ends)
      Lemma.true_is_not_false(Equal.trans(Bool, True{}, Prefer.anyEndsAll(set, lg, n, len), False{}, Equal.sym(Bool, Prefer.anyEndsAll(set, lg, n, len), True{}, isT), noEnd))

law refute_with:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +set: +List<Spec.Bsr>
  for +eqC: {Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  for +noEnd: {Prefer.anyEndsAll(set, List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w))))) == False{} : Bool}
  Empty

def refute_with(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, set, eqC, noEnd):
  +fresh = Prefer.freshNt(grammar)
  +g2 = Prefer.extended(grammar, items)
  +lg = List.length(&2, Spec.Production, grammar)
  +toks = Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))
  +tEq = tokens_spelled(input, k, w, sp)
  +lf = Spec.leaves(f)
  +fitsF2 = Equal.trans(Bool, Spec.fits(f, g2, Spec.rhsOf(g2, lg)), Spec.fits(f, g2, items), True{}, Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(f, g2, v), Spec.rhsOf(g2, lg), items, rhs_of_last(grammar, fresh, items)), fits_ext(f, grammar, [Spec.Production{fresh, items}], items, fitF))
  +fitT = Lemma.and_true_intro(Bool.and(Spec.lhsIs(g2, lg, fresh), Spec.fits(f, g2, Spec.rhsOf(g2, lg))), Spec.fits([], g2, []), Lemma.and_true_intro(Spec.lhsIs(g2, lg, fresh), Spec.fits(f, g2, Spec.rhsOf(g2, lg)), lhs_is_last(grammar, fresh, items), fitsF2), {==})
  +lfToks = Equal.trans(+List<Nat>, lf, w, toks, leavesF, Equal.sym(+List<Nat>, toks, w, tEq))
  +leavesT = Equal.trans(+List<Nat>, List.append(&2, Nat, lf, []), lf, toks, Lemma.append_nil_right(lf), lfToks)
  stepsIn = steps_in_found(Check.checkedSteps(fuel, g2, fresh, toks), g2, fresh, toks, set, R.checked_found(fuel, g2, fresh, toks), eqC)
  +allT = stepsIn(Spec.Node{lg, f}, fitT, leavesT)
  +countEq = Fits.fits_count(f, grammar, items, fitF)
  +lenEq = Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), lf, toks, lfToks)
  refute_last(set, lg, f, List.length(&2, Spec.Item, items), List.length(&2, Nat, toks), countEq, lenEq, allT, noEnd, last_any(f, lg, [], 0n, 0n))

law refute_pair:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for +set: +List<Spec.Bsr>
  for facts: {Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))) == Some{set} : Maybe<&2, +List<Spec.Bsr>>} & {Prefer.anyEndsAll(set, List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w))))) == False{} : Bool}
  Empty

def refute_pair(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, set, facts):
  match facts:
    case (eqC, noEnd):
      refute_with(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, set, eqC, noEnd)

law refute_found:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for nf: NoEnd(Check.checkedSteps(fuel, Prefer.extended(grammar, items), Prefer.freshNt(grammar), Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))), List.length(&2, Spec.Production, grammar), List.length(&2, Spec.Item, items), List.length(&2, Nat, Prefer.tokensFrom(input, k, Nat.add(k, List.length(&2, Nat, w)))))
  Empty

def refute_found(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, nf):
  match nf:
    case (set0, facts):
      +set = {set0 : +List<Spec.Bsr>}
      refute_pair(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, set, facts)

# If the sub-parse said no, no forest for the items spells the tokens.
law sub_parse_refutes:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +input: +List<Nat>
  for +k: Nat
  for +w: +List<Nat>
  for +sp: {w == Lemma.slice(input, k, List.length(&2, Nat, w)) : +List<Nat>}
  for +f: +List<Spec.Tree>
  for +fitF: {Spec.fits(f, grammar, items) == True{} : Bool}
  for +leavesF: {Spec.leaves(f) == w : +List<Nat>}
  for dh: {Prefer.derivesHere(fuel, grammar, items, input, k, Nat.add(k, List.length(&2, Nat, w))) == Some{False{}} : Maybe<&2, Bool>}
  Empty

def sub_parse_refutes(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, dh):
  refute_found(fuel, grammar, items, input, k, w, sp, f, fitF, leavesF, derives_false(fuel, grammar, items, input, k, Nat.add(k, List.length(&2, Nat, w)), dh))

def isNoneItem(m: Maybe<&2, Spec.Item>) -> Bool:
  match m:
    case Some{x}:
      False{}
    case None{}:
      True{}

law end_of_one:
  for t: Spec.Tree
  for +k: Nat
  {endOf(t, k) == Nat.add(k, List.length(&2, Nat, Spec.leaves([t]))) : Nat}

def end_of_one(t, k):
  match t:
    case Spec.Leaf{kind}:
      Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k))
    case Spec.Node{q, +ch}:
      G.end_alone(k, Spec.leaves(ch))
    case Spec.Pick{a, +ch}:
      G.end_alone(k, Spec.leaves(ch))
    case Spec.Skip{}:
      Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k))
    case Spec.Loop{+rs}:
      G.end_alone(k, Spec.leaves(rs))

# ======== THE LAW ========

law exact_pick_steps:
  for ok: Bool
  for +ps: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +eqF: {Prune.prunedSteps(fuel, grammar, start, input) == Some{ps} : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Exact.exactPick(ok, ps) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def exact_pick_steps(ok, ps, set, fuel, grammar, start, input, eqF, got):
  match ok:
    case True{}:
      +same = Equal.cong(Maybe<&2, +List<Spec.Bsr>>, +List<Spec.Bsr>, v => G.stepsOr(v), Some{ps}, Some{set}, got)
      +filtered = Prune.roundRule(Check.checkedSteps(fuel, grammar, start, input), grammar)
      every = P.prune_found_eq(filtered, fuel, grammar, start, input, R.rounds_found(fuel, grammar, start, input), Prune.prunedSteps(fuel, grammar, start, input), {==})
      +eqSet = Equal.trans(Maybe<&2, +List<Spec.Bsr>>, Prune.prunedSteps(fuel, grammar, start, input), Some{ps}, Some{set}, eqF, Equal.cong(+List<Spec.Bsr>, Maybe<&2, +List<Spec.Bsr>>, v => Some{v}, ps, set, same))
      steps_in_found(Prune.prunedSteps(fuel, grammar, start, input), grammar, start, input, set, every, eqSet)
    case False{}:
      Empty.absurd(R.StepsIn(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

law exact_steps_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +eqF: {Prune.prunedSteps(fuel, grammar, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  for got: {Exact.exactFrom(found, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def exact_steps_found(found, fuel, grammar, start, input, set, eqF, got):
  match found:
    case Some{+ps}:
      exact_pick_steps(Bool.and(Exact.witnessed(grammar, start, input, ps, Witness.witnesses(fuel, grammar, start, input, ps)), Exact.allTokensOk(ps, grammar, input)), ps, set, fuel, grammar, start, input, eqF, got)
    case None{}:
      Empty.absurd(R.StepsIn(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# Every step of every parse tree is in the exact set.
law exact_steps_in:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  R.StepsIn(grammar, start, input, set)

def exact_steps_in(fuel, grammar, start, input, set, got):
  exact_steps_found(Prune.prunedSteps(fuel, grammar, start, input), fuel, grammar, start, input, set, {==}, got)

# ======== AN ANSWER LEAVES A READING: prefer_avoid_safe ========
#
# Take any parse tree and repair it from the top down. A node or pick whose completion
# the oracle kept stays, and its children are repaired in turn. One whose completion
# was removed is replaced by the rival forest of the removal's certificate: SPEC's rival,
# over the same tokens, and made of kept steps only. Every step of the repaired tree is
# then kept, so it is unbeaten by the first half of prefer_avoid_exact.

# The steps the walk lists inside a tree, between its own step and the rest.
def inner(t: Spec.Tree, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +k: Nat) -> +List<Spec.Bsr>:
  match t:
    case Spec.Leaf{kind}:
      []
    case Spec.Node{+q, +ch}:
      Spec.walk(ch, False{}, q, [], 0n, k, k)
    case Spec.Pick{+a, +ch}:
      Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, k, k)
    case Spec.Skip{}:
      []
    case Spec.Loop{+rs}:
      Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, k, k)

law walk_cons:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  {Spec.walk(t <> ts, False{}, index, prefix, dot, i, k) == Spec.at(index, prefix, 1n+dot, i, k, endOf(t, k)) <> List.append(&2, Spec.Bsr, inner(t, index, prefix, dot, k), Spec.walk(ts, False{}, index, prefix, 1n+dot, i, endOf(t, k))) : +List<Spec.Bsr>}

def walk_cons(t, ts, index, prefix, dot, i, k):
  match t:
    case Spec.Leaf{+kind}:
      {==}
    case Spec.Node{+q, +ch}:
      {==}
    case Spec.Pick{+a, +ch}:
      {==}
    case Spec.Skip{}:
      {==}
    case Spec.Loop{+rs}:
      {==}

law leaves_cons:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {Spec.leaves(t <> ts) == List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)) : +List<Nat>}

def leaves_cons(t, ts):
  match t:
    case Spec.Leaf{+kind}:
      {==}
    case Spec.Node{+q, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Pick{+a, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Skip{}:
      {==}
    case Spec.Loop{+rs}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(rs), List.append(&2, Nat, Spec.leaves(rs), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(rs), []), Spec.leaves(rs), Lemma.append_nil_right(Spec.leaves(rs))))
