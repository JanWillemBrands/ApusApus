import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./PRUNE.bend as Prune
import ./WITNESS.bend as Witness
import ./EXACT.bend as Exact
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_EXACT.bend as X

# TREES FROM THE EXACT SET SPELL THE INPUT. A tree that fits the start symbol, uses only steps
# of the exact parser's set, and is as long as the input, spells the input. Its leaves are the
# only part that depends on the input, and every leaf's step is a step of a witness tree,
# which the exact parser has checked with `reads`: so the token is the input's token there.
# The tree then reads the input, and a tree that reads all of it spells it.

# ======== THE TOKEN OF A STEP ========

# A step after a terminal says which token is at its pivot.
def tokItem(item: Maybe<&2, Core.Sym>, +input: +List<Nat>, +k: Nat) -> Bool:
  match item:
    case Some{Core.Terminal{+t}}:
      Core.tokIs(Core.tokAt(input, k), t)
    case _:
      True{}

def stepTok(+grammar: +List<Core.Production>, +input: +List<Nat>, e: Core.Bsr) -> Bool:
  match e:
    case Core.Bsr{q, 0n, i, k, j}:
      True{}
    case Core.Bsr{+q, 1n+(+d), i, +k, j}:
      tokItem(Gll.nthSym(Core.rhsOf(grammar, q), d), input, k)

def allTok(xs: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(stepTok(grammar, input, x), allTok(rest, grammar, input))

law all_tok_app:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +hx: {allTok(xs, grammar, input) == True{} : Bool}
  for +hy: {allTok(ys, grammar, input) == True{} : Bool}
  {allTok(List.append(&2, Core.Bsr, xs, ys), grammar, input) == True{} : Bool}

def all_tok_app(xs, ys, grammar, input, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      Lemma.and_true_intro(stepTok(grammar, input, x), allTok(List.append(&2, Core.Bsr, rest, ys), grammar, input),
        Lemma.and_true_left(stepTok(grammar, input, x), allTok(rest, grammar, input), hx),
        all_tok_app(rest, ys, grammar, input, Lemma.and_true_right_side(stepTok(grammar, input, x), allTok(rest, grammar, input), hx), hy))

def tok_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  +here: {stepTok(grammar, input, y) == True{} : Bool},
  later: {Core.member(x, rest) == True{} : Bool} -> {stepTok(grammar, input, x) == True{} : Bool})
  -> {stepTok(grammar, input, x) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {stepTok(grammar, input, _) == True{} : Bool}
      here
    case Inr{m}:
      later(m)

law all_tok_member:
  for xs: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +all: {allTok(xs, grammar, input) == True{} : Bool}
  for +m: {Core.member(x, xs) == True{} : Bool}
  {stepTok(grammar, input, x) == True{} : Bool}

def all_tok_member(xs, grammar, input, x, all, m):
  match xs:
    case Nil{}:
      Empty.absurd({stepTok(grammar, input, x) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      tok_pick(grammar, input, x, y, rest, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        Lemma.and_true_left(stepTok(grammar, input, y), allTok(rest, grammar, input), all),
        later => all_tok_member(rest, grammar, input, x, Lemma.and_true_right_side(stepTok(grammar, input, y), allTok(rest, grammar, input), all), later))

# ======== A TREE THAT READS THE INPUT HAS THE INPUT'S TOKENS IN ITS STEPS ========

def Toks(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +f: +List<Core.Tree>, +d: Nat, +k: Nat) -> Type:
  {allTok(Core.own(q, f, d, ks, k), grammar, input) == True{} : Bool} & {allTok(Core.steps(f, k), grammar, input) == True{} : Bool}

law empty_tok:
  for dot: Nat
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ks: Nat
  for +k: Nat
  {allTok(Core.emptyAt(dot, q, ks, k), grammar, input) == True{} : Bool}

def empty_tok(dot, grammar, input, q, ks, k):
  match dot:
    case 0n:
      {==}
    case 1n+(+n):
      {==}

law item_tok:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +h: {tokItem(Some{y}, input, k) == True{} : Bool}
  {tokItem(Gll.nthSym(Core.rhsOf(grammar, q), d), input, k) == True{} : Bool}

def item_tok(grammar, input, q, d, k, y, rest, ie, h):
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), Some{y}, G.nth_drop(Core.rhsOf(grammar, q), d, y, rest, ie)) : {tokItem(_, input, k) == True{} : Bool}
  h

law tok_item_back:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +h: {tokItem(Gll.nthSym(Core.rhsOf(grammar, q), d), input, k) == True{} : Bool}
  {tokItem(Some{y}, input, k) == True{} : Bool}

def tok_item_back(grammar, input, q, d, k, y, rest, ie, h):
  %G.nth_drop(Core.rhsOf(grammar, q), d, y, rest, ie) : {tokItem(_, input, k) == True{} : Bool}
  h

law leaf_tok_own:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ks: Nat
  for +a: Nat
  for +ts: +List<Core.Tree>
  for +d: Nat
  for +k: Nat
  for +h: {allTok(Core.Bsr{q, 1n+d, ks, k, 1n+k} <> Core.own(q, ts, 1n+d, ks, 1n+k), grammar, input) == True{} : Bool}
  {allTok(Core.own(q, Core.Leaf{a} <> ts, d, ks, k), grammar, input) == True{} : Bool}

def leaf_tok_own(grammar, input, q, ks, a, ts, d, k, h):
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k)) : {allTok(Core.Bsr{q, 1n+d, ks, k, _} <> Core.own(q, ts, 1n+d, ks, _), grammar, input) == True{} : Bool}
  h

def leaf_toks(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +a: Nat, +ts: +List<Core.Tree>, +d: Nat, +k: Nat,
  +here: {stepTok(grammar, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}) == True{} : Bool},
  rest: Toks(grammar, input, q, ks, ts, 1n+d, 1n+k)) -> Toks(grammar, input, q, ks, Core.Leaf{a} <> ts, d, k):
  match rest:
    case (o, st):
      +own = leaf_tok_own(grammar, input, q, ks, a, ts, d, k, Lemma.and_true_intro(stepTok(grammar, input, Core.Bsr{q, 1n+d, ks, k, 1n+k}), allTok(Core.own(q, ts, 1n+d, ks, 1n+k), grammar, input), here, o))
      {(own, st) : Toks(grammar, input, q, ks, Core.Leaf{a} <> ts, d, k)}

def node_toks2(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +d: Nat, +k: Nat,
  +here: {stepTok(grammar, input, Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}) == True{} : Bool},
  +oc: {allTok(Core.own(q2, ch, 0n, k, k), grammar, input) == True{} : Bool},
  +sc: {allTok(Core.steps(ch, k), grammar, input) == True{} : Bool},
  rest: Toks(grammar, input, q, ks, ts, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})))) -> Toks(grammar, input, q, ks, Core.Node{q2, ch} <> ts, d, k):
  match rest:
    case (o, st):
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +own = Lemma.and_true_intro(stepTok(grammar, input, Core.Bsr{q, 1n+d, ks, k, far}), allTok(Core.own(q, ts, 1n+d, ks, far), grammar, input), here, o)
      +all = all_tok_app(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), grammar, input, oc, all_tok_app(Core.steps(ch, k), Core.steps(ts, far), grammar, input, sc, st))
      {(own, all) : Toks(grammar, input, q, ks, Core.Node{q2, ch} <> ts, d, k)}

def node_toks(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +d: Nat, +k: Nat,
  +here: {stepTok(grammar, input, Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}) == True{} : Bool},
  below: Toks(grammar, input, q2, k, ch, 0n, k),
  rest: Toks(grammar, input, q, ks, ts, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})))) -> Toks(grammar, input, q, ks, Core.Node{q2, ch} <> ts, d, k):
  match below:
    case (oc, sc):
      node_toks2(grammar, input, q, ks, q2, ch, ts, d, k, here, oc, sc, rest)

law twalk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  Toks(grammar, input, q, ks, f, d, k)

def twalk(f, items, grammar, input, q, ks, d, k, ie, r):
  match f items:
    case Nil{} Nil{}:
      +own = empty_tok(d, grammar, input, q, ks, k)
      {(own, {==}) : Toks(grammar, input, q, ks, [], d, k)}
    case Nil{} Con{+y, +yr}:
      Empty.absurd(Toks(grammar, input, q, ks, [], d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd(Toks(grammar, input, q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Toks(grammar, input, q, ks, Core.Leaf{a} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +ea = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more, r))
      +tk = G.token_here(input, k, a, t, ea, Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r)))
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      leaf_toks(grammar, input, q, ks, a, ts, d, k, item_tok(grammar, input, q, d, k, Core.Terminal{t}, rest, ie, tk),
        twalk(ts, rest, grammar, input, q, ks, 1n+d, 1n+k, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie), rt))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd(Toks(grammar, input, q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Toks(grammar, input, q, ks, Core.Node{q2, ch} <> ts, d, k), Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r))
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      node_toks(grammar, input, q, ks, q2, ch, ts, d, k, item_tok(grammar, input, q, d, k, Core.Nonterminal{x, need}, rest, ie, {==}),
        twalk(ch, Core.rhsOf(grammar, q2), grammar, input, q2, k, 0n, k, {==}, rc),
        twalk(ts, rest, grammar, input, q, ks, 1n+d, far, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie), rt))

def tree_toks(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ch: +List<Core.Tree>, t: Toks(grammar, input, q, 0n, ch, 0n, 0n))
  -> {allTok(Core.steps([Core.Node{q, ch}], 0n), grammar, input) == True{} : Bool}:
  match t:
    case (o, st):
      all_tok_app(Core.own(q, ch, 0n, 0n, 0n), List.append(&2, Core.Bsr, Core.steps(ch, 0n), []), grammar, input, o, all_tok_app(Core.steps(ch, 0n), [], grammar, input, st, {==}))

# A witness checked by the exact parser has the input's tokens in all its steps.
law tree_tok:
  for w: Core.Tree
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ok: {Exact.treeOk(grammar, start, input, w) == True{} : Bool}
  {allTok(Core.steps([w], 0n), grammar, input) == True{} : Bool}

def tree_tok(w, grammar, start, input, ok):
  match w:
    case Core.Leaf{+a}:
      Empty.absurd({allTok(Core.steps([Core.Leaf{a}], 0n), grammar, input) == True{} : Bool}, Lemma.false_is_not_true(ok))
    case Core.Node{+q, +ch}:
      +rr = Lemma.and_true_left(Core.reads([Core.Node{q, ch}], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([Core.Node{q, ch}])), List.length(&2, Nat, input)), ok)
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)) : Bool}
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), Lemma.and_true_left(own, Core.reads([], grammar, [], input, Nat.add(0n, Core.width(Core.Node{q, ch}))), rr))
      tree_toks(grammar, input, q, ch, twalk(ch, Core.rhsOf(grammar, q), grammar, input, q, 0n, 0n, 0n, {==}, rc))

def ws_pick(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +x: Core.Bsr, +t: Core.Tree, +rest: +List<Core.Tree>,
  +ok: {Exact.treeOk(grammar, start, input, t) == True{} : Bool},
  cases: Either<{Core.member(x, Core.steps([t], 0n)) == True{} : Bool}, {Witness.coveredBy(x, rest) == True{} : Bool}>,
  later: {Witness.coveredBy(x, rest) == True{} : Bool} -> {stepTok(grammar, input, x) == True{} : Bool}) -> {stepTok(grammar, input, x) == True{} : Bool}:
  match cases:
    case Inl{m}:
      all_tok_member(Core.steps([t], 0n), grammar, input, x, tree_tok(t, grammar, start, input, ok), m)
    case Inr{c}:
      later(c)

# A step covered by checked witnesses has the input's token.
law ws_tok:
  for ws: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +c: {Witness.coveredBy(x, ws) == True{} : Bool}
  {stepTok(grammar, input, x) == True{} : Bool}

def ws_tok(ws, grammar, start, input, x, okAll, c):
  match ws:
    case Nil{}:
      Empty.absurd({stepTok(grammar, input, x) == True{} : Bool}, Lemma.false_is_not_true(c))
    case Con{+t, +rest}:
      ws_pick(grammar, start, input, x, t, rest, Lemma.and_true_left(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), okAll),
        Lemma.or_true_cases(Core.member(x, Core.steps([t], 0n)), Witness.coveredBy(x, rest), c),
        later => ws_tok(rest, grammar, start, input, x, Lemma.and_true_right_side(Exact.treeOk(grammar, start, input, t), Exact.allTreesOk(rest, grammar, start, input), okAll), later))

# A step of the exact set has the input's token.
law ps_tok:
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +x: Core.Bsr
  for +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +cov: {Exact.allCovered(ps, ws) == True{} : Bool}
  for +m: {Core.member(x, ps) == True{} : Bool}
  {stepTok(grammar, input, x) == True{} : Bool}

def ps_tok(ps, ws, grammar, start, input, x, okAll, cov, m):
  ws_tok(ws, grammar, start, input, x, okAll, X.covered_of(ps, ws, x, cov, m))

# ======== A TREE THAT FITS AND USES ONLY EXACT STEPS READS THE INPUT ========

law fwalk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +cov: {Exact.allCovered(ps, ws) == True{} : Bool}
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +fit: {Core.fits(f, grammar, items) == True{} : Bool}
  for +io: {Core.allIn(Core.own(q, f, d, ks, k), ps) == True{} : Bool}
  for +sx: {Core.allIn(Core.steps(f, k), ps) == True{} : Bool}
  {Core.reads(f, grammar, items, input, k) == True{} : Bool}

def fwalk(f, items, grammar, start, input, ps, ws, okAll, cov, q, ks, d, k, ie, fit, io, sx):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yr}:
      Empty.absurd({Core.reads([], grammar, y <> yr, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> ts, grammar, [], input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> ts, grammar, Core.Nonterminal{x, need} <> rest, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +eab = Lemma.and_true_left(Nat.is_eq(a, t), Core.fits(ts, grammar, rest), fit)
      +ea = Lemma.nat_eq_sound(a, t, eab)
      +view = P.leaf_view(q, d, ks, k, a, ts, ps, io)
      +x = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      +mx = Lemma.and_true_left(Core.member(x, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ps), view)
      +tail = Lemma.and_true_right_side(Core.member(x, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ps), view)
      +tk = tok_item_back(grammar, input, q, d, k, Core.Terminal{t}, rest, ie, ps_tok(ps, ws, grammar, start, input, x, okAll, cov, mx))
      +tka = G.token_here(input, k, t, a, Equal.sym(Nat, a, t, ea), tk)
      +rt = fwalk(ts, rest, grammar, start, input, ps, ws, okAll, cov, q, ks, 1n+d, 1n+k, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie), Lemma.and_true_right_side(Nat.is_eq(a, t), Core.fits(ts, grammar, rest), fit), tail, sx)
      Lemma.and_true_intro(Nat.is_eq(a, t), Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)), eab,
        Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), tka, rt))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Node{q2, ch} <> ts, grammar, [], input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Core.reads(Core.Node{q2, ch} <> ts, grammar, Core.Terminal{t} <> rest, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +ownF = {Bool.and(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q2))) : Bool}
      +leftF = Lemma.and_true_left(ownF, Core.fits(ts, grammar, rest), fit)
      +hd = Lemma.and_true_left(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q2)), leftF)
      +fc = Lemma.and_true_right_side(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q2)), leftF)
      +ft = Lemma.and_true_right_side(ownF, Core.fits(ts, grammar, rest), fit)
      +step = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +tail = Lemma.and_true_right_side(Core.member(step, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, far), ps), io)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)) : +List<Core.Bsr>}
      +iso = P.in_app_left(Core.own(q2, ch, 0n, k, k), below, ps, sx)
      +isr = P.in_app_right(Core.own(q2, ch, 0n, k, k), below, ps, sx)
      +isc = P.in_app_left(Core.steps(ch, k), Core.steps(ts, far), ps, isr)
      +ist = P.in_app_right(Core.steps(ch, k), Core.steps(ts, far), ps, isr)
      +rc = fwalk(ch, Core.rhsOf(grammar, q2), grammar, start, input, ps, ws, okAll, cov, q2, k, 0n, k, {==}, fc, iso, isc)
      +rt = fwalk(ts, rest, grammar, start, input, ps, ws, okAll, cov, q, ks, 1n+d, far, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie), ft, tail, ist)
      Lemma.and_true_intro(Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)), Core.reads(ts, grammar, rest, input, far),
        Lemma.and_true_intro(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), hd, rc), rt)

law tree_reads:
  for tree: Core.Tree
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +okAll: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +cov: {Exact.allCovered(ps, ws) == True{} : Bool}
  for +fitting: {Core.fits([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}]) == True{} : Bool}
  for +inSet: {Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}
  {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}

def tree_reads(tree, grammar, start, input, ps, ws, okAll, cov, fitting, inSet):
  match tree:
    case Core.Leaf{+a}:
      Empty.absurd({Core.reads([Core.Leaf{a}], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Core.Node{+q, +ch}:
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +ownF = {Bool.and(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q))) : Bool}
      +leftF = Lemma.and_true_left(ownF, True{}, fitting)
      +hd = Lemma.and_true_left(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q)), leftF)
      +fc = Lemma.and_true_right_side(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q)), leftF)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, 0n), []) : +List<Core.Bsr>}
      +io = P.in_app_left(Core.own(q, ch, 0n, 0n, 0n), below, ps, inSet)
      +isc = P.in_app_left(Core.steps(ch, 0n), [], ps, P.in_app_right(Core.own(q, ch, 0n, 0n, 0n), below, ps, inSet))
      +rc = fwalk(ch, Core.rhsOf(grammar, q), grammar, start, input, ps, ws, okAll, cov, q, 0n, 0n, 0n, {==}, fc, io, isc)
      Lemma.and_true_intro(Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)), True{},
        Lemma.and_true_intro(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), hd, rc), {==})

# ======== A TREE THAT READS ALL OF THE INPUT SPELLS IT ========

# The tokens are the input's, from position k on.
def spells(w: +List<Nat>, +input: +List<Nat>, +k: Nat) -> Bool:
  match w:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Core.tokIs(Core.tokAt(input, k), c), spells(rest, input, 1n+k))

law shift_pos:
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +la: Nat
  for +hb: {spells(b, input, Nat.add(k, 1n+la)) == True{} : Bool}
  {spells(b, input, 1n+Nat.add(k, la)) == True{} : Bool}

def shift_pos(b, input, k, la, hb):
  %Lemma.add_succ_right(k, la) : {spells(b, input, _) == True{} : Bool}
  hb


law spells_app:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +ha: {spells(a, input, k) == True{} : Bool}
  for +hb: {spells(b, input, Nat.add(k, List.length(&2, Nat, a))) == True{} : Bool}
  {spells(List.append(&2, Nat, a, b), input, k) == True{} : Bool}

def spells_app(a, b, input, k, ha, hb):
  match a:
    case Nil{}:
      %Lemma.add_zero_right(k) : {spells(b, input, _) == True{} : Bool}
      hb
    case Con{+c, +rest}:
      +la = {List.length(&2, Nat, rest) : Nat}
      +hb2 = shift_pos(b, input, k, la, hb)
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), c), spells(List.append(&2, Nat, rest, b), input, 1n+k),
        Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), c), spells(rest, input, 1n+k), ha),
        spells_app(rest, b, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), c), spells(rest, input, 1n+k), ha), hb2))

law width_pos:
  for +ch: +List<Core.Tree>
  for +q2: Nat
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +h: {spells(w, input, Nat.add(k, Core.width(Core.Node{q2, ch}))) == True{} : Bool}
  {spells(w, input, Nat.add(k, List.length(&2, Nat, Core.leaves(ch)))) == True{} : Bool}

def width_pos(ch, q2, w, input, k, h):
  %Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, Core.leaves(ch), []), Core.leaves(ch), Lemma.append_nil_right(Core.leaves(ch))) : {spells(w, input, Nat.add(k, _)) == True{} : Bool}
  h


law reads_spells:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  {spells(Core.leaves(f), input, k) == True{} : Bool}

def reads_spells(f, items, grammar, input, k, r):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yr}:
      Empty.absurd({spells([], input, k) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({spells(Core.leaves(Core.Leaf{a} <> ts), input, k) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({spells(Core.leaves(Core.Leaf{a} <> ts), input, k) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +inner = Lemma.and_true_right_side(Nat.is_eq(a, t), more, r)
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), a), spells(Core.leaves(ts), input, 1n+k),
        Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), inner),
        reads_spells(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), inner)))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd({spells(Core.leaves(Core.Node{q2, ch} <> ts), input, k) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({spells(Core.leaves(Core.Node{q2, ch} <> ts), input, k) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r))
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      spells_app(Core.leaves(ch), Core.leaves(ts), input, k, reads_spells(ch, Core.rhsOf(grammar, q2), grammar, input, k, rc),
        width_pos(ch, q2, Core.leaves(ts), input, k, reads_spells(ts, rest, grammar, input, far, rt)))

law spells_shift:
  for w: +List<Nat>
  for +x: Nat
  for +xs: +List<Nat>
  for +k: Nat
  for +h: {spells(w, x <> xs, 1n+k) == True{} : Bool}
  {spells(w, xs, k) == True{} : Bool}

def spells_shift(w, x, xs, k, h):
  match w:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(xs, k), c), spells(rest, xs, 1n+k),
        Lemma.and_true_left(Core.tokIs(Core.tokAt(xs, k), c), spells(rest, x <> xs, 2n+k), h),
        spells_shift(rest, x, xs, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(xs, k), c), spells(rest, x <> xs, 2n+k), h)))

law spells_eq:
  for w: +List<Nat>
  for input: +List<Nat>
  for +h: {spells(w, input, 0n) == True{} : Bool}
  for +l: {List.length(&2, Nat, w) == List.length(&2, Nat, input) : Nat}
  {w == input : +List<Nat>}

def spells_eq(w, input, h, l):
  match w input:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+x, +xs}:
      Empty.absurd({[] == x <> xs : +List<Nat>}, Lemma.true_is_not_false(Equal.cong(Nat, Bool, v => Nat.is_eq(v, 0n), 0n, 1n+List.length(&2, Nat, xs), l)))
    case Con{+c, +rest} Nil{}:
      Empty.absurd({c <> rest == [] : +List<Nat>}, Lemma.false_is_not_true(Equal.cong(Nat, Bool, v => Nat.is_eq(v, 0n), 1n+List.length(&2, Nat, rest), 0n, l)))
    case Con{+c, +rest} Con{+x, +xs}:
      +ec = Lemma.nat_eq_sound(x, c, Lemma.and_true_left(Nat.is_eq(x, c), spells(rest, x <> xs, 1n), h))
      +sh = spells_shift(rest, x, xs, 0n, Lemma.and_true_right_side(Nat.is_eq(x, c), spells(rest, x <> xs, 1n), h))
      +lr = Equal.cong(Nat, Nat, v => Lemma.predOf(v), 1n+List.length(&2, Nat, rest), 1n+List.length(&2, Nat, xs), l)
      +er = spells_eq(rest, xs, sh, lr)
      %ec : {_ <> rest == x <> xs : +List<Nat>}
      %Equal.sym(+List<Nat>, rest, xs, er) : {x <> _ == x <> xs : +List<Nat>}
      {==}

# ======== THE THEOREM ========

law in_ps:
  for +ps: +List<Core.Bsr>
  for +set: +List<Core.Bsr>
  for +xs: +List<Core.Bsr>
  for +es: {ps == set : +List<Core.Bsr>}
  for +h: {Core.allIn(xs, set) == True{} : Bool}
  {Core.allIn(xs, ps) == True{} : Bool}

def in_ps(ps, set, xs, es, h):
  %Equal.sym(+List<Core.Bsr>, ps, set, es) : {Core.allIn(xs, _) == True{} : Bool}
  h

def spell_pick(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +set: +List<Core.Bsr>,
  +eb: {b == Bool.and(Exact.allTreesOk(Witness.witnesses(fuel, grammar, start, input, ps), grammar, start, input), Exact.allCovered(ps, Witness.witnesses(fuel, grammar, start, input, ps))) : Bool},
  +e: {Exact.exactPick(b, ps) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +fitting: {Core.fits([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}]) == True{} : Bool},
  +inSet: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool},
  +long: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat})
  -> {Core.leaves([tree]) == input : +List<Nat>}:
  match b:
    case True{}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      +both = Equal.sym(Bool, True{}, Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), eb)
      +okAll = Lemma.and_true_left(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), both)
      +cov = Lemma.and_true_right_side(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws), both)
      +es = Equal.cong(Maybe<&2, +List<Core.Bsr>>, +List<Core.Bsr>, v => G.setOr(v, []), Some{ps}, Some{set}, e)
      +rr = tree_reads(tree, grammar, start, input, ps, ws, okAll, cov, fitting, in_ps(ps, set, Core.steps([tree], 0n), es, inSet))
      spells_eq(Core.leaves([tree]), input, reads_spells([tree], [Core.Nonterminal{start, Core.Anything{}}], grammar, input, 0n, rr), long)
    case False{}:
      Empty.absurd({Core.leaves([tree]) == input : +List<Nat>}, G.none_not_some(set, e))

def spell_parts(m: Maybe<&2, +List<Core.Bsr>>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +set: +List<Core.Bsr>,
  +e: {Exact.exactFrom(m, fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>},
  +tree: Core.Tree,
  +fitting: {Core.fits([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}]) == True{} : Bool},
  +inSet: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool},
  +long: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat})
  -> {Core.leaves([tree]) == input : +List<Nat>}:
  match m:
    case Some{+ps}:
      +ws = Witness.witnesses(fuel, grammar, start, input, ps)
      spell_pick(Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), fuel, grammar, start, input, ps, set, {==}, e, tree, fitting, inSet, long)
    case None{}:
      Empty.absurd({Core.leaves([tree]) == input : +List<Nat>}, G.none_not_some(set, e))

# TREES FROM THE EXACT SET SPELL THE INPUT: a tree that fits the start symbol, uses only steps
# of the exact parser's set, and is as long as the input, spells the input. An oracle that
# picks a tree from the set cannot produce something that is not a parse tree.
law exact_trees_spell:
  for fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +got: {Exact.exactSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Core.Bsr>>}
  for +tree: Core.Tree
  for +fitting: {Core.fits([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}]) == True{} : Bool}
  for +inSet: {Core.allIn(Core.steps([tree], 0n), set) == True{} : Bool}
  for +long: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  {Core.leaves([tree]) == input : +List<Nat>}

def exact_trees_spell(fuel, grammar, start, input, set, got, tree, fitting, inSet, long):
  +f = fuel
  spell_parts(Prune.prunedSteps(f, grammar, start, input), f, grammar, start, input, set, got, tree, fitting, inSet, long)
