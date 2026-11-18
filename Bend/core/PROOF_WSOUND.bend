import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./WITNESS.bend as W
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as PP
import ./PROOF_WITNESS.bend as WC
import ./PROOF_COUNT.bend as C
import ./PROOF_NEEDS.bend as N
import ./EXACT.bend as Exact

# THE WITNESS FACTS ARE SOUND (WITNESS.bend): every fact's forest reads the first `dot` items
# of its production from its start to its end, and a flagged forest contains the target
# among the node's steps. So whatever the root search hands out is a parse tree of the input
# that contains the target.

# ======== ONE TREE MORE AT THE END ========

def takeN(n: Nat, items: +List<Core.Sym>) -> +List<Core.Sym>:
  match n items:
    case 0n _:
      []
    case 1n+m Nil{}:
      []
    case 1n+m Con{+x, rest}:
      x <> takeN(m, rest)

law take_snoc:
  for d: Nat
  for items: +List<Core.Sym>
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, items) == y <> rest : +List<Core.Sym>}
  {takeN(1n+d, items) == List.append(&2, Core.Sym, takeN(d, items), [y]) : +List<Core.Sym>}

def take_snoc(d, items, y, rest, ie):
  match d items:
    case 0n +its:
      %Equal.sym(+List<Core.Sym>, its, y <> rest, ie) : {takeN(1n, _) == List.append(&2, Core.Sym, takeN(0n, _), [y]) : +List<Core.Sym>}
      {==}
    case 1n+(+m) Nil{}:
      Empty.absurd({[] == [y] : +List<Core.Sym>}, Lemma.true_is_not_false(Equal.cong(+List<Core.Sym>, Bool, v => List.is_empty(&2, Core.Sym, v), [], y <> rest, ie)))
    case 1n+(+m) Con{+x, +r}:
      Equal.cong(+List<Core.Sym>, +List<Core.Sym>, v => x <> v, takeN(1n+m, r), List.append(&2, Core.Sym, takeN(m, r), [y]), take_snoc(m, r, y, rest, ie))

law take_len:
  for d: Nat
  for items: +List<Core.Sym>
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, items) == y <> rest : +List<Core.Sym>}
  {List.length(&2, Core.Sym, takeN(d, items)) == d : Nat}

def take_len(d, items, y, rest, ie):
  match d items:
    case 0n +its:
      {==}
    case 1n+(+m) Nil{}:
      Empty.absurd({0n == 1n+m : Nat}, Lemma.true_is_not_false(Equal.cong(+List<Core.Sym>, Bool, v => List.is_empty(&2, Core.Sym, v), [], y <> rest, ie)))
    case 1n+(+m) Con{+x, +r}:
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, Core.Sym, takeN(m, r)), m, take_len(m, r, y, rest, ie))

law take_all:
  for items: +List<Core.Sym>
  {takeN(List.length(&2, Core.Sym, items), items) == items : +List<Core.Sym>}

def take_all(items):
  match items:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(+List<Core.Sym>, +List<Core.Sym>, v => x <> v, takeN(List.length(&2, Core.Sym, rest), rest), rest, take_all(rest))

law end_snoc:
  for fo: +List<Core.Tree>
  for +t: Core.Tree
  for +k: Nat
  {G.endOf(List.append(&2, Core.Tree, fo, [t]), k) == G.endOf([t], G.endOf(fo, k)) : Nat}

def end_snoc(fo, t, k):
  match fo:
    case Nil{}:
      {==}
    case Con{Core.Leaf{+a}, +ts}:
      end_snoc(ts, t, 1n+k)
    case Con{Core.Node{+q, +ch}, +ts}:
      end_snoc(ts, t, Nat.add(k, Core.width(Core.Node{q, ch})))

law reads_snoc:
  for fo: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +t: Core.Tree
  for +y: Core.Sym
  for +h1: {Core.reads(fo, grammar, items, input, k) == True{} : Bool}
  for +h2: {Core.reads([t], grammar, [y], input, G.endOf(fo, k)) == True{} : Bool}
  {Core.reads(List.append(&2, Core.Tree, fo, [t]), grammar, List.append(&2, Core.Sym, items, [y]), input, k) == True{} : Bool}

def reads_snoc(fo, items, grammar, input, k, t, y, h1, h2):
  match fo items:
    case Nil{} Nil{}:
      h2
    case Nil{} Con{+z, +zr}:
      Empty.absurd({Core.reads([t], grammar, z <> List.append(&2, Core.Sym, zr, [y]), input, k) == True{} : Bool}, Lemma.false_is_not_true(h1))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> List.append(&2, Core.Tree, ts, [t]), grammar, [y], input, k) == True{} : Bool}, Lemma.false_is_not_true(h1))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> List.append(&2, Core.Tree, ts, [t]), grammar, Core.Nonterminal{x, need} <> List.append(&2, Core.Sym, rest, [y]), input, k) == True{} : Bool}, Lemma.false_is_not_true(h1))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+tt}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +r2 = Lemma.and_true_right_side(Nat.is_eq(a, tt), more, h1)
      +more2 = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(List.append(&2, Core.Tree, ts, [t]), grammar, List.append(&2, Core.Sym, rest, [y]), input, 1n+k)) : Bool}
      Lemma.and_true_intro(Nat.is_eq(a, tt), more2, Lemma.and_true_left(Nat.is_eq(a, tt), more, h1),
        Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), a), Core.reads(List.append(&2, Core.Tree, ts, [t]), grammar, List.append(&2, Core.Sym, rest, [y]), input, 1n+k), Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), r2),
          reads_snoc(ts, rest, grammar, input, 1n+k, t, y, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), r2), h2)))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Node{q2, ch} <> List.append(&2, Core.Tree, ts, [t]), grammar, [y], input, k) == True{} : Bool}, Lemma.false_is_not_true(h1))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+tt}, +rest}:
      Empty.absurd({Core.reads(Core.Node{q2, ch} <> List.append(&2, Core.Tree, ts, [t]), grammar, Core.Terminal{tt} <> List.append(&2, Core.Sym, rest, [y]), input, k) == True{} : Bool}, Lemma.false_is_not_true(h1))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +own = {Bool.and(Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))), Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      Lemma.and_true_intro(own, Core.reads(List.append(&2, Core.Tree, ts, [t]), grammar, List.append(&2, Core.Sym, rest, [y]), input, far), Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), h1),
        reads_snoc(ts, rest, grammar, input, far, t, y, Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), h1), h2))

# The steps of a forest stay when a tree is added at its end; the new tree's steps join.
law mem_steps_l:
  for fo: +List<Core.Tree>
  for +t: Core.Tree
  for +k: Nat
  for +x: Core.Bsr
  for +h: {Core.member(x, Core.steps(fo, k)) == True{} : Bool}
  {Core.member(x, Core.steps(List.append(&2, Core.Tree, fo, [t]), k)) == True{} : Bool}

def steps_node_l2(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +t: Core.Tree, +k: Nat, +x: Core.Bsr,
  c: Either<{Core.member(x, Core.steps(ch, k)) == True{} : Bool}, {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool}>,
  later: {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool} -> {Core.member(x, Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool})
  -> {Core.member(x, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch}))))) == True{} : Bool}:
  match c:
    case Inl{m}:
      WC.mem_left(Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch}))), x, m)
    case Inr{m}:
      WC.mem_right(Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch}))), x, later(m))

def steps_node_l(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +t: Core.Tree, +k: Nat, +x: Core.Bsr,
  c: Either<{Core.member(x, Core.own(q2, ch, 0n, k, k)) == True{} : Bool}, {Core.member(x, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch}))))) == True{} : Bool}>,
  later: {Core.member(x, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool} -> {Core.member(x, Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool})
  -> {Core.member(x, Core.steps(Core.Node{q2, ch} <> List.append(&2, Core.Tree, ts, [t]), k)) == True{} : Bool}:
  match c:
    case Inl{m}:
      WC.mem_left(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch})))), x, m)
    case Inr{m}:
      WC.mem_right(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), Nat.add(k, Core.width(Core.Node{q2, ch})))), x,
        steps_node_l2(q2, ch, ts, t, k, x, WC.mem_split(Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch}))), x, m), later))

def mem_steps_l(fo, t, k, x, h):
  match fo:
    case Nil{}:
      Empty.absurd({Core.member(x, Core.steps([t], k)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Leaf{+a}, +ts}:
      mem_steps_l(ts, t, 1n+k, x, h)
    case Con{Core.Node{+q2, +ch}, +ts}:
      +far = Nat.add(k, Core.width(Core.Node{q2, ch}))
      steps_node_l(q2, ch, ts, t, k, x, WC.mem_split(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), x, h),
        m => mem_steps_l(ts, t, far, x, m))

law mem_steps_r:
  for fo: +List<Core.Tree>
  for +t: Core.Tree
  for +k: Nat
  for +x: Core.Bsr
  for +h: {Core.member(x, Core.steps([t], G.endOf(fo, k))) == True{} : Bool}
  {Core.member(x, Core.steps(List.append(&2, Core.Tree, fo, [t]), k)) == True{} : Bool}

def mem_steps_r(fo, t, k, x, h):
  match fo:
    case Nil{}:
      h
    case Con{Core.Leaf{+a}, +ts}:
      mem_steps_r(ts, t, 1n+k, x, h)
    case Con{Core.Node{+q2, +ch}, +ts}:
      +far = Nat.add(k, Core.width(Core.Node{q2, ch}))
      WC.mem_right(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), far)), x,
        WC.mem_right(Core.steps(ch, k), Core.steps(List.append(&2, Core.Tree, ts, [t]), far), x, mem_steps_r(ts, t, far, x, h)))

# ======== A NODE'S OWN STEPS ========

# Where a forest read from k ends, counted with `own`'s widths.
def endW(fo: +List<Core.Tree>, +k: Nat) -> Nat:
  match fo:
    case Nil{}:
      k
    case Con{+t, ts}:
      endW(ts, Nat.add(k, Core.width(t)))

law end_w:
  for fo: +List<Core.Tree>
  for +k: Nat
  {endW(fo, k) == G.endOf(fo, k) : Nat}

def end_w(fo, k):
  match fo:
    case Nil{}:
      {==}
    case Con{Core.Leaf{+a}, +ts}:
      Equal.trans(Nat, endW(ts, Nat.add(k, 1n)), endW(ts, 1n+k), G.endOf(ts, 1n+k),
        Equal.cong(Nat, Nat, v => endW(ts, v), Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k)), end_w(ts, 1n+k))
    case Con{Core.Node{+q, +ch}, +ts}:
      end_w(ts, Nat.add(k, Core.width(Core.Node{q, ch})))

def end_one(t: Core.Tree, +k: Nat) -> {G.endOf([t], k) == Nat.add(k, Core.width(t)) : Nat}:
  match t:
    case Core.Leaf{+a}:
      Equal.sym(Nat, Nat.add(k, 1n), 1n+k, Lemma.add_one_right(k))
    case Core.Node{+q, +ch}:
      {==}

def own_pre_pick(+q: Nat, +b: Core.Bsr, +rest: +List<Core.Bsr>, +rest2: +List<Core.Bsr>, +x: Core.Bsr,
  cases: Either<{Core.bsrEq(x, b) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, rest2) == True{} : Bool}) -> {Core.member(x, b <> rest2) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Core.bsrEq(x, b), Core.member(x, rest2), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, b), Core.member(x, rest2), later(m))

# A node's own steps stay when a child is added at the end.
law own_pre:
  for +q: Nat
  for fo: +List<Core.Tree>
  for +t: Core.Tree
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  for +x: Core.Bsr
  for +h: {Core.member(x, WC.ownNE(q, fo, d, ks, k)) == True{} : Bool}
  {Core.member(x, WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), d, ks, k)) == True{} : Bool}

def own_pre(q, fo, t, d, ks, k, x, h):
  match fo:
    case Nil{}:
      Empty.absurd({Core.member(x, WC.ownNE(q, [t], d, ks, k)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+s, +rest}:
      +far = Nat.add(k, Core.width(s))
      +b = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      own_pre_pick(q, b, WC.ownNE(q, rest, 1n+d, ks, far), WC.ownNE(q, List.append(&2, Core.Tree, rest, [t]), 1n+d, ks, far), x,
        Lemma.or_true_cases(Core.bsrEq(x, b), Core.member(x, WC.ownNE(q, rest, 1n+d, ks, far)), h), m => own_pre(q, rest, t, 1n+d, ks, far, x, m))

def last_zero(+q: Nat, +d: Nat, +ks: Nat, +k: Nat, +j: Nat, +more: +List<Core.Bsr>)
  -> {Core.member(Core.Bsr{q, 1n+Nat.add(d, 0n), ks, k, j}, Core.Bsr{q, 1n+d, ks, k, j} <> more) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 0n), d, Lemma.add_zero_right(d)) : {Core.member(Core.Bsr{q, 1n+_, ks, k, j}, Core.Bsr{q, 1n+d, ks, k, j} <> more) == True{} : Bool}
  Lemma.or_true_left_intro(Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, Core.Bsr{q, 1n+d, ks, k, j}), Core.member(Core.Bsr{q, 1n+d, ks, k, j}, more), C.bsr_eq_refl(Core.Bsr{q, 1n+d, ks, k, j}))

def last_succ(+q: Nat, +d: Nat, +n: Nat, +ks: Nat, +k: Nat, +j: Nat, +xs: +List<Core.Bsr>,
  +h: {Core.member(Core.Bsr{q, 1n+Nat.add(1n+d, n), ks, k, j}, xs) == True{} : Bool}) -> {Core.member(Core.Bsr{q, 1n+Nat.add(d, 1n+n), ks, k, j}, xs) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 1n+n), 1n+Nat.add(d, n), Lemma.add_succ_right(d, n)) : {Core.member(Core.Bsr{q, 1n+_, ks, k, j}, xs) == True{} : Bool}
  h

# The step of the added child is one of the node's own steps.
law own_last:
  for +q: Nat
  for fo: +List<Core.Tree>
  for +t: Core.Tree
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  {Core.member(Core.Bsr{q, 1n+Nat.add(d, List.length(&2, Core.Tree, fo)), ks, endW(fo, k), Nat.add(endW(fo, k), Core.width(t))}, WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), d, ks, k)) == True{} : Bool}

def own_last(q, fo, t, d, ks, k):
  match fo:
    case Nil{}:
      last_zero(q, d, ks, k, Nat.add(k, Core.width(t)), [])
    case Con{+s, +rest}:
      +far = Nat.add(k, Core.width(s))
      +b = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +x = {Core.Bsr{q, 1n+Nat.add(d, 1n+List.length(&2, Core.Tree, rest)), ks, endW(rest, far), Nat.add(endW(rest, far), Core.width(t))} : Core.Bsr}
      Lemma.or_true_right_intro(Core.bsrEq(x, b), Core.member(x, WC.ownNE(q, List.append(&2, Core.Tree, rest, [t]), 1n+d, ks, far)),
        last_succ(q, d, List.length(&2, Core.Tree, rest), ks, endW(rest, far), Nat.add(endW(rest, far), Core.width(t)), WC.ownNE(q, List.append(&2, Core.Tree, rest, [t]), 1n+d, ks, far), own_last(q, rest, t, 1n+d, ks, far)))

# ======== WHAT A SOUND FACT IS ========

def emptyIf(b: Bool, +x: Core.Bsr) -> +List<Core.Bsr>:
  match b:
    case True{}:
      [x]
    case False{}:
      []

# A prefix forest's own steps in its node: the empty step only for an empty right side.
def ownS(+grammar: +List<Core.Production>, +q: Nat, fo: +List<Core.Tree>, +ks: Nat) -> +List<Core.Bsr>:
  match fo:
    case Nil{}:
      emptyIf(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.Bsr{q, 0n, ks, ks, ks})
    case Con{+t, rest}:
      WC.ownNE(q, t <> rest, 0n, ks, ks)

def stepsP(+grammar: +List<Core.Production>, +q: Nat, +fo: +List<Core.Tree>, +ks: Nat) -> +List<Core.Bsr>:
  List.append(&2, Core.Bsr, ownS(grammar, q, fo, ks), Core.steps(fo, ks))

def flagOk(fl: Bool, +target: Core.Bsr, +xs: +List<Core.Bsr>) -> Bool:
  Bool.or(Bool.not(fl), Core.member(target, xs))

# A prefix forest of production q from ks to e, after d items, with a flag that holds.
def prefOk(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +fl: Bool, +fo: +List<Core.Tree>) -> Bool:
  Bool.and(Core.reads(fo, grammar, takeN(d, Core.rhsOf(grammar, q)), input, ks), Bool.and(Nat.is_eq(G.endOf(fo, ks), e), flagOk(fl, target, stepsP(grammar, q, fo, ks))))

def optsOk(os: +List<W.Opt>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +e: Nat) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.and(prefOk(grammar, input, target, q, ks, d, e, fl, fo), optsOk(rest, grammar, input, target, q, ks, d, e))

# One tree for item y from k to j, with a flag that holds.
def itemOk(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +y: Core.Sym, +k: Nat, +j: Nat, +fl: Bool, fo: +List<Core.Tree>) -> Bool:
  match fo:
    case Con{+t, Nil{}}:
      Bool.and(Core.reads([t], grammar, [y], input, k), Bool.and(Nat.is_eq(G.endOf([t], k), j), flagOk(fl, target, Core.steps([t], k))))
    case _:
      False{}

def itemsOk(os: +List<W.Opt>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +y: Core.Sym, +k: Nat, +j: Nat) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.and(itemOk(grammar, input, target, y, k, j, fl, fo), itemsOk(rest, grammar, input, target, y, k, j))

def factsOk(fs: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{W.Fact{+q, +ks, +d, +e, +fl, +fo}, rest}:
      Bool.and(prefOk(grammar, input, target, q, ks, d, e, fl, fo), factsOk(rest, grammar, input, target))

# ---- Flags ----

def flag_mk(fl: Bool, +target: Core.Bsr, +xs: +List<Core.Bsr>, later: {fl == True{} : Bool} -> {Core.member(target, xs) == True{} : Bool}) -> {flagOk(fl, target, xs) == True{} : Bool}:
  match fl:
    case True{}:
      later({==})
    case False{}:
      {==}

def flag_or(f1: Bool, f2: Bool, +target: Core.Bsr, +a: +List<Core.Bsr>, +b: +List<Core.Bsr>, +xs: +List<Core.Bsr>,
  +h1: {flagOk(f1, target, a) == True{} : Bool}, +h2: {flagOk(f2, target, b) == True{} : Bool},
  sa: {Core.member(target, a) == True{} : Bool} -> {Core.member(target, xs) == True{} : Bool}, sb: {Core.member(target, b) == True{} : Bool} -> {Core.member(target, xs) == True{} : Bool}) -> {flagOk(Bool.or(f1, f2), target, xs) == True{} : Bool}:
  match f1 f2:
    case True{} +g:
      sa(h1)
    case False{} True{}:
      sb(h2)
    case False{} False{}:
      {==}

def flag_mark(f: Bool, here: Bool, +target: Core.Bsr, +xs: +List<Core.Bsr>,
  +h: {flagOk(f, target, xs) == True{} : Bool}, hh: {here == True{} : Bool} -> {Core.member(target, xs) == True{} : Bool}) -> {flagOk(Bool.or(f, here), target, xs) == True{} : Bool}:
  match f here:
    case True{} +g:
      h
    case False{} True{}:
      hh({==})
    case False{} False{}:
      {==}

# ---- Prefix options ----

def empty_flag(e: Bool, +b0: Core.Bsr, +target: Core.Bsr)
  -> {flagOk(Bool.and(e, Core.bsrEq(b0, target)), target, List.append(&2, Core.Bsr, emptyIf(e, b0), [])) == True{} : Bool}:
  match e:
    case True{}:
      flag_mk(Core.bsrEq(b0, target), target, [b0], x => Lemma.or_true_left_intro(Core.bsrEq(target, b0), False{}, WC.bsr_flip(b0, target, x)))
    case False{}:
      {==}

def empty_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +k: Nat, +eb: {Nat.is_eq(ks, k) == b : Bool})
  -> {optsOk(W.emptyPrefix(b, grammar, target, q, ks), grammar, input, target, q, ks, 0n, k) == True{} : Bool}:
  match b:
    case True{}:
      +e = List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q))
      +b0 = {Core.Bsr{q, 0n, ks, ks, ks} : Core.Bsr}
      Lemma.and_true_intro(prefOk(grammar, input, target, q, ks, 0n, k, Bool.and(e, Core.bsrEq(b0, target)), []), True{},
        Lemma.and_true_intro(True{}, Bool.and(Nat.is_eq(ks, k), flagOk(Bool.and(e, Core.bsrEq(b0, target)), target, stepsP(grammar, q, [], ks))), {==},
          Lemma.and_true_intro(Nat.is_eq(ks, k), flagOk(Bool.and(e, Core.bsrEq(b0, target)), target, stepsP(grammar, q, [], ks)), eb, empty_flag(e, b0, target))), {==})
    case False{}:
      {==}

def key_move(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fl: Bool, +fo: +List<Core.Tree>,
  +h: {Bool.and(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)))) == True{} : Bool},
  +hp: {prefOk(grammar, input, target, q2, ks2, d2, e2, fl, fo) == True{} : Bool}) -> {prefOk(grammar, input, target, q, ks, d, e, fl, fo) == True{} : Bool}:
  +r1 = Lemma.and_true_right_side(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2))), h)
  +r2 = Lemma.and_true_right_side(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)), r1)
  +eq = Lemma.nat_eq_sound(q, q2, Lemma.and_true_left(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2))), h))
  +eks = Lemma.nat_eq_sound(ks, ks2, Lemma.and_true_left(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)), r1))
  +ed = Lemma.nat_eq_sound(d, d2, Lemma.and_true_left(Nat.is_eq(d, d2), Nat.is_eq(e, e2), r2))
  +ee = Lemma.nat_eq_sound(e, e2, Lemma.and_true_right_side(Nat.is_eq(d, d2), Nat.is_eq(e, e2), r2))
  %Equal.sym(Nat, q, q2, eq) : {prefOk(grammar, input, target, _, ks, d, e, fl, fo) == True{} : Bool}
  %Equal.sym(Nat, ks, ks2, eks) : {prefOk(grammar, input, target, q2, _, d, e, fl, fo) == True{} : Bool}
  %Equal.sym(Nat, d, d2, ed) : {prefOk(grammar, input, target, q2, ks2, _, e, fl, fo) == True{} : Bool}
  %Equal.sym(Nat, e, e2, ee) : {prefOk(grammar, input, target, q2, ks2, d2, _, fl, fo) == True{} : Bool}
  hp

def found_ok_pick(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +q2: Nat, +ks2: Nat, +d2: Nat, +e2: Nat, +fl: Bool, +fo: +List<Core.Tree>, +more: +List<W.Opt>,
  +eb: {Bool.and(Nat.is_eq(q, q2), Bool.and(Nat.is_eq(ks, ks2), Bool.and(Nat.is_eq(d, d2), Nat.is_eq(e, e2)))) == b : Bool},
  +hp: {prefOk(grammar, input, target, q2, ks2, d2, e2, fl, fo) == True{} : Bool}, +hr: {optsOk(more, grammar, input, target, q, ks, d, e) == True{} : Bool})
  -> {optsOk(W.optIf(b, W.Opt{fl, fo}, more), grammar, input, target, q, ks, d, e) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(prefOk(grammar, input, target, q, ks, d, e, fl, fo), optsOk(more, grammar, input, target, q, ks, d, e), key_move(grammar, input, target, q, ks, d, e, q2, ks2, d2, e2, fl, fo, eb, hp), hr)
    case False{}:
      hr

law found_ok:
  for F: +List<W.Fact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  {optsOk(W.foundAt(q, ks, d, e, F), grammar, input, target, q, ks, d, e) == True{} : Bool}

def found_ok(F, grammar, input, target, q, ks, d, e, hF):
  match F:
    case Nil{}:
      {==}
    case Con{W.Fact{+q2, +ks2, +d2, +e2, +fl, +fo}, +rest}:
      +hp = Lemma.and_true_left(prefOk(grammar, input, target, q2, ks2, d2, e2, fl, fo), factsOk(rest, grammar, input, target), hF)
      +hr = Lemma.and_true_right_side(prefOk(grammar, input, target, q2, ks2, d2, e2, fl, fo), factsOk(rest, grammar, input, target), hF)
      found_ok_pick(W.sameKey(q, ks, d, e, W.Fact{q2, ks2, d2, e2, fl, fo}), grammar, input, target, q, ks, d, e, q2, ks2, d2, e2, fl, fo, W.foundAt(q, ks, d, e, rest), {==}, hp,
        found_ok(rest, grammar, input, target, q, ks, d, e, hr))

# Every prefix option of a segment is sound.
def opts_at_ok(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, d: Nat, +k: Nat, +hF: {factsOk(F, grammar, input, target) == True{} : Bool})
  -> {optsOk(W.optsAt(grammar, target, q, ks, d, k, F), grammar, input, target, q, ks, d, k) == True{} : Bool}:
  match d:
    case 0n:
      empty_ok(Nat.is_eq(ks, k), grammar, input, target, q, ks, k, {==})
    case 1n+(+m):
      found_ok(F, grammar, input, target, q, ks, 1n+m, k, hF)

# ---- Item options ----

law need_ok:
  for need: Core.Need
  for +k: Nat
  for w: Nat
  for +h: {Gll.needHolds(need, k, Nat.add(k, w)) == True{} : Bool}
  {Core.needOk(need, w) == True{} : Bool}

def need_ok(need, k, w, h):
  match need w:
    case Core.Anything{} +w0:
      {==}
    case Core.Something{} 0n:
      +e = Equal.trans(Bool, Nat.is_eq(k, Nat.add(k, 0n)), Nat.is_eq(k, k), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(k, v), Nat.add(k, 0n), k, Lemma.add_zero_right(k)), Lemma.nat_eq_refl(k))
      Equal.trans(Bool, False{}, Bool.not(Nat.is_eq(k, Nat.add(k, 0n))), True{}, Equal.cong(Bool, Bool, v => Bool.not(v), True{}, Nat.is_eq(k, Nat.add(k, 0n)), Equal.sym(Bool, Nat.is_eq(k, Nat.add(k, 0n)), True{}, e)), h)
    case Core.Something{} 1n+(+m):
      {==}
    case Core.Nothing{} 0n:
      {==}
    case Core.Nothing{} 1n+(+m):
      +ne = Equal.trans(Bool, Nat.is_eq(k, Nat.add(k, 1n+m)), Nat.is_eq(Nat.add(k, 1n+m), k), False{}, Lemma.nat_eq_symm(k, Nat.add(k, 1n+m)), Lemma.add_succ_ne(k, m))
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Nat.is_eq(k, Nat.add(k, 1n+m)), True{}, Equal.sym(Bool, Nat.is_eq(k, Nat.add(k, 1n+m)), False{}, ne), h)))

def leaf_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +t: Nat, +k: Nat, +j: Nat, +eb: {Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)) == b : Bool})
  -> {itemsOk(W.leafIf(b, t), grammar, input, target, Core.Terminal{t}, k, j) == True{} : Bool}:
  match b:
    case True{}:
      +tok = Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k), eb)
      +ej = Equal.trans(Bool, Nat.is_eq(1n+k, j), Nat.is_eq(j, 1n+k), True{}, Lemma.nat_eq_symm(1n+k, j), Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k), eb))
      +rd = Lemma.and_true_intro(Nat.is_eq(t, t), Bool.and(Core.tokIs(Core.tokAt(input, k), t), True{}), Lemma.nat_eq_refl(t), Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), t), True{}, tok, {==}))
      +io = Lemma.and_true_intro(Core.reads([Core.Leaf{t}], grammar, [Core.Terminal{t}], input, k), Bool.and(Nat.is_eq(1n+k, j), True{}), rd, Lemma.and_true_intro(Nat.is_eq(1n+k, j), True{}, ej, {==}))
      Lemma.and_true_intro(itemOk(grammar, input, target, Core.Terminal{t}, k, j, False{}, [Core.Leaf{t}]), True{}, io, {==})
    case False{}:
      {==}

def emptyif_mem(e: Bool, +b0: Core.Bsr, +x: Core.Bsr, +m: {Core.member(x, emptyIf(e, b0)) == True{} : Bool}) -> {Core.member(x, [b0]) == True{} : Bool}:
  match e:
    case True{}:
      m
    case False{}:
      Empty.absurd({Core.member(x, [b0]) == True{} : Bool}, Lemma.false_is_not_true(m))

def own_s_mem(+grammar: +List<Core.Production>, +q: Nat, fo: +List<Core.Tree>, +k: Nat, +x: Core.Bsr, +m: {Core.member(x, ownS(grammar, q, fo, k)) == True{} : Bool}) -> {Core.member(x, Core.own(q, fo, 0n, k, k)) == True{} : Bool}:
  match fo:
    case Nil{}:
      emptyif_mem(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.Bsr{q, 0n, k, k, k}, x, m)
    case Con{+t, +rest}:
      %Equal.sym(+List<Core.Bsr>, Core.own(q, t <> rest, 0n, k, k), WC.ownNE(q, t <> rest, 0n, k, k), WC.own_first(q, t, rest, 0n, k, k)) : {Core.member(x, _) == True{} : Bool}
      m

def node_mem_pick(+grammar: +List<Core.Production>, +q: Nat, +fo: +List<Core.Tree>, +k: Nat, +x: Core.Bsr,
  c: Either<{Core.member(x, ownS(grammar, q, fo, k)) == True{} : Bool}, {Core.member(x, Core.steps(fo, k)) == True{} : Bool}>) -> {Core.member(x, Core.steps([Core.Node{q, fo}], k)) == True{} : Bool}:
  match c:
    case Inl{m}:
      WC.mem_left(Core.own(q, fo, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(fo, k), []), x, own_s_mem(grammar, q, fo, k, x, m))
    case Inr{m}:
      WC.mem_right(Core.own(q, fo, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(fo, k), []), x, WC.mem_left(Core.steps(fo, k), [], x, m))

# A prefix forest's steps in its node are steps of the node.
def node_mem(+grammar: +List<Core.Production>, +q: Nat, +fo: +List<Core.Tree>, +k: Nat, +x: Core.Bsr, +m: {Core.member(x, stepsP(grammar, q, fo, k)) == True{} : Bool}) -> {Core.member(x, Core.steps([Core.Node{q, fo}], k)) == True{} : Bool}:
  node_mem_pick(grammar, q, fo, k, x, WC.mem_split(ownS(grammar, q, fo, k), Core.steps(fo, k), x, m))

def flag_move(fl: Bool, +target: Core.Bsr, +a: +List<Core.Bsr>, +b: +List<Core.Bsr>, +h: {flagOk(fl, target, a) == True{} : Bool},
  s: {Core.member(target, a) == True{} : Bool} -> {Core.member(target, b) == True{} : Bool}) -> {flagOk(fl, target, b) == True{} : Bool}:
  match fl:
    case True{}:
      s(h)
    case False{}:
      {==}

def reads_all(+grammar: +List<Core.Production>, +input: +List<Nat>, +fo: +List<Core.Tree>, +items: +List<Core.Sym>, +k: Nat,
  +r: {Core.reads(fo, grammar, takeN(List.length(&2, Core.Sym, items), items), input, k) == True{} : Bool}) -> {Core.reads(fo, grammar, items, input, k) == True{} : Bool}:
  %take_all(items) : {Core.reads(fo, grammar, _, input, k) == True{} : Bool}
  r

def eq_is(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

def need_to(+need: Core.Need, +k: Nat, +j: Nat, +w: Nat, +e: {w == j : Nat}, +h: {Gll.needHolds(need, k, j) == True{} : Bool})
  -> {Gll.needHolds(need, k, w) == True{} : Bool}:
  %Equal.sym(Nat, w, j, e) : {Gll.needHolds(need, k, _) == True{} : Bool}
  h

# A sound prefix forest of the whole production is a sound item node.
def node_item_ok(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +fl: Bool, +fo: +List<Core.Tree>, +index: Nat, +x: Nat, +need: Core.Need, +k: Nat, +j: Nat,
  +hl: {Core.lhsIs(grammar, index, x) == True{} : Bool}, +hn: {Gll.needHolds(need, k, j) == True{} : Bool},
  +hp: {prefOk(grammar, input, target, index, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), j, fl, fo) == True{} : Bool})
  -> {itemOk(grammar, input, target, Core.Nonterminal{x, need}, k, j, fl, [Core.Node{index, fo}]) == True{} : Bool}:
  +rhs = Core.rhsOf(grammar, index)
  +R = {Core.reads(fo, grammar, takeN(List.length(&2, Core.Sym, rhs), rhs), input, k) : Bool}
  +E = {Nat.is_eq(G.endOf(fo, k), j) : Bool}
  +Fl = {flagOk(fl, target, stepsP(grammar, index, fo, k)) : Bool}
  +r = Lemma.and_true_left(R, Bool.and(E, Fl), hp)
  +r2 = Lemma.and_true_right_side(R, Bool.and(E, Fl), hp)
  +ej = Lemma.nat_eq_sound(G.endOf(fo, k), j, Lemma.and_true_left(E, Fl, r2))
  +hf = Lemma.and_true_right_side(E, Fl, r2)
  +w = Core.width(Core.Node{index, fo})
  +eqj = Equal.trans(Nat, Nat.add(k, w), G.endOf(fo, k), j, Equal.sym(Nat, G.endOf(fo, k), Nat.add(k, w), G.end_node(index, fo, k)), ej)
  +nk = need_ok(need, k, w, need_to(need, k, j, Nat.add(k, w), eqj, hn))
  +head = {Bool.and(Core.lhsIs(grammar, index, x), Core.needOk(need, w)) : Bool}
  +own = {Bool.and(head, Core.reads(fo, grammar, rhs, input, k)) : Bool}
  +rd = Lemma.and_true_intro(own, True{}, Lemma.and_true_intro(head, Core.reads(fo, grammar, rhs, input, k), Lemma.and_true_intro(Core.lhsIs(grammar, index, x), Core.needOk(need, w), hl, nk), reads_all(grammar, input, fo, rhs, k, r)), {==})
  +st = Core.steps([Core.Node{index, fo}], k)
  Lemma.and_true_intro(Core.reads([Core.Node{index, fo}], grammar, [Core.Nonterminal{x, need}], input, k), Bool.and(Nat.is_eq(Nat.add(k, w), j), flagOk(fl, target, st)), rd,
    Lemma.and_true_intro(Nat.is_eq(Nat.add(k, w), j), flagOk(fl, target, st), eq_is(Nat.add(k, w), j, eqj), flag_move(fl, target, stepsP(grammar, index, fo, k), st, hf, m => node_mem(grammar, index, fo, k, target, m))))

law nodeopts_ok:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +index: Nat
  for +x: Nat
  for +need: Core.Need
  for +k: Nat
  for +j: Nat
  for +hl: {Core.lhsIs(grammar, index, x) == True{} : Bool}
  for +hn: {Gll.needHolds(need, k, j) == True{} : Bool}
  for +hO: {optsOk(os, grammar, input, target, index, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), j) == True{} : Bool}
  {itemsOk(W.nodeOpts(index, os), grammar, input, target, Core.Nonterminal{x, need}, k, j) == True{} : Bool}

def nodeopts_ok(os, grammar, input, target, index, x, need, k, j, hl, hn, hO):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +L = List.length(&2, Core.Sym, Core.rhsOf(grammar, index))
      Lemma.and_true_intro(itemOk(grammar, input, target, Core.Nonterminal{x, need}, k, j, fl, [Core.Node{index, fo}]), itemsOk(W.nodeOpts(index, rest), grammar, input, target, Core.Nonterminal{x, need}, k, j),
        node_item_ok(grammar, input, target, fl, fo, index, x, need, k, j, hl, hn, Lemma.and_true_left(prefOk(grammar, input, target, index, k, L, j, fl, fo), optsOk(rest, grammar, input, target, index, k, L, j), hO)),
        nodeopts_ok(rest, grammar, input, target, index, x, need, k, j, hl, hn, Lemma.and_true_right_side(prefOk(grammar, input, target, index, k, L, j, fl, fo), optsOk(rest, grammar, input, target, index, k, L, j), hO)))

law items_app:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +y: Core.Sym
  for +k: Nat
  for +j: Nat
  for +hx: {itemsOk(xs, grammar, input, target, y, k, j) == True{} : Bool}
  for +hy: {itemsOk(ys, grammar, input, target, y, k, j) == True{} : Bool}
  {itemsOk(List.append(&2, W.Opt, xs, ys), grammar, input, target, y, k, j) == True{} : Bool}

def items_app(xs, ys, grammar, input, target, y, k, j, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{W.Opt{+fl, +fo}, +rest}:
      +io = {itemOk(grammar, input, target, y, k, j, fl, fo) : Bool}
      Lemma.and_true_intro(io, itemsOk(List.append(&2, W.Opt, rest, ys), grammar, input, target, y, k, j), Lemma.and_true_left(io, itemsOk(rest, grammar, input, target, y, k, j), hx),
        items_app(rest, ys, grammar, input, target, y, k, j, Lemma.and_true_right_side(io, itemsOk(rest, grammar, input, target, y, k, j), hx), hy))

def opts_len(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +os: +List<W.Opt>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +k: Nat, +j: Nat,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +h: {optsOk(os, grammar, input, target, base, k, List.length(&2, Core.Sym, rhs), j) == True{} : Bool}) -> {optsOk(os, grammar, input, target, base, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, base)), j) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, Core.rhsOf(grammar, base), rhs, N.drop_rhs(base, grammar, lhs, rhs, rest, hg)) : {optsOk(os, grammar, input, target, base, k, List.length(&2, Core.Sym, _), j) == True{} : Bool}
  h

def pick_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +x: Nat, +need: Core.Need, +k: Nat, +j: Nat,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +eb: {Nat.is_eq(lhs, x) == b : Bool}, +hF: {factsOk(F, grammar, input, target) == True{} : Bool}, +hn: {Gll.needHolds(need, k, j) == True{} : Bool})
  -> {itemsOk(W.prodPick(b, grammar, target, base, List.length(&2, Core.Sym, rhs), k, j, F), grammar, input, target, Core.Nonterminal{x, need}, k, j) == True{} : Bool}:
  match b:
    case True{}:
      +os = W.optsAt(grammar, target, base, k, List.length(&2, Core.Sym, rhs), j, F)
      nodeopts_ok(os, grammar, input, target, base, x, need, k, j, G.head_lhs(grammar, base, x, lhs, rhs, rest, hg, eb), hn,
        opts_len(grammar, input, target, os, base, lhs, rhs, rest, k, j, hg, opts_at_ok(grammar, input, target, F, base, k, List.length(&2, Core.Sym, rhs), j, hF)))
    case False{}:
      {==}

law prod_ok:
  for g: +List<Core.Production>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +base: Nat
  for +x: Nat
  for +need: Core.Need
  for +k: Nat
  for +j: Nat
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  for +hn: {Gll.needHolds(need, k, j) == True{} : Bool}
  {itemsOk(W.prodOpts(g, grammar, target, base, x, k, j, F), grammar, input, target, Core.Nonterminal{x, need}, k, j) == True{} : Bool}

def prod_ok(g, grammar, input, target, F, base, x, need, k, j, hg, hF, hn):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      items_app(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, List.length(&2, Core.Sym, rhs), k, j, F), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), grammar, input, target, Core.Nonterminal{x, need}, k, j,
        pick_ok(Nat.is_eq(lhs, x), grammar, input, target, F, base, lhs, rhs, rest, x, need, k, j, hg, {==}, hF, hn),
        prod_ok(rest, grammar, input, target, F, 1n+base, x, need, k, j, G.drop_step(base, grammar, lhs, rhs, rest, hg), hF, hn))

def need_pick_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +os: +List<W.Opt>, +y: Core.Sym, +k: Nat, +j: Nat,
  h: {b == True{} : Bool} -> {itemsOk(os, grammar, input, target, y, k, j) == True{} : Bool}) -> {itemsOk(W.needIf(b, os), grammar, input, target, y, k, j) == True{} : Bool}:
  match b:
    case True{}:
      h({==})
    case False{}:
      {==}

# Every option of an item is a sound tree for it.
def items_at(y: Core.Sym, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +k: Nat, +j: Nat, +hF: {factsOk(F, grammar, input, target) == True{} : Bool})
  -> {itemsOk(W.itemOpts(Some{y}, grammar, input, target, k, j, F), grammar, input, target, y, k, j) == True{} : Bool}:
  match y:
    case Core.Terminal{+t}:
      leaf_ok(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(j, 1n+k)), grammar, input, target, t, k, j, {==})
    case Core.Nonterminal{+x, +need}:
      need_pick_ok(Gll.needHolds(need, k, j), grammar, input, target, W.prodOpts(grammar, grammar, target, 0n, x, k, j, F), Core.Nonterminal{x, need}, k, j,
        hb => prod_ok(grammar, grammar, input, target, F, 0n, x, need, k, j, {==}, hF, hb))

# ---- Joining a prefix and an item ----

# Every option is sound once its flag is marked with `here`.
def optsOkM(os: +List<W.Opt>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +here: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.and(prefOk(grammar, input, target, q, ks, d, e, Bool.or(fl, here), fo), optsOkM(rest, grammar, input, target, here, q, ks, d, e))

law mark_ok:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +here: Bool
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +h: {optsOkM(os, grammar, input, target, here, q, ks, d, e) == True{} : Bool}
  {optsOk(W.markIf(here, os), grammar, input, target, q, ks, d, e) == True{} : Bool}

def mark_ok(os, grammar, input, target, here, q, ks, d, e, h):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +po = {prefOk(grammar, input, target, q, ks, d, e, Bool.or(fl, here), fo) : Bool}
      Lemma.and_true_intro(po, optsOk(W.markIf(here, rest), grammar, input, target, q, ks, d, e), Lemma.and_true_left(po, optsOkM(rest, grammar, input, target, here, q, ks, d, e), h),
        mark_ok(rest, grammar, input, target, here, q, ks, d, e, Lemma.and_true_right_side(po, optsOkM(rest, grammar, input, target, here, q, ks, d, e), h)))

law okm_app:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +here: Bool
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +hx: {optsOkM(xs, grammar, input, target, here, q, ks, d, e) == True{} : Bool}
  for +hy: {optsOkM(ys, grammar, input, target, here, q, ks, d, e) == True{} : Bool}
  {optsOkM(List.append(&2, W.Opt, xs, ys), grammar, input, target, here, q, ks, d, e) == True{} : Bool}

def okm_app(xs, ys, grammar, input, target, here, q, ks, d, e, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{W.Opt{+fl, +fo}, +rest}:
      +po = {prefOk(grammar, input, target, q, ks, d, e, Bool.or(fl, here), fo) : Bool}
      Lemma.and_true_intro(po, optsOkM(List.append(&2, W.Opt, rest, ys), grammar, input, target, here, q, ks, d, e), Lemma.and_true_left(po, optsOkM(rest, grammar, input, target, here, q, ks, d, e), hx),
        okm_app(rest, ys, grammar, input, target, here, q, ks, d, e, Lemma.and_true_right_side(po, optsOkM(rest, grammar, input, target, here, q, ks, d, e), hx), hy))

law drop_ne:
  for d: Nat
  for items: +List<Core.Sym>
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, items) == y <> rest : +List<Core.Sym>}
  {List.is_empty(&2, Core.Sym, items) == False{} : Bool}

def drop_ne(d, items, y, rest, ie):
  match d items:
    case 0n +its:
      %Equal.sym(+List<Core.Sym>, its, y <> rest, ie) : {List.is_empty(&2, Core.Sym, _) == False{} : Bool}
      {==}
    case 1n+(+m) Nil{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.true_is_not_false(Equal.cong(+List<Core.Sym>, Bool, v => List.is_empty(&2, Core.Sym, v), [], y <> rest, ie)))
    case 1n+(+m) Con{+x, +r}:
      {==}

def empty_none(e: Bool, +b0: Core.Bsr, +x: Core.Bsr, +ys: +List<Core.Bsr>, +ne: {e == False{} : Bool}, +m: {Core.member(x, emptyIf(e, b0)) == True{} : Bool}) -> {Core.member(x, ys) == True{} : Bool}:
  match e:
    case True{}:
      Empty.absurd({Core.member(x, ys) == True{} : Bool}, Lemma.true_is_not_false(ne))
    case False{}:
      Empty.absurd({Core.member(x, ys) == True{} : Bool}, Lemma.false_is_not_true(m))

def sa_own(+grammar: +List<Core.Production>, +q: Nat, fo: +List<Core.Tree>, +t: Core.Tree, +ks: Nat, +x: Core.Bsr,
  +ne: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == False{} : Bool}, +m: {Core.member(x, ownS(grammar, q, fo, ks)) == True{} : Bool}) -> {Core.member(x, ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)) == True{} : Bool}:
  match fo:
    case Nil{}:
      empty_none(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.Bsr{q, 0n, ks, ks, ks}, x, ownS(grammar, q, [t], ks), ne, m)
    case Con{+s, +r}:
      own_pre(q, s <> r, t, 0n, ks, ks, x, m)

def sa_pick(+grammar: +List<Core.Production>, +q: Nat, +fo: +List<Core.Tree>, +t: Core.Tree, +ks: Nat, +x: Core.Bsr,
  +ne: {List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)) == False{} : Bool},
  c: Either<{Core.member(x, ownS(grammar, q, fo, ks)) == True{} : Bool}, {Core.member(x, Core.steps(fo, ks)) == True{} : Bool}>) -> {Core.member(x, stepsP(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)) == True{} : Bool}:
  match c:
    case Inl{m}:
      WC.mem_left(ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), Core.steps(List.append(&2, Core.Tree, fo, [t]), ks), x, sa_own(grammar, q, fo, t, ks, x, ne, m))
    case Inr{m}:
      WC.mem_right(ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), Core.steps(List.append(&2, Core.Tree, fo, [t]), ks), x, mem_steps_l(fo, t, ks, x, m))

def steps_at(+t: Core.Tree, +a: Nat, +b: Nat, +x: Core.Bsr, +e: {a == b : Nat}, +m: {Core.member(x, Core.steps([t], b)) == True{} : Bool}) -> {Core.member(x, Core.steps([t], a)) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.member(x, Core.steps([t], _)) == True{} : Bool}
  m

def sb_fn(+grammar: +List<Core.Production>, +q: Nat, +fo: +List<Core.Tree>, +t: Core.Tree, +ks: Nat, +k: Nat, +x: Core.Bsr,
  +ek: {G.endOf(fo, ks) == k : Nat}, +m: {Core.member(x, Core.steps([t], k)) == True{} : Bool}) -> {Core.member(x, stepsP(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)) == True{} : Bool}:
  WC.mem_right(ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), Core.steps(List.append(&2, Core.Tree, fo, [t]), ks), x, mem_steps_r(fo, t, ks, x, steps_at(t, G.endOf(fo, ks), k, x, ek, m)))

def ownS_snoc(+grammar: +List<Core.Production>, +q: Nat, fo: +List<Core.Tree>, +t: Core.Tree, +ks: Nat, +x: Core.Bsr,
  +m: {Core.member(x, WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), 0n, ks, ks)) == True{} : Bool}) -> {Core.member(x, ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)) == True{} : Bool}:
  match fo:
    case Nil{}:
      m
    case Con{+s, +r}:
      m

def bsr_fields(+q: Nat, +d1: Nat, +d2: Nat, +ks: Nat, +k1: Nat, +k2: Nat, +j1: Nat, +j2: Nat, +xs: +List<Core.Bsr>,
  +e1: {d1 == d2 : Nat}, +e2: {k1 == k2 : Nat}, +e3: {j1 == j2 : Nat},
  +h: {Core.member(Core.Bsr{q, 1n+d1, ks, k1, j1}, xs) == True{} : Bool}) -> {Core.member(Core.Bsr{q, 1n+d2, ks, k2, j2}, xs) == True{} : Bool}:
  %e1 : {Core.member(Core.Bsr{q, 1n+_, ks, k2, j2}, xs) == True{} : Bool}
  %e2 : {Core.member(Core.Bsr{q, 1n+d1, ks, _, j2}, xs) == True{} : Bool}
  %e3 : {Core.member(Core.Bsr{q, 1n+d1, ks, k1, _}, xs) == True{} : Bool}
  h

def to_target(+b: Core.Bsr, +target: Core.Bsr, +xs: +List<Core.Bsr>, +e: {b == target : Core.Bsr}, +h: {Core.member(b, xs) == True{} : Bool}) -> {Core.member(target, xs) == True{} : Bool}:
  %e : {Core.member(_, xs) == True{} : Bool}
  h

# The step of the joined child: it is the node's own step after the prefix.
def hh_fn(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +fo: +List<Core.Tree>, +t: Core.Tree,
  +len: {List.length(&2, Core.Tree, fo) == d : Nat}, +ek: {G.endOf(fo, ks) == k : Nat}, +ej: {G.endOf([t], k) == j : Nat},
  +hh: {Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target) == True{} : Bool}) -> {Core.member(target, stepsP(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)) == True{} : Bool}:
  +ew = endW(fo, ks)
  +eK = Equal.trans(Nat, ew, G.endOf(fo, ks), k, end_w(fo, ks), ek)
  +eJ = Equal.trans(Nat, Nat.add(ew, Core.width(t)), Nat.add(k, Core.width(t)), j, Equal.cong(Nat, Nat, v => Nat.add(v, Core.width(t)), ew, k, eK),
    Equal.trans(Nat, Nat.add(k, Core.width(t)), G.endOf([t], k), j, Equal.sym(Nat, G.endOf([t], k), Nat.add(k, Core.width(t)), end_one(t, k)), ej))
  +b = {Core.Bsr{q, 1n+d, ks, k, j} : Core.Bsr}
  +mb = bsr_fields(q, List.length(&2, Core.Tree, fo), d, ks, ew, k, Nat.add(ew, Core.width(t)), j, WC.ownNE(q, List.append(&2, Core.Tree, fo, [t]), 0n, ks, ks), len, eK, eJ, own_last(q, fo, t, 0n, ks, ks))
  to_target(b, target, stepsP(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), G.bsr_eq_sound(b, target, hh),
    WC.mem_left(ownS(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks), Core.steps(List.append(&2, Core.Tree, fo, [t]), ks), b, ownS_snoc(grammar, q, fo, t, ks, b, mb)))

def reads_at(+grammar: +List<Core.Production>, +input: +List<Nat>, +t: Core.Tree, +y: Core.Sym, +a: Nat, +k: Nat, +e: {a == k : Nat},
  +r: {Core.reads([t], grammar, [y], input, k) == True{} : Bool}) -> {Core.reads([t], grammar, [y], input, a) == True{} : Bool}:
  %Equal.sym(Nat, a, k, e) : {Core.reads([t], grammar, [y], input, _) == True{} : Bool}
  r

def reads_new(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fo: +List<Core.Tree>, +t: Core.Tree, +y: Core.Sym, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +r1: {Core.reads(fo, grammar, takeN(d, Core.rhsOf(grammar, q)), input, ks) == True{} : Bool},
  +ri: {Core.reads([t], grammar, [y], input, k) == True{} : Bool}, +ek: {G.endOf(fo, ks) == k : Nat})
  -> {Core.reads(List.append(&2, Core.Tree, fo, [t]), grammar, takeN(1n+d, Core.rhsOf(grammar, q)), input, ks) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, takeN(1n+d, Core.rhsOf(grammar, q)), List.append(&2, Core.Sym, takeN(d, Core.rhsOf(grammar, q)), [y]), take_snoc(d, Core.rhsOf(grammar, q), y, rest, ie)) : {Core.reads(List.append(&2, Core.Tree, fo, [t]), grammar, _, input, ks) == True{} : Bool}
  reads_snoc(fo, takeN(d, Core.rhsOf(grammar, q)), grammar, input, ks, t, y, r1, reads_at(grammar, input, t, y, G.endOf(fo, ks), k, ek, ri))

# A sound prefix and a sound item give a sound joined forest, flag marked.
def one_ok(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +f1: Bool, +fo: +List<Core.Tree>, +t: Core.Tree, +f2: Bool, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +y: Core.Sym, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +hp: {prefOk(grammar, input, target, q, ks, d, k, f1, fo) == True{} : Bool},
  +ri: {Core.reads([t], grammar, [y], input, k) == True{} : Bool}, +ej0: {Nat.is_eq(G.endOf([t], k), j) == True{} : Bool},
  +hf2: {flagOk(f2, target, Core.steps([t], k)) == True{} : Bool})
  -> {prefOk(grammar, input, target, q, ks, 1n+d, j, Bool.or(Bool.or(f1, f2), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)), List.append(&2, Core.Tree, fo, [t])) == True{} : Bool}:
  +R = {Core.reads(fo, grammar, takeN(d, Core.rhsOf(grammar, q)), input, ks) : Bool}
  +E = {Nat.is_eq(G.endOf(fo, ks), k) : Bool}
  +Fl = {flagOk(f1, target, stepsP(grammar, q, fo, ks)) : Bool}
  +r1 = Lemma.and_true_left(R, Bool.and(E, Fl), hp)
  +r2 = Lemma.and_true_right_side(R, Bool.and(E, Fl), hp)
  +ek = Lemma.nat_eq_sound(G.endOf(fo, ks), k, Lemma.and_true_left(E, Fl, r2))
  +hf1 = Lemma.and_true_right_side(E, Fl, r2)
  +ej = Lemma.nat_eq_sound(G.endOf([t], k), j, ej0)
  +len = Equal.trans(Nat, List.length(&2, Core.Tree, fo), List.length(&2, Core.Sym, takeN(d, Core.rhsOf(grammar, q))), d, PP.reads_length(fo, takeN(d, Core.rhsOf(grammar, q)), grammar, input, ks, r1), take_len(d, Core.rhsOf(grammar, q), y, rest, ie))
  +ne = drop_ne(d, Core.rhsOf(grammar, q), y, rest, ie)
  +sp = stepsP(grammar, q, List.append(&2, Core.Tree, fo, [t]), ks)
  +ee = eq_is(G.endOf(List.append(&2, Core.Tree, fo, [t]), ks), j, Equal.trans(Nat, G.endOf(List.append(&2, Core.Tree, fo, [t]), ks), G.endOf([t], G.endOf(fo, ks)), j, end_snoc(fo, t, ks),
    Equal.trans(Nat, G.endOf([t], G.endOf(fo, ks)), G.endOf([t], k), j, Equal.cong(Nat, Nat, v => G.endOf([t], v), G.endOf(fo, ks), k, ek), ej)))
  +fl = flag_mark(Bool.or(f1, f2), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), target, sp,
    flag_or(f1, f2, target, stepsP(grammar, q, fo, ks), Core.steps([t], k), sp, hf1, hf2,
      m => sa_pick(grammar, q, fo, t, ks, target, ne, WC.mem_split(ownS(grammar, q, fo, ks), Core.steps(fo, ks), target, m)),
      m => sb_fn(grammar, q, fo, t, ks, k, target, ek, m)),
    h => hh_fn(grammar, input, target, q, ks, d, k, j, fo, t, len, ek, ej, h))
  Lemma.and_true_intro(Core.reads(List.append(&2, Core.Tree, fo, [t]), grammar, takeN(1n+d, Core.rhsOf(grammar, q)), input, ks), Bool.and(Nat.is_eq(G.endOf(List.append(&2, Core.Tree, fo, [t]), ks), j), flagOk(Bool.or(Bool.or(f1, f2), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)), target, sp)),
    reads_new(grammar, input, target, q, ks, d, k, fo, t, y, rest, ie, r1, ri, ek),
    Lemma.and_true_intro(Nat.is_eq(G.endOf(List.append(&2, Core.Tree, fo, [t]), ks), j), flagOk(Bool.or(Bool.or(f1, f2), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)), target, sp), ee, fl))

law with_ok:
  for P: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +t: Core.Tree
  for +f2: Bool
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +j: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +hP: {optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool}
  for +ri: {Core.reads([t], grammar, [y], input, k) == True{} : Bool}
  for +ej0: {Nat.is_eq(G.endOf([t], k), j) == True{} : Bool}
  for +hf2: {flagOk(f2, target, Core.steps([t], k)) == True{} : Bool}
  {optsOkM(W.withTree(t, f2, P), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j) == True{} : Bool}

def with_ok(P, grammar, input, target, t, f2, q, ks, d, k, j, y, rest, ie, hP, ri, ej0, hf2):
  match P:
    case Nil{}:
      {==}
    case Con{W.Opt{+f1, +fo}, +restP}:
      +po = {prefOk(grammar, input, target, q, ks, d, k, f1, fo) : Bool}
      Lemma.and_true_intro(prefOk(grammar, input, target, q, ks, 1n+d, j, Bool.or(Bool.or(f1, f2), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)), List.append(&2, Core.Tree, fo, [t])), optsOkM(W.withTree(t, f2, restP), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j),
        one_ok(grammar, input, target, f1, fo, t, f2, q, ks, d, k, j, y, rest, ie, Lemma.and_true_left(po, optsOk(restP, grammar, input, target, q, ks, d, k), hP), ri, ej0, hf2),
        with_ok(restP, grammar, input, target, t, f2, q, ks, d, k, j, y, rest, ie, Lemma.and_true_right_side(po, optsOk(restP, grammar, input, target, q, ks, d, k), hP), ri, ej0, hf2))

def join_one(fo2: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +f2: Bool, +P: +List<W.Opt>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +y: Core.Sym, +rest: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +hP: {optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool},
  +hit: {itemOk(grammar, input, target, y, k, j, f2, fo2) == True{} : Bool}) -> {optsOkM(W.withTreeList(fo2, f2, P), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j) == True{} : Bool}:
  match fo2:
    case Nil{}:
      {==}
    case Con{+t, Nil{}}:
      +R = {Core.reads([t], grammar, [y], input, k) : Bool}
      +E = {Nat.is_eq(G.endOf([t], k), j) : Bool}
      +Fl = {flagOk(f2, target, Core.steps([t], k)) : Bool}
      +r2 = Lemma.and_true_right_side(R, Bool.and(E, Fl), hit)
      with_ok(P, grammar, input, target, t, f2, q, ks, d, k, j, y, rest, ie, hP, Lemma.and_true_left(R, Bool.and(E, Fl), hit), Lemma.and_true_left(E, Fl, r2), Lemma.and_true_right_side(E, Fl, r2))
    case Con{+t, Con{+t2, +more}}:
      {==}

law join_ok:
  for +P: +List<W.Opt>
  for I: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +j: Nat
  for +y: Core.Sym
  for +rest: +List<Core.Sym>
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>}
  for +hP: {optsOk(P, grammar, input, target, q, ks, d, k) == True{} : Bool}
  for +hI: {itemsOk(I, grammar, input, target, y, k, j) == True{} : Bool}
  {optsOkM(W.joinAll(P, I), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j) == True{} : Bool}

def join_ok(P, I, grammar, input, target, q, ks, d, k, j, y, rest, ie, hP, hI):
  match I:
    case Nil{}:
      {==}
    case Con{W.Opt{+f2, +fo2}, +restI}:
      +io = {itemOk(grammar, input, target, y, k, j, f2, fo2) : Bool}
      okm_app(W.withTreeList(fo2, f2, P), W.joinAll(P, restI), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j,
        join_one(fo2, grammar, input, target, f2, P, q, ks, d, k, j, y, rest, ie, hP, Lemma.and_true_left(io, itemsOk(restI, grammar, input, target, y, k, j), hI)),
        join_ok(P, restI, grammar, input, target, q, ks, d, k, j, y, rest, ie, hP, Lemma.and_true_right_side(io, itemsOk(restI, grammar, input, target, y, k, j), hI)))

law facts_of_ok:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +q: Nat
  for +ks: Nat
  for +dt: Nat
  for +e: Nat
  for +hO: {optsOk(os, grammar, input, target, q, ks, dt, e) == True{} : Bool}
  {factsOk(W.factsOf(q, ks, dt, e, os), grammar, input, target) == True{} : Bool}

def facts_of_ok(os, grammar, input, target, q, ks, dt, e, hO):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +po = {prefOk(grammar, input, target, q, ks, dt, e, fl, fo) : Bool}
      Lemma.and_true_intro(po, factsOk(W.factsOf(q, ks, dt, e, rest), grammar, input, target), Lemma.and_true_left(po, optsOk(rest, grammar, input, target, q, ks, dt, e), hO),
        facts_of_ok(rest, grammar, input, target, q, ks, dt, e, Lemma.and_true_right_side(po, optsOk(rest, grammar, input, target, q, ks, dt, e), hO)))

def symOr(m: Maybe<&2, Core.Sym>, +x: Core.Sym) -> Core.Sym:
  match m:
    case Some{+s}:
      s
    case None{}:
      x

def maybeSome(m: Maybe<&2, Core.Sym>) -> Bool:
  match m:
    case Some{s}:
      True{}
    case None{}:
      False{}

law nth_rev:
  for items: +List<Core.Sym>
  for d: Nat
  for +y: Core.Sym
  for +h: {Gll.nthSym(items, d) == Some{y} : Maybe<&2, Core.Sym>}
  {G.dropFrom(d, items) == y <> G.dropFrom(1n+d, items) : +List<Core.Sym>}

def nth_rev(items, d, y, h):
  match items d:
    case Nil{} +d0:
      Empty.absurd({G.dropFrom(d0, []) == y <> G.dropFrom(1n+d0, []) : +List<Core.Sym>}, Lemma.false_is_not_true(Equal.cong(Maybe<&2, Core.Sym>, Bool, v => maybeSome(v), None{}, Some{y}, h)))
    case Con{+x, +r} 0n:
      +e = Equal.cong(Maybe<&2, Core.Sym>, Core.Sym, v => symOr(v, x), Some{x}, Some{y}, h)
      %Equal.sym(Core.Sym, x, y, e) : {_ <> r == y <> r : +List<Core.Sym>}
      {==}
    case Con{+x, +r} 1n+(+m):
      nth_rev(r, m, y, h)

def join_item(item: Maybe<&2, Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat,
  +hF: {factsOk(F, grammar, input, target) == True{} : Bool},
  +ei: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>})
  -> {optsOkM(W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(item, grammar, input, target, k, j, F)), grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j) == True{} : Bool}:
  match item:
    case Some{+y}:
      join_ok(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Some{y}, grammar, input, target, k, j, F), grammar, input, target, q, ks, d, k, j, y, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), nth_rev(Core.rhsOf(grammar, q), d, y, ei),
        opts_at_ok(grammar, input, target, F, q, ks, d, k, hF), items_at(y, grammar, input, target, F, k, j, hF))
    case None{}:
      {==}

# The facts a step makes from sound facts are sound.
def step_ok(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, e: Core.Bsr, +hF: {factsOk(F, grammar, input, target) == True{} : Bool})
  -> {factsOk(W.stepFacts(grammar, input, target, F, e), grammar, input, target) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +ks, +k, +j}:
      {==}
    case Core.Bsr{+q, 1n+(+d), +ks, +k, +j}:
      +os = W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F))
      facts_of_ok(W.markIf(Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), os), grammar, input, target, q, ks, 1n+d, j,
        mark_ok(os, grammar, input, target, Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), q, ks, 1n+d, j, join_item(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, F, q, ks, d, k, j, hF, {==})))

def add_pick_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +F: +List<W.Fact>,
  +hp: {prefOk(grammar, input, target, q, ks, d, e, f, fo) == True{} : Bool}, +hF: {factsOk(F, grammar, input, target) == True{} : Bool})
  -> {factsOk(W.addPick(b, W.Fact{q, ks, d, e, f, fo}, F), grammar, input, target) == True{} : Bool}:
  match b:
    case True{}:
      hF
    case False{}:
      Lemma.and_true_intro(prefOk(grammar, input, target, q, ks, d, e, f, fo), factsOk(F, grammar, input, target), hp, hF)

law add_ok:
  for new: +List<W.Fact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +hn: {factsOk(new, grammar, input, target) == True{} : Bool}
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  {factsOk(W.addNew(new, F), grammar, input, target) == True{} : Bool}

def add_ok(new, grammar, input, target, F, hn, hF):
  match new:
    case Nil{}:
      hF
    case Con{W.Fact{+q, +ks, +d, +e, +f, +fo}, +rest}:
      +po = {prefOk(grammar, input, target, q, ks, d, e, f, fo) : Bool}
      add_ok(rest, grammar, input, target, W.addPick(W.hasFact(q, ks, d, e, f, F), W.Fact{q, ks, d, e, f, fo}, F), Lemma.and_true_right_side(po, factsOk(rest, grammar, input, target), hn),
        add_pick_ok(W.hasFact(q, ks, d, e, f, F), grammar, input, target, q, ks, d, e, f, fo, F, Lemma.and_true_left(po, factsOk(rest, grammar, input, target), hn), hF))

law round_ok:
  for ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  {factsOk(W.roundOf(ps, grammar, input, target, F), grammar, input, target) == True{} : Bool}

def round_ok(ps, grammar, input, target, F, hF):
  match ps:
    case Nil{}:
      hF
    case Con{+e, +rest}:
      +sf = W.stepFacts(grammar, input, target, F, e)
      round_ok(rest, grammar, input, target, W.addNew(sf, F), add_ok(sf, grammar, input, target, F, step_ok(grammar, input, target, F, e, hF), hF))

law fix_ok:
  for fuel: Nat
  for +ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  {factsOk(W.fixpoint(fuel, ps, grammar, input, target, F), grammar, input, target) == True{} : Bool}

def fix_ok(fuel, ps, grammar, input, target, F, hF):
  match fuel:
    case 0n:
      hF
    case 1n+(+f):
      fix_ok(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F), round_ok(ps, grammar, input, target, F, hF))

# ======== WHAT THE ROOT SEARCH HANDS OUT ========

def treesGood(fs: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +start: Nat) -> Bool:
  match fs:
    case Con{+t, Nil{}}:
      Bool.and(Exact.treeOk(grammar, start, input, t), Core.member(target, Core.steps([t], 0n)))
    case _:
      False{}

# Nothing, or one parse tree of the input that contains the target.
def rootGood(m: Maybe<&2, +List<Core.Tree>>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +start: Nat) -> Bool:
  match m:
    case Some{+fs}:
      treesGood(fs, grammar, input, target, start)
    case None{}:
      True{}

def tree_good(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +index: Nat, +fo: +List<Core.Tree>, +start: Nat,
  +hl: {Core.lhsIs(grammar, index, start) == True{} : Bool},
  +hp: {prefOk(grammar, input, target, index, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), List.length(&2, Nat, input), True{}, fo) == True{} : Bool})
  -> {Bool.and(Exact.treeOk(grammar, start, input, Core.Node{index, fo}), Core.member(target, Core.steps([Core.Node{index, fo}], 0n))) == True{} : Bool}:
  +rhs = Core.rhsOf(grammar, index)
  +R = {Core.reads(fo, grammar, takeN(List.length(&2, Core.Sym, rhs), rhs), input, 0n) : Bool}
  +E = {Nat.is_eq(G.endOf(fo, 0n), List.length(&2, Nat, input)) : Bool}
  +Fl = {flagOk(True{}, target, stepsP(grammar, index, fo, 0n)) : Bool}
  +r = reads_all(grammar, input, fo, rhs, 0n, Lemma.and_true_left(R, Bool.and(E, Fl), hp))
  +r2 = Lemma.and_true_right_side(R, Bool.and(E, Fl), hp)
  +en = Lemma.nat_eq_sound(G.endOf(fo, 0n), List.length(&2, Nat, input), Lemma.and_true_left(E, Fl, r2))
  +hf = Lemma.and_true_right_side(E, Fl, r2)
  +w = Core.width(Core.Node{index, fo})
  +head = {Bool.and(Core.lhsIs(grammar, index, start), True{}) : Bool}
  +own = {Bool.and(head, Core.reads(fo, grammar, rhs, input, 0n)) : Bool}
  +rd = Lemma.and_true_intro(own, True{}, Lemma.and_true_intro(head, Core.reads(fo, grammar, rhs, input, 0n), Lemma.and_true_intro(Core.lhsIs(grammar, index, start), True{}, hl, {==}), r), {==})
  +lf = Core.leaves(fo)
  +eqn = Equal.trans(Nat, List.length(&2, Nat, List.append(&2, Nat, lf, [])), List.length(&2, Nat, lf), List.length(&2, Nat, input),
    Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, lf, []), lf, Lemma.append_nil_right(lf)),
    Equal.trans(Nat, List.length(&2, Nat, lf), G.endOf(fo, 0n), List.length(&2, Nat, input), Equal.sym(Nat, G.endOf(fo, 0n), List.length(&2, Nat, lf), G.end_eq(fo, 0n)), en))
  +ok = Lemma.and_true_intro(Core.reads([Core.Node{index, fo}], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves([Core.Node{index, fo}])), List.length(&2, Nat, input)), rd,
    eq_is(List.length(&2, Nat, Core.leaves([Core.Node{index, fo}])), List.length(&2, Nat, input), eqn))
  Lemma.and_true_intro(Exact.treeOk(grammar, start, input, Core.Node{index, fo}), Core.member(target, Core.steps([Core.Node{index, fo}], 0n)), ok, node_mem(grammar, index, fo, 0n, target, hf))

def flag_pick_ok(fl: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +fo: +List<Core.Tree>, +index: Nat, +start: Nat, +later: Maybe<&2, +List<Core.Tree>>,
  +hl: {Core.lhsIs(grammar, index, start) == True{} : Bool},
  +hp: {prefOk(grammar, input, target, index, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), List.length(&2, Nat, input), fl, fo) == True{} : Bool},
  +hr: {rootGood(later, grammar, input, target, start) == True{} : Bool})
  -> {rootGood(W.flaggedPick(fl, [Core.Node{index, fo}], later), grammar, input, target, start) == True{} : Bool}:
  match fl:
    case True{}:
      tree_good(grammar, input, target, index, fo, start, hl, hp)
    case False{}:
      hr

law first_ok:
  for os: +List<W.Opt>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +index: Nat
  for +start: Nat
  for +hl: {Core.lhsIs(grammar, index, start) == True{} : Bool}
  for +hO: {optsOk(os, grammar, input, target, index, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, index)), List.length(&2, Nat, input)) == True{} : Bool}
  {rootGood(W.firstFlagged(W.nodeOpts(index, os)), grammar, input, target, start) == True{} : Bool}

def first_ok(os, grammar, input, target, index, start, hl, hO):
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+fl, +fo}, +rest}:
      +L = List.length(&2, Core.Sym, Core.rhsOf(grammar, index))
      +po = {prefOk(grammar, input, target, index, 0n, L, List.length(&2, Nat, input), fl, fo) : Bool}
      flag_pick_ok(fl, grammar, input, target, fo, index, start, W.firstFlagged(W.nodeOpts(index, rest)), hl, Lemma.and_true_left(po, optsOk(rest, grammar, input, target, index, 0n, L, List.length(&2, Nat, input)), hO),
        first_ok(rest, grammar, input, target, index, start, hl, Lemma.and_true_right_side(po, optsOk(rest, grammar, input, target, index, 0n, L, List.length(&2, Nat, input)), hO)))

def root_pick_ok(b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +base: Nat, +lhs: Nat, +rhs: +List<Core.Sym>, +rest: +List<Core.Production>, +start: Nat,
  +hg: {G.dropProds(base, grammar) == Core.Production{lhs, rhs} <> rest : +List<Core.Production>},
  +eb: {Nat.is_eq(lhs, start) == b : Bool}, +hF: {factsOk(F, grammar, input, target) == True{} : Bool})
  -> {rootGood(W.rootPick(b, grammar, target, base, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F), grammar, input, target, start) == True{} : Bool}:
  match b:
    case True{}:
      +os = W.optsAt(grammar, target, base, 0n, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F)
      first_ok(os, grammar, input, target, base, start, G.head_lhs(grammar, base, start, lhs, rhs, rest, hg, eb),
        opts_len(grammar, input, target, os, base, lhs, rhs, rest, 0n, List.length(&2, Nat, input), hg, opts_at_ok(grammar, input, target, F, base, 0n, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), hF)))
    case False{}:
      {==}

def or_else_ok(a: Maybe<&2, +List<Core.Tree>>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +start: Nat, +b: Maybe<&2, +List<Core.Tree>>,
  +ha: {rootGood(a, grammar, input, target, start) == True{} : Bool}, +hb: {rootGood(b, grammar, input, target, start) == True{} : Bool})
  -> {rootGood(W.orElse(a, b), grammar, input, target, start) == True{} : Bool}:
  match a:
    case Some{+x}:
      ha
    case None{}:
      hb

law root_ok:
  for g: +List<Core.Production>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +base: Nat
  for +start: Nat
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +hF: {factsOk(F, grammar, input, target) == True{} : Bool}
  {rootGood(W.rootFor(g, grammar, target, base, start, List.length(&2, Nat, input), F), grammar, input, target, start) == True{} : Bool}

def root_ok(g, grammar, input, target, F, base, start, hg, hF):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      or_else_ok(W.rootPick(Nat.is_eq(lhs, start), grammar, target, base, List.length(&2, Core.Sym, rhs), List.length(&2, Nat, input), F), grammar, input, target, start, W.rootFor(rest, grammar, target, 1n+base, start, List.length(&2, Nat, input), F),
        root_pick_ok(Nat.is_eq(lhs, start), grammar, input, target, F, base, lhs, rhs, rest, start, hg, {==}, hF),
        root_ok(rest, grammar, input, target, F, 1n+base, start, G.drop_step(base, grammar, lhs, rhs, rest, hg), hF))

# WITNESS SOUNDNESS: whatever the witness search hands out for a target is one parse tree of
# the input that contains the target.
law witness_good:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +target: Core.Bsr
  {rootGood(W.witnessFor(fuel, grammar, start, input, ps, target), grammar, input, target, start) == True{} : Bool}

def witness_good(fuel, grammar, start, input, ps, target):
  +F = W.fixpoint(fuel, ps, grammar, input, target, [])
  root_ok(grammar, grammar, input, target, F, 0n, start, {==}, fix_ok(fuel, ps, grammar, input, target, [], {==}))

# ======== THE COVER LOOP ========

# Every target of the list gets a witness.
def allFound(todo: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>) -> Bool:
  match todo:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(WC.isTrees(W.witnessFor(fuel, grammar, start, input, ps, e)), allFound(rest, fuel, grammar, start, input, ps))

def trees_got(fs: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +e: Core.Bsr, +ws: +List<Core.Tree>,
  +hT: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool},
  +hg: {treesGood(fs, grammar, input, e, start) == True{} : Bool})
  -> {Bool.and(Exact.allTreesOk(W.addWitness(Some{fs}, ws), grammar, start, input), W.coveredBy(e, W.addWitness(Some{fs}, ws))) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Bool.and(Exact.allTreesOk(ws, grammar, start, input), W.coveredBy(e, ws)) == True{} : Bool}, Lemma.false_is_not_true(hg))
    case Con{+t, Nil{}}:
      +ok = {Exact.treeOk(grammar, start, input, t) : Bool}
      +mt = {Core.member(e, Core.steps([t], 0n)) : Bool}
      Lemma.and_true_intro(Exact.allTreesOk(t <> ws, grammar, start, input), W.coveredBy(e, t <> ws),
        Lemma.and_true_intro(ok, Exact.allTreesOk(ws, grammar, start, input), Lemma.and_true_left(ok, mt, hg), hT),
        Lemma.or_true_left_intro(mt, W.coveredBy(e, ws), Lemma.and_true_right_side(ok, mt, hg)))
    case Con{+t, Con{+t2, +more}}:
      Empty.absurd({Bool.and(Exact.allTreesOk(ws, grammar, start, input), W.coveredBy(e, ws)) == True{} : Bool}, Lemma.false_is_not_true(hg))

def witness_got(m: Maybe<&2, +List<Core.Tree>>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +e: Core.Bsr, +ws: +List<Core.Tree>,
  +hT: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool},
  +hg: {rootGood(m, grammar, input, e, start) == True{} : Bool}, +hi: {WC.isTrees(m) == True{} : Bool})
  -> {Bool.and(Exact.allTreesOk(W.addWitness(m, ws), grammar, start, input), W.coveredBy(e, W.addWitness(m, ws))) == True{} : Bool}:
  match m:
    case Some{+fs}:
      trees_got(fs, grammar, start, input, e, ws, hT, hg)
    case None{}:
      Empty.absurd({Bool.and(Exact.allTreesOk(ws, grammar, start, input), W.coveredBy(e, ws)) == True{} : Bool}, Lemma.false_is_not_true(hi))

def pick_cov(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +e: Core.Bsr, +ws: +List<Core.Tree>,
  +eb: {W.coveredBy(e, ws) == b : Bool},
  +hT: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}, +hi: {WC.isTrees(W.witnessFor(fuel, grammar, start, input, ps, e)) == True{} : Bool})
  -> {Bool.and(Exact.allTreesOk(W.coverPick(b, fuel, grammar, start, input, ps, e, ws), grammar, start, input), W.coveredBy(e, W.coverPick(b, fuel, grammar, start, input, ps, e, ws))) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.and_true_intro(Exact.allTreesOk(ws, grammar, start, input), W.coveredBy(e, ws), hT, eb)
    case False{}:
      witness_got(W.witnessFor(fuel, grammar, start, input, ps, e), grammar, start, input, e, ws, hT, witness_good(fuel, grammar, start, input, ps, e), hi)

def covered_trees(+x: Core.Bsr, fs: +List<Core.Tree>, +ws: +List<Core.Tree>, +h: {W.coveredBy(x, ws) == True{} : Bool})
  -> {W.coveredBy(x, W.addWitness(Some{fs}, ws)) == True{} : Bool}:
  match fs:
    case Nil{}:
      h
    case Con{+t, Nil{}}:
      Lemma.or_true_right_intro(Core.member(x, Core.steps([t], 0n)), W.coveredBy(x, ws), h)
    case Con{+t, Con{+t2, +more}}:
      h

law covered_more:
  for +x: Core.Bsr
  for m: Maybe<&2, +List<Core.Tree>>
  for +ws: +List<Core.Tree>
  for +h: {W.coveredBy(x, ws) == True{} : Bool}
  {W.coveredBy(x, W.addWitness(m, ws)) == True{} : Bool}

def covered_more(x, m, ws, h):
  match m:
    case Some{+fs}:
      covered_trees(x, fs, ws, h)
    case None{}:
      h

def pick_more(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +e: Core.Bsr, +ws: +List<Core.Tree>, +x: Core.Bsr, +h: {W.coveredBy(x, ws) == True{} : Bool})
  -> {W.coveredBy(x, W.coverPick(b, fuel, grammar, start, input, ps, e, ws)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      covered_more(x, W.witnessFor(fuel, grammar, start, input, ps, e), ws, h)

# The cover loop keeps what it covers.
law cover_mono:
  for todo: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +x: Core.Bsr
  for +h: {W.coveredBy(x, ws) == True{} : Bool}
  {W.coveredBy(x, W.cover(todo, fuel, grammar, start, input, ps, ws)) == True{} : Bool}

def cover_mono(todo, fuel, grammar, start, input, ps, ws, x, h):
  match todo:
    case Nil{}:
      h
    case Con{+e, +rest}:
      cover_mono(rest, fuel, grammar, start, input, ps, W.coverPick(W.coveredBy(e, ws), fuel, grammar, start, input, ps, e, ws), x,
        pick_more(W.coveredBy(e, ws), fuel, grammar, start, input, ps, e, ws, x, h))

def cover_join(+e: Core.Bsr, +rest: +List<Core.Bsr>, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +ps: +List<Core.Bsr>, +ws1: +List<Core.Tree>,
  +h1: {Bool.and(Exact.allTreesOk(ws1, grammar, start, input), W.coveredBy(e, ws1)) == True{} : Bool},
  later: {Exact.allTreesOk(ws1, grammar, start, input) == True{} : Bool} -> {Bool.and(Exact.allTreesOk(W.cover(rest, fuel, grammar, start, input, ps, ws1), grammar, start, input), Exact.allCovered(rest, W.cover(rest, fuel, grammar, start, input, ps, ws1))) == True{} : Bool})
  -> {Bool.and(Exact.allTreesOk(W.cover(rest, fuel, grammar, start, input, ps, ws1), grammar, start, input), Exact.allCovered(e <> rest, W.cover(rest, fuel, grammar, start, input, ps, ws1))) == True{} : Bool}:
  +a = {Exact.allTreesOk(ws1, grammar, start, input) : Bool}
  +r = later(Lemma.and_true_left(a, W.coveredBy(e, ws1), h1))
  +t = {Exact.allTreesOk(W.cover(rest, fuel, grammar, start, input, ps, ws1), grammar, start, input) : Bool}
  +c = {Exact.allCovered(rest, W.cover(rest, fuel, grammar, start, input, ps, ws1)) : Bool}
  Lemma.and_true_intro(t, Exact.allCovered(e <> rest, W.cover(rest, fuel, grammar, start, input, ps, ws1)), Lemma.and_true_left(t, c, r),
    Lemma.and_true_intro(W.coveredBy(e, W.cover(rest, fuel, grammar, start, input, ps, ws1)), c, cover_mono(rest, fuel, grammar, start, input, ps, ws1, e, Lemma.and_true_right_side(a, W.coveredBy(e, ws1), h1)), Lemma.and_true_right_side(t, c, r)))

# With a witness for every target, the cover loop ends with sound trees that cover them all.
law cover_ok:
  for todo: +List<Core.Bsr>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +ws: +List<Core.Tree>
  for +hT: {Exact.allTreesOk(ws, grammar, start, input) == True{} : Bool}
  for +hF: {allFound(todo, fuel, grammar, start, input, ps) == True{} : Bool}
  {Bool.and(Exact.allTreesOk(W.cover(todo, fuel, grammar, start, input, ps, ws), grammar, start, input), Exact.allCovered(todo, W.cover(todo, fuel, grammar, start, input, ps, ws))) == True{} : Bool}

def cover_ok(todo, fuel, grammar, start, input, ps, ws, hT, hF):
  match todo:
    case Nil{}:
      Lemma.and_true_intro(Exact.allTreesOk(ws, grammar, start, input), True{}, hT, {==})
    case Con{+e, +rest}:
      +fe = {WC.isTrees(W.witnessFor(fuel, grammar, start, input, ps, e)) : Bool}
      +b = W.coveredBy(e, ws)
      +ws1 = W.coverPick(b, fuel, grammar, start, input, ps, e, ws)
      cover_join(e, rest, fuel, grammar, start, input, ps, ws1,
        pick_cov(b, fuel, grammar, start, input, ps, e, ws, {==}, hT, Lemma.and_true_left(fe, allFound(rest, fuel, grammar, start, input, ps), hF)),
        h2 => cover_ok(rest, fuel, grammar, start, input, ps, ws1, h2, Lemma.and_true_right_side(fe, allFound(rest, fuel, grammar, start, input, ps), hF)))

def exact_pick(b: Bool, +ps: +List<Core.Bsr>, +h: {b == True{} : Bool}) -> {N.isSteps(Exact.exactPick(b, ps)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

# THE EXACT PARSER ANSWERS once every kept step has a witness.
law exact_from_answers:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +hF: {allFound(ps, fuel, grammar, start, input, ps) == True{} : Bool}
  {N.isSteps(Exact.exactFrom(Some{ps}, fuel, grammar, start, input)) == True{} : Bool}

def exact_from_answers(fuel, grammar, start, input, ps, hF):
  +ws = W.witnesses(fuel, grammar, start, input, ps)
  exact_pick(Bool.and(Exact.allTreesOk(ws, grammar, start, input), Exact.allCovered(ps, ws)), ps, cover_ok(ps, fuel, grammar, start, input, ps, [], {==}, hF))

