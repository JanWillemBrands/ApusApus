import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./LL1.bend as LL
import ./PROOF_PRUNE.bend as P
import ./PROOF_DECIDE.bend as D

# AN LL(1) GRAMMAR IS UNAMBIGUOUS, AND LL(1) AT A NONTERMINAL DECIDES IT. Two forests
# reading the same items from the same position are equal, or somewhere two different
# productions of one nonterminal both predict the token there. The comparison does not use
# LL(1); the laws use it once, on the clash.

# ======== THE COMPARISON: EQUAL, OR A CLASH ========

def Clash(+grammar: +List<Core.Production>, +start: Nat) -> Type:
  &q1: Nat -> &q2: Nat -> &x: Nat -> &next: Maybe<&2, Nat> ->
    {Nat.is_eq(q1, q2) == False{} : Bool} & {Core.lhsIs(grammar, q1, x) == True{} : Bool} & {Core.lhsIs(grammar, q2, x) == True{} : Bool} &
    LL.Predicts(grammar, start, q1, next) & LL.Predicts(grammar, start, q2, next)

def Same(+grammar: +List<Core.Production>, +start: Nat, f1: +List<Core.Tree>, f2: +List<Core.Tree>) -> Type:
  Either<{f1 == f2 : +List<Core.Tree>}, Clash(grammar, start)>

# ======== SMALL FACTS ========

def headOr(xs: +List<Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{x, rest}:
      x

law cons_head:
  for +a: Nat
  for +t: Nat
  for +l1: +List<Nat>
  for +l2: +List<Nat>
  for e: {a <> l1 == t <> l2 : +List<Nat>}
  {a == t : Nat}

def cons_head(a, t, l1, l2, e):
  Equal.cong(+List<Nat>, Nat, v => headOr(v, a), a <> l1, t <> l2, e)

law cons_not_nil:
  for +t: Nat
  for +r: +List<Nat>
  for e: {t <> r == [] : +List<Nat>}
  Empty

def cons_not_nil(t, r, e):
  Lemma.false_is_not_true(Equal.cong(+List<Nat>, Bool, v => List.is_empty(&2, Nat, v), t <> r, [], e))

law append_nil_left:
  for x: +List<Nat>
  for +y: +List<Nat>
  for e: {List.append(&2, Nat, x, y) == [] : +List<Nat>}
  {x == [] : +List<Nat>}

def append_nil_left(x, y, e):
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Empty.absurd({h <> t == [] : +List<Nat>}, cons_not_nil(h, List.append(&2, Nat, t, y), e))

law append_nil_right:
  for x: +List<Nat>
  for +y: +List<Nat>
  for e: {List.append(&2, Nat, x, y) == [] : +List<Nat>}
  {y == [] : +List<Nat>}

def append_nil_right(x, y, e):
  match x:
    case Nil{}:
      e
    case Con{+h, +t}:
      Empty.absurd({y == [] : +List<Nat>}, cons_not_nil(h, List.append(&2, Nat, t, y), e))

law tok_is_some:
  for m: Maybe<&2, Nat>
  for +a: Nat
  for e: {Core.tokIs(m, a) == True{} : Bool}
  {m == Some{a} : Maybe<&2, Nat>}

def tok_is_some(m, a, e):
  match m:
    case None{}:
      Empty.absurd({None{} == Some{a} : Maybe<&2, Nat>}, Lemma.false_is_not_true(e))
    case Some{+x}:
      Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, x, a, Lemma.nat_eq_sound(x, a, e))

law decide:
  for b: Bool
  for +c1: Nat
  for +c2: Nat
  for +bEq: {Nat.is_eq(c1, c2) == b : Bool}
  Either<{c1 == c2 : Nat}, {Nat.is_eq(c1, c2) == False{} : Bool}>

def decide(b, c1, c2, bEq):
  match b:
    case True{}:
      Inl{Lemma.nat_eq_sound(c1, c2, bEq)}
    case False{}:
      Inr{bEq}

law width_zero:
  for +q: Nat
  for +ch: +List<Core.Tree>
  for +k: Nat
  for +e: {Core.leaves(ch) == [] : +List<Nat>}
  {Nat.add(k, Core.width(Core.Node{q, ch})) == k : Nat}

def width_zero(q, ch, k, e):
  Equal.trans(Nat, Nat.add(k, Core.width(Core.Node{q, ch})), Nat.add(k, 0n), k,
    Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, v, []))), Core.leaves(ch), [], e),
    Lemma.add_zero_right(k))

# ======== THE LAST STEP OF A NODE THAT READS NOTHING ========

law own_end_in:
  for rest: +List<Core.Tree>
  for t: Core.Tree
  for +q: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +set: +List<Core.Bsr>
  for +e: {Core.leaves(t <> rest) == [] : +List<Nat>}
  for h: {Core.allIn(Core.own(q, t <> rest, dot, i, k), set) == True{} : Bool}
  {Core.member(Core.Bsr{q, Nat.add(dot, List.length(&2, Core.Tree, t <> rest)), i, k, k}, set) == True{} : Bool}

def own_end_in(rest, t, q, dot, i, k, set, e, h):
  match rest t:
    case +rs Core.Leaf{+a}:
      Empty.absurd({Core.member(Core.Bsr{q, Nat.add(dot, List.length(&2, Core.Tree, Core.Leaf{a} <> rs)), i, k, k}, set) == True{} : Bool}, cons_not_nil(a, Core.leaves(rs), e))
    case Nil{} Core.Node{+q2, +ch2}:
      +lz = append_nil_left(Core.leaves(ch2), [], e)
      +kz = width_zero(q2, ch2, k, lz)
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch2})) : Nat}
      +m = Lemma.and_true_left(Core.member(Core.Bsr{q, 1n+dot, i, k, far}, set), True{}, h)
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {Core.member(Core.Bsr{q, _, i, k, k}, set) == True{} : Bool}
      %kz : {Core.member(Core.Bsr{q, 1n+dot, i, k, _}, set) == True{} : Bool}
      m
    case Con{+t2, +rest2} Core.Node{+q2, +ch2}:
      +lz = append_nil_left(Core.leaves(ch2), Core.leaves(t2 <> rest2), e)
      +e2 = append_nil_right(Core.leaves(ch2), Core.leaves(t2 <> rest2), e)
      +kz = width_zero(q2, ch2, k, lz)
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch2})) : Nat}
      +len = {List.length(&2, Core.Tree, t2 <> rest2) : Nat}
      +tail = Lemma.and_true_right_side(Core.member(Core.Bsr{q, 1n+dot, i, k, far}, set), Core.allIn(Core.own(q, t2 <> rest2, 1n+dot, i, far), set), h)
      %Equal.sym(Nat, Nat.add(dot, 1n+len), 1n+Nat.add(dot, len), Lemma.add_succ_right(dot, len)) : {Core.member(Core.Bsr{q, _, i, k, k}, set) == True{} : Bool}
      %kz : {Core.member(Core.Bsr{q, 1n+Nat.add(dot, len), i, _, _}, set) == True{} : Bool}
      own_end_in(rest2, t2, q, 1n+dot, i, far, set, e2, tail)

law own_end:
  for ch: +List<Core.Tree>
  for +q: Nat
  for +k: Nat
  for +set: +List<Core.Bsr>
  for +e: {Core.leaves(ch) == [] : +List<Nat>}
  for h: {Core.allIn(Core.own(q, ch, 0n, k, k), set) == True{} : Bool}
  {Core.member(Core.Bsr{q, List.length(&2, Core.Tree, ch), k, k, k}, set) == True{} : Bool}

def own_end(ch, q, k, set, e, h):
  match ch:
    case Nil{}:
      Lemma.and_true_left(Core.member(Core.Bsr{q, 0n, k, k, k}, set), True{}, h)
    case Con{+t, +rest}:
      own_end_in(rest, t, q, 0n, k, k, set, e, h)

# ======== THE FIRST TOKEN ========

# A node whose children start with t2: through its children, or, when they read nothing,
# through what follows.
def node_head(w: +List<Nat>, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +q: Nat, +input: +List<Nat>, +k: Nat, +t: Nat, +rest: +List<Nat>,
  +ew: {Core.leaves(ch) == w : +List<Nat>},
  +e: {List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)) == t <> rest : +List<Nat>},
  recCh: @t2: Nat -> @r2: +List<Nat> -> {Core.leaves(ch) == t2 <> r2 : +List<Nat>} -> {Core.tokAt(input, k) == Some{t2} : Maybe<&2, Nat>},
  recTs: {Core.leaves(ts) == t <> rest : +List<Nat>} -> {Core.tokAt(input, Nat.add(k, Core.width(Core.Node{q, ch}))) == Some{t} : Maybe<&2, Nat>})
  -> {Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}:
  match w:
    case Nil{}:
      +e2 = Equal.trans(+List<Nat>, Core.leaves(ts), List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)), t <> rest,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Core.leaves(ts)), [], Core.leaves(ch), Equal.sym(+List<Nat>, Core.leaves(ch), [], ew)), e)
      %width_zero(q, ch, k, ew) : {Core.tokAt(input, _) == Some{t} : Maybe<&2, Nat>}
      recTs(e2)
    case Con{+t2, +r2}:
      +e2 = Equal.trans(+List<Nat>, t2 <> List.append(&2, Nat, r2, Core.leaves(ts)), List.append(&2, Nat, Core.leaves(ch), Core.leaves(ts)), t <> rest,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Core.leaves(ts)), t2 <> r2, Core.leaves(ch), Equal.sym(+List<Nat>, Core.leaves(ch), t2 <> r2, ew)), e)
      Equal.trans(Maybe<&2, Nat>, Core.tokAt(input, k), Some{t2}, Some{t}, recCh(t2, r2, ew),
        Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, t2, t, cons_head(t2, t, List.append(&2, Nat, r2, Core.leaves(ts)), rest, e2)))

law reads_head:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +t: Nat
  for +rest: +List<Nat>
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +e: {Core.leaves(f) == t <> rest : +List<Nat>}
  {Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}

def reads_head(f, items, grammar, input, k, t, rest, r, e):
  match f items:
    case Nil{} +its:
      Empty.absurd({Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, cons_not_nil(t, rest, Equal.sym(+List<Nat>, [], t <> rest, e)))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+s}, +rs}:
      +rest1 = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rs, input, 1n+k)) : Bool}
      +tok = tok_is_some(Core.tokAt(input, k), a, Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rs, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, s), rest1, r)))
      Equal.trans(Maybe<&2, Nat>, Core.tokAt(input, k), Some{a}, Some{t}, tok, Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, a, t, cons_head(a, t, Core.leaves(ts), rest, e)))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rs}:
      Empty.absurd({Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rs}:
      +head = {Bool.and(Core.lhsIs(grammar, q, x), Core.needOk(need, Core.width(Core.Node{q, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)) : Bool}
      +far = {Nat.add(k, Core.width(Core.Node{q, ch})) : Nat}
      +after = {Core.reads(ts, grammar, rs, input, far) : Bool}
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), Lemma.and_true_left(own, after, r))
      +rt = Lemma.and_true_right_side(own, after, r)
      node_head(Core.leaves(ch), ch, ts, q, input, k, t, rest, {==}, e,
        t2 => r2 => h => reads_head(ch, Core.rhsOf(grammar, q), grammar, input, k, t2, r2, rc, h),
        h => reads_head(ts, rs, grammar, input, far, t, rest, rt, h))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+s}, +rs}:
      Empty.absurd({Core.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))

# ======== WHAT A NODE PREDICTS ========

law all_in_cons:
  for xs: +List<Core.Bsr>
  for +y: Core.Bsr
  for +set: +List<Core.Bsr>
  for h: {Core.allIn(xs, set) == True{} : Bool}
  {Core.allIn(xs, y <> set) == True{} : Bool}

def all_in_cons(xs, y, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = h
      Lemma.and_true_intro(Bool.or(Core.bsrEq(x, y), Core.member(x, set)), Core.allIn(rest, y <> set),
        Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, set), Lemma.and_true_left(Core.member(x, set), Core.allIn(rest, set), both)),
        all_in_cons(rest, y, set, Lemma.and_true_right_side(Core.member(x, set), Core.allIn(rest, set), both)))

law all_in_refl:
  for xs: +List<Core.Bsr>
  {Core.allIn(xs, xs) == True{} : Bool}

def all_in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(Core.bsrEq(x, x), Core.member(x, rest)), Core.allIn(rest, x <> rest),
        Lemma.or_true_left_intro(Core.bsrEq(x, x), Core.member(x, rest), D.bsr_eq_refl(x)),
        all_in_cons(rest, x, rest, all_in_refl(rest)))

# The last step of a node of q that reads nothing is a step of the tree.
law end_step:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ch: +List<Core.Tree>
  for +k: Nat
  for +set: +List<Core.Bsr>
  for +e: {Core.leaves(ch) == [] : +List<Nat>}
  for +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k) == True{} : Bool}
  for io: {Core.allIn(Core.own(q, ch, 0n, k, k), set) == True{} : Bool}
  {Core.member(Core.Bsr{q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), k, k, k}, set) == True{} : Bool}

def end_step(grammar, input, q, ch, k, set, e, rc, io):
  %P.reads_length(ch, Core.rhsOf(grammar, q), grammar, input, k, rc) : {Core.member(Core.Bsr{q, _, k, k, k}, set) == True{} : Bool}
  own_end(ch, q, k, set, e, io)

# A node of q at k predicts the token at k: by its first token, or it reads nothing and
# the tree itself shows that token after q.
def predicts_node(w: +List<Nat>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +root: Core.Tree,
  +rr: {Core.reads([root], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([root])) == List.length(&2, Nat, input) : Nat},
  +q: Nat, +ch: +List<Core.Tree>, +k: Nat,
  +ew: {Core.leaves(ch) == w : +List<Nat>},
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, ch, 0n, k, k), Core.steps([root], 0n)) == True{} : Bool})
  -> LL.Predicts(grammar, start, q, Core.tokAt(input, k)):
  match w:
    case Nil{}:
      +fit = D.reads_fits(ch, Core.rhsOf(grammar, q), grammar, input, k, rc)
      Inr{((ch, (fit, ew)), (input, (root, (k, (k, (k, ((rr, rl), (end_step(grammar, input, q, ch, k, Core.steps([root], 0n), ew, rc, io), {==}))))))))}
    case Con{+t, +r}:
      +fit = D.reads_fits(ch, Core.rhsOf(grammar, q), grammar, input, k, rc)
      Inl{(ch, (t, (r, (fit, (ew, reads_head(ch, Core.rhsOf(grammar, q), grammar, input, k, t, r, rc, ew))))))}

# ======== COMPARING TWO FORESTS ========

def then_same(+grammar: +List<Core.Production>, +start: Nat, -t1: +List<Core.Tree>, -t2: +List<Core.Tree>, -f1: +List<Core.Tree>, -f2: +List<Core.Tree>,
  r: Same(grammar, start, t1, t2), mk: {t1 == t2 : +List<Core.Tree>} -> {f1 == f2 : +List<Core.Tree>}) -> Same(grammar, start, f1, f2):
  match r:
    case Inl{e}:
      Inl{mk(e)}
    case Inr{c}:
      Inr{c}

law leaf_eq:
  for +a: Nat
  for +b: Nat
  for +t: Nat
  for +ts1: +List<Core.Tree>
  for +ts2: +List<Core.Tree>
  for +ae: {a == t : Nat}
  for +be: {b == t : Nat}
  for +te: {ts1 == ts2 : +List<Core.Tree>}
  {Core.Leaf{a} <> ts1 == Core.Leaf{b} <> ts2 : +List<Core.Tree>}

def leaf_eq(a, b, t, ts1, ts2, ae, be, te):
  Equal.trans(+List<Core.Tree>, Core.Leaf{a} <> ts1, Core.Leaf{t} <> ts1, Core.Leaf{b} <> ts2, Equal.cong(Nat, +List<Core.Tree>, v => Core.Leaf{v} <> ts1, a, t, ae),
    Equal.trans(+List<Core.Tree>, Core.Leaf{t} <> ts1, Core.Leaf{b} <> ts1, Core.Leaf{b} <> ts2, Equal.cong(Nat, +List<Core.Tree>, v => Core.Leaf{v} <> ts1, t, b, Equal.sym(Nat, b, t, be)),
      Equal.cong(+List<Core.Tree>, +List<Core.Tree>, v => Core.Leaf{b} <> v, ts1, ts2, te)))

law node_eq:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<Core.Tree>
  for +ch2: +List<Core.Tree>
  for +ts1: +List<Core.Tree>
  for +ts2: +List<Core.Tree>
  for +qe: {q1 == q2 : Nat}
  for +ce: {ch1 == ch2 : +List<Core.Tree>}
  for +te: {ts1 == ts2 : +List<Core.Tree>}
  {Core.Node{q1, ch1} <> ts1 == Core.Node{q2, ch2} <> ts2 : +List<Core.Tree>}

def node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, ce, te):
  Equal.trans(+List<Core.Tree>, Core.Node{q1, ch1} <> ts1, Core.Node{q2, ch1} <> ts1, Core.Node{q2, ch2} <> ts2, Equal.cong(Nat, +List<Core.Tree>, v => Core.Node{v, ch1} <> ts1, q1, q2, qe),
    Equal.trans(+List<Core.Tree>, Core.Node{q2, ch1} <> ts1, Core.Node{q2, ch2} <> ts1, Core.Node{q2, ch2} <> ts2, Equal.cong(+List<Core.Tree>, +List<Core.Tree>, v => Core.Node{q2, v} <> ts1, ch1, ch2, ce),
      Equal.cong(+List<Core.Tree>, +List<Core.Tree>, v => Core.Node{q2, ch2} <> v, ts1, ts2, te)))

# The second tree's facts, moved to the first tree's production and children once they are equal.
law children_reads:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +ch2: +List<Core.Tree>
  for +k: Nat
  for +qe: {q1 == q2 : Nat}
  for +h: {Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool}
  {Core.reads(ch2, grammar, Core.rhsOf(grammar, q1), input, k) == True{} : Bool}

def children_reads(grammar, input, q1, q2, ch2, k, qe, h):
  %Equal.sym(Nat, q1, q2, qe) : {Core.reads(ch2, grammar, Core.rhsOf(grammar, _), input, k) == True{} : Bool}
  h

law rest_reads:
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<Core.Tree>
  for +ch2: +List<Core.Tree>
  for +ts2: +List<Core.Tree>
  for +rest: +List<Core.Sym>
  for +k: Nat
  for +ce: {ch1 == ch2 : +List<Core.Tree>}
  for +h: {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q2, ch2}))) == True{} : Bool}
  {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q1, ch1}))) == True{} : Bool}

def rest_reads(grammar, input, q1, q2, ch1, ch2, ts2, rest, k, ce, h):
  %Equal.sym(+List<Core.Tree>, ch1, ch2, ce) : {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q1, _}))) == True{} : Bool}
  h

law rest_in:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<Core.Tree>
  for +ch2: +List<Core.Tree>
  for +ts2: +List<Core.Tree>
  for +k: Nat
  for +set: +List<Core.Bsr>
  for +ce: {ch1 == ch2 : +List<Core.Tree>}
  for +h: {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q2, ch2}))), set) == True{} : Bool}
  {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q1, ch1}))), set) == True{} : Bool}

def rest_in(q1, q2, ch1, ch2, ts2, k, set, ce, h):
  %Equal.sym(+List<Core.Tree>, ch1, ch2, ce) : {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q1, _}))), set) == True{} : Bool}
  h

# Equal children: go on with the rest of both sequences.
def children_then(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +root2: Core.Tree,
  +q1: Nat, +q2: Nat, +ch1: +List<Core.Tree>, +ch2: +List<Core.Tree>, +ts1: +List<Core.Tree>, +ts2: +List<Core.Tree>, +rest: +List<Core.Sym>, +k: Nat,
  +qe: {q1 == q2 : Nat},
  +rt2: {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q2, ch2}))) == True{} : Bool},
  +it2: {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q2, ch2}))), Core.steps([root2], 0n)) == True{} : Bool},
  rch: Same(grammar, start, ch1, ch2),
  recTs: {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q1, ch1}))) == True{} : Bool} -> {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q1, ch1}))), Core.steps([root2], 0n)) == True{} : Bool} -> Same(grammar, start, ts1, ts2))
  -> Same(grammar, start, Core.Node{q1, ch1} <> ts1, Core.Node{q2, ch2} <> ts2):
  match rch:
    case Inl{+ce}:
      then_same(grammar, start, ts1, ts2, Core.Node{q1, ch1} <> ts1, Core.Node{q2, ch2} <> ts2,
        recTs(rest_reads(grammar, input, q1, q2, ch1, ch2, ts2, rest, k, ce, rt2), rest_in(q1, q2, ch1, ch2, ts2, k, Core.steps([root2], 0n), ce, it2)),
        te => node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, ce, te))
    case Inr{c}:
      Inr{c}

# Two nodes of x at k: the same production, or a clash.
def node_case(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +root1: Core.Tree, +root2: Core.Tree,
  +rr1: {Core.reads([root1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl1: {List.length(&2, Nat, Core.leaves([root1])) == List.length(&2, Nat, input) : Nat},
  +rr2: {Core.reads([root2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl2: {List.length(&2, Nat, Core.leaves([root2])) == List.length(&2, Nat, input) : Nat},
  +q1: Nat, +q2: Nat, +ch1: +List<Core.Tree>, +ch2: +List<Core.Tree>, +ts1: +List<Core.Tree>, +ts2: +List<Core.Tree>, +x: Nat, +rest: +List<Core.Sym>, +k: Nat,
  dec: Either<{q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}>,
  +lhs1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +lhs2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +rc1: {Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input, k) == True{} : Bool},
  +rc2: {Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool},
  +io1: {Core.allIn(Core.own(q1, ch1, 0n, k, k), Core.steps([root1], 0n)) == True{} : Bool},
  +io2: {Core.allIn(Core.own(q2, ch2, 0n, k, k), Core.steps([root2], 0n)) == True{} : Bool},
  +rt2: {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q2, ch2}))) == True{} : Bool},
  +it2: {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q2, ch2}))), Core.steps([root2], 0n)) == True{} : Bool},
  recCh: {Core.reads(ch2, grammar, Core.rhsOf(grammar, q1), input, k) == True{} : Bool} -> Same(grammar, start, ch1, ch2),
  recTs: {Core.reads(ts2, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q1, ch1}))) == True{} : Bool} -> {Core.allIn(Core.steps(ts2, Nat.add(k, Core.width(Core.Node{q1, ch1}))), Core.steps([root2], 0n)) == True{} : Bool} -> Same(grammar, start, ts1, ts2))
  -> Same(grammar, start, Core.Node{q1, ch1} <> ts1, Core.Node{q2, ch2} <> ts2):
  match dec:
    case Inl{+qe}:
      children_then(grammar, start, input, root2, q1, q2, ch1, ch2, ts1, ts2, rest, k, qe, rt2, it2, recCh(children_reads(grammar, input, q1, q2, ch2, k, qe, rc2)), recTs)
    case Inr{+neq}:
      Inr{(q1, (q2, (x, (Core.tokAt(input, k), (neq, (lhs1, (lhs2,
        (predicts_node(Core.leaves(ch1), grammar, start, input, root1, rr1, rl1, q1, ch1, k, {==}, rc1, io1),
         predicts_node(Core.leaves(ch2), grammar, start, input, root2, rr2, rl2, q2, ch2, k, {==}, rc2, io2)))))))))}

law compare:
  for f1: +List<Core.Tree>
  for f2: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: Core.Tree
  for +root2: Core.Tree
  for +rr1: {Core.reads([root1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, Core.leaves([root1])) == List.length(&2, Nat, input) : Nat}
  for +rr2: {Core.reads([root2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, Core.leaves([root2])) == List.length(&2, Nat, input) : Nat}
  for +k: Nat
  for +r1: {Core.reads(f1, grammar, items, input, k) == True{} : Bool}
  for +r2: {Core.reads(f2, grammar, items, input, k) == True{} : Bool}
  for +in1: {Core.allIn(Core.steps(f1, k), Core.steps([root1], 0n)) == True{} : Bool}
  for +in2: {Core.allIn(Core.steps(f2, k), Core.steps([root2], 0n)) == True{} : Bool}
  Same(grammar, start, f1, f2)

def compare(f1, f2, items, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, k, r1, r2, in1, in2):
  match f1 f2 items:
    case Nil{} Nil{} Nil{}:
      Inl{{==}}
    case Nil{} Con{Core.Leaf{+b}, +ts2} Nil{}:
      Empty.absurd(Same(grammar, start, [], Core.Leaf{b} <> ts2), Lemma.false_is_not_true(r2))
    case Nil{} Con{Core.Node{+q2, +ch2}, +ts2} Nil{}:
      Empty.absurd(Same(grammar, start, [], Core.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(r2))
    case Nil{} +g2 Con{+s, +rest}:
      Empty.absurd(Same(grammar, start, [], g2), Lemma.false_is_not_true(r1))
    case Con{Core.Leaf{+a}, +ts1} +g2 Nil{}:
      Empty.absurd(Same(grammar, start, Core.Leaf{a} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{Core.Leaf{+a}, +ts1} +g2 Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Leaf{a} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{Core.Leaf{+a}, +ts1} Nil{} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Leaf{a} <> ts1, []), Lemma.false_is_not_true(r2))
    case Con{Core.Leaf{+a}, +ts1} Con{Core.Node{+q2, +ch2}, +ts2} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Leaf{a} <> ts1, Core.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(r2))
    case Con{Core.Leaf{+a}, +ts1} Con{Core.Leaf{+b}, +ts2} Con{Core.Terminal{+t}, +rest}:
      +more1 = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts1, grammar, rest, input, 1n+k)) : Bool}
      +more2 = {Bool.and(Core.tokIs(Core.tokAt(input, k), b), Core.reads(ts2, grammar, rest, input, 1n+k)) : Bool}
      +ae = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more1, r1))
      +be = Lemma.nat_eq_sound(b, t, Lemma.and_true_left(Nat.is_eq(b, t), more2, r2))
      +rt1 = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts1, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more1, r1))
      +rt2 = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), b), Core.reads(ts2, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(b, t), more2, r2))
      then_same(grammar, start, ts1, ts2, Core.Leaf{a} <> ts1, Core.Leaf{b} <> ts2,
        compare(ts1, ts2, rest, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, 1n+k, rt1, rt2, in1, in2),
        te => leaf_eq(a, b, t, ts1, ts2, ae, be, te))
    case Con{Core.Node{+q1, +ch1}, +ts1} +g2 Nil{}:
      Empty.absurd(Same(grammar, start, Core.Node{q1, ch1} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{Core.Node{+q1, +ch1}, +ts1} +g2 Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Node{q1, ch1} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{Core.Node{+q1, +ch1}, +ts1} Nil{} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(r2))
    case Con{Core.Node{+q1, +ch1}, +ts1} Con{Core.Leaf{+b}, +ts2} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd(Same(grammar, start, Core.Node{q1, ch1} <> ts1, Core.Leaf{b} <> ts2), Lemma.false_is_not_true(r2))
    case Con{Core.Node{+q1, +ch1}, +ts1} Con{Core.Node{+q2, +ch2}, +ts2} Con{Core.Nonterminal{+x, +need}, +rest}:
      +S1 = {Core.steps([root1], 0n) : +List<Core.Bsr>}
      +S2 = {Core.steps([root2], 0n) : +List<Core.Bsr>}
      +far1 = {Nat.add(k, Core.width(Core.Node{q1, ch1})) : Nat}
      +far2 = {Nat.add(k, Core.width(Core.Node{q2, ch2})) : Nat}
      +head1 = {Bool.and(Core.lhsIs(grammar, q1, x), Core.needOk(need, Core.width(Core.Node{q1, ch1}))) : Bool}
      +own1 = {Bool.and(head1, Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input, k)) : Bool}
      +head2 = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch2}))) : Bool}
      +own2 = {Bool.and(head2, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +left1 = Lemma.and_true_left(own1, Core.reads(ts1, grammar, rest, input, far1), r1)
      +left2 = Lemma.and_true_left(own2, Core.reads(ts2, grammar, rest, input, far2), r2)
      +lhs1 = Lemma.and_true_left(Core.lhsIs(grammar, q1, x), Core.needOk(need, Core.width(Core.Node{q1, ch1})), Lemma.and_true_left(head1, Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input, k), left1))
      +lhs2 = Lemma.and_true_left(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch2})), Lemma.and_true_left(head2, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, k), left2))
      +rc1 = Lemma.and_true_right_side(head1, Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input, k), left1)
      +rc2 = Lemma.and_true_right_side(head2, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, k), left2)
      +rt1 = Lemma.and_true_right_side(own1, Core.reads(ts1, grammar, rest, input, far1), r1)
      +rt2 = Lemma.and_true_right_side(own2, Core.reads(ts2, grammar, rest, input, far2), r2)
      +below1 = P.in_app_right(Core.own(q1, ch1, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch1, k), Core.steps(ts1, far1)), S1, in1)
      +below2 = P.in_app_right(Core.own(q2, ch2, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch2, k), Core.steps(ts2, far2)), S2, in2)
      +io1 = P.in_app_left(Core.own(q1, ch1, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch1, k), Core.steps(ts1, far1)), S1, in1)
      +io2 = P.in_app_left(Core.own(q2, ch2, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch2, k), Core.steps(ts2, far2)), S2, in2)
      +ic1 = P.in_app_left(Core.steps(ch1, k), Core.steps(ts1, far1), S1, below1)
      +ic2 = P.in_app_left(Core.steps(ch2, k), Core.steps(ts2, far2), S2, below2)
      +it1 = P.in_app_right(Core.steps(ch1, k), Core.steps(ts1, far1), S1, below1)
      +it2 = P.in_app_right(Core.steps(ch2, k), Core.steps(ts2, far2), S2, below2)
      node_case(grammar, start, input, root1, root2, rr1, rl1, rr2, rl2,
        q1, q2, ch1, ch2, ts1, ts2, x, rest, k, decide(Nat.is_eq(q1, q2), q1, q2, {==}), lhs1, lhs2, rc1, rc2, io1, io2, rt2, it2,
        h => compare(ch1, ch2, Core.rhsOf(grammar, q1), grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, k, rc1, h, ic1, ic2),
        h => g => compare(ts1, ts2, rest, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, far1, rt1, h, it1, g))

# ======== THE LAW ========

def treeOr(ts: +List<Core.Tree>, +d: Core.Tree) -> Core.Tree:
  match ts:
    case Nil{}:
      d
    case Con{t, rest}:
      t

law no_clash:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +t1: Core.Tree
  for +t2: Core.Tree
  for r: Same(grammar, start, [t1], [t2])
  for ll1: LL.LL1(grammar, start)
  {t1 == t2 : Core.Tree}

def no_clash(grammar, start, t1, t2, r, ll1):
  match r:
    case Inl{e}:
      Equal.cong(+List<Core.Tree>, Core.Tree, v => treeOr(v, t1), [t1], [t2], e)
    case Inr{c}:
      match c:
        case (q1, (q2, (x, (next, (neq, (lhs1, (lhs2, (p1, p2)))))))):
          Empty.absurd({t1 == t2 : Core.Tree}, ll1(x)(q1, q2, next, neq, lhs1, lhs2, p1, p2))

# AN LL(1) GRAMMAR IS UNAMBIGUOUS: two parse trees of the same input are the same tree.
law ll1_unambiguous:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree1: Core.Tree
  for +tree2: Core.Tree
  for ll1: LL.LL1(grammar, start)
  for +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input) : Nat}
  for +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input) : Nat}
  {tree1 == tree2 : Core.Tree}

def ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, rr1, rl1, rr2, rl2):
  no_clash(grammar, start, tree1, tree2,
    compare([tree1], [tree2], [Core.Nonterminal{start, Core.Anything{}}], grammar, start, input, tree1, tree2, rr1, rl1, rr2, rl2, 0n, rr1, rr2,
      all_in_refl(Core.steps([tree1], 0n)), all_in_refl(Core.steps([tree2], 0n))),
    ll1)

# ======== LL(1) AT ONE NONTERMINAL ========

def predicts_cast(+grammar: +List<Core.Production>, +start: Nat, +q: Nat, +n1: Maybe<&2, Nat>, +n2: Maybe<&2, Nat>,
  +e: {n2 == n1 : Maybe<&2, Nat>}, p: LL.Predicts(grammar, start, q, n2)) -> LL.Predicts(grammar, start, q, n1):
  %e : LL.Predicts(grammar, start, q, _)
  p

def at_pick(+grammar: +List<Core.Production>, +start: Nat, +x: Nat, +q1: Nat, +q2: Nat, +next: Maybe<&2, Nat>,
  dec: Either<{q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}>,
  ll1: LL.LL1At(grammar, start, x),
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  p1: LL.Predicts(grammar, start, q1, next),
  p2: LL.Predicts(grammar, start, q2, next)) -> {q1 == q2 : Nat}:
  match dec:
    case Inl{e}:
      e
    case Inr{neq}:
      Empty.absurd({q1 == q2 : Nat}, ll1(q1, q2, next, neq, l1, l2, p1, p2))

def at_nodes(+grammar: +List<Core.Production>, +start: Nat, +input1: +List<Nat>, +input2: +List<Nat>, +tree1: Core.Tree, +tree2: Core.Tree, +x: Nat, +q1: Nat, +q2: Nat, +k: Nat,
  ll1: LL.LL1At(grammar, start, x),
  +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input1, 0n) == True{} : Bool},
  +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input1) : Nat},
  +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input2, 0n) == True{} : Bool},
  +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input2) : Nat},
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +ch1: +List<Core.Tree>, +rc1: {Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input1, k) == True{} : Bool}, +io1: {Core.allIn(Core.own(q1, ch1, 0n, k, k), Core.steps([tree1], 0n)) == True{} : Bool},
  +ch2: +List<Core.Tree>, +rc2: {Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input2, k) == True{} : Bool}, +io2: {Core.allIn(Core.own(q2, ch2, 0n, k, k), Core.steps([tree2], 0n)) == True{} : Bool},
  +same: {Core.tokAt(input1, k) == Core.tokAt(input2, k) : Maybe<&2, Nat>}) -> {q1 == q2 : Nat}:
  p1 = predicts_node(Core.leaves(ch1), grammar, start, input1, tree1, rr1, rl1, q1, ch1, k, {==}, rc1, io1)
  p2 = predicts_node(Core.leaves(ch2), grammar, start, input2, tree2, rr2, rl2, q2, ch2, k, {==}, rc2, io2)
  at_pick(grammar, start, x, q1, q2, Core.tokAt(input1, k), decide(Nat.is_eq(q1, q2), q1, q2, {==}), ll1, l1, l2, p1,
    predicts_cast(grammar, start, q2, Core.tokAt(input1, k), Core.tokAt(input2, k), Equal.sym(Maybe<&2, Nat>, Core.tokAt(input1, k), Core.tokAt(input2, k), same), p2))

def at_second(+grammar: +List<Core.Production>, +start: Nat, +input1: +List<Nat>, +input2: +List<Nat>, +tree1: Core.Tree, +tree2: Core.Tree, +x: Nat, +q1: Nat, +q2: Nat, +k: Nat,
  ll1: LL.LL1At(grammar, start, x),
  +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input1, 0n) == True{} : Bool},
  +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input1) : Nat},
  +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input2, 0n) == True{} : Bool},
  +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input2) : Nat},
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +ch1: +List<Core.Tree>, +rc1: {Core.reads(ch1, grammar, Core.rhsOf(grammar, q1), input1, k) == True{} : Bool}, +io1: {Core.allIn(Core.own(q1, ch1, 0n, k, k), Core.steps([tree1], 0n)) == True{} : Bool},
  n2: LL.NodeAt(grammar, input2, tree2, q2, k),
  +same: {Core.tokAt(input1, k) == Core.tokAt(input2, k) : Maybe<&2, Nat>}) -> {q1 == q2 : Nat}:
  match n2:
    case (ch20, (rc20, io20)):
      at_nodes(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, ch1, rc1, io1, ch20, rc20, io20, same)

def at_first(+grammar: +List<Core.Production>, +start: Nat, +input1: +List<Nat>, +input2: +List<Nat>, +tree1: Core.Tree, +tree2: Core.Tree, +x: Nat, +q1: Nat, +q2: Nat, +k: Nat,
  ll1: LL.LL1At(grammar, start, x),
  +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input1, 0n) == True{} : Bool},
  +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input1) : Nat},
  +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input2, 0n) == True{} : Bool},
  +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input2) : Nat},
  +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool},
  +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  n1: LL.NodeAt(grammar, input1, tree1, q1, k),
  n2: LL.NodeAt(grammar, input2, tree2, q2, k),
  +same: {Core.tokAt(input1, k) == Core.tokAt(input2, k) : Maybe<&2, Nat>}) -> {q1 == q2 : Nat}:
  match n1:
    case (ch10, (rc10, io10)):
      at_second(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, ch10, rc10, io10, n2, same)

# LL(1) AT ONE NONTERMINAL DECIDES IT: where the grammar is LL(1) at x, two parse trees, of
# any inputs, with nodes of x at the same position and the same token next use the same
# production there. So a parser may predict by one token at x, even where the grammar is
# not LL(1) elsewhere.
law ll1_at:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input1: +List<Nat>
  for +input2: +List<Nat>
  for +tree1: Core.Tree
  for +tree2: Core.Tree
  for +x: Nat
  for +q1: Nat
  for +q2: Nat
  for +k: Nat
  for ll1: LL.LL1At(grammar, start, x)
  for +rr1: {Core.reads([tree1], grammar, [Core.Nonterminal{start, Core.Anything{}}], input1, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, Core.leaves([tree1])) == List.length(&2, Nat, input1) : Nat}
  for +rr2: {Core.reads([tree2], grammar, [Core.Nonterminal{start, Core.Anything{}}], input2, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, Core.leaves([tree2])) == List.length(&2, Nat, input2) : Nat}
  for +l1: {Core.lhsIs(grammar, q1, x) == True{} : Bool}
  for +l2: {Core.lhsIs(grammar, q2, x) == True{} : Bool}
  for n1: LL.NodeAt(grammar, input1, tree1, q1, k)
  for n2: LL.NodeAt(grammar, input2, tree2, q2, k)
  for +same: {Core.tokAt(input1, k) == Core.tokAt(input2, k) : Maybe<&2, Nat>}
  {q1 == q2 : Nat}

def ll1_at(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, n1, n2, same):
  at_first(grammar, start, input1, input2, tree1, tree2, x, q1, q2, k, ll1, rr1, rl1, rr2, rl2, l1, l2, n1, n2, same)
