import Base
import /Users/janwillem/Developer/Xcode/ApusApus/Bend/LEMMAS.bend as Lemma
import ./CORE_L0_walk.bend as C

# LL(1) ON THE CORE (measurement draft, not installed): ll1_unambiguous on L0.
#
# On the core every choice point is a nonterminal and every choice a production, so LL(1)
# is the textbook strong LL(1) of a BNF grammar. FOLLOW of a production is read from parse
# trees, as in SPEC.bend: in some parse tree, the production's last step ends at j and the
# token at j is `next`.

# ======== THE MEANING ========

# A parse tree of the input: it reads the input from 0, and all of it.
def ParseTree(+grammar: +List<C.Production>, +start: Nat, +input: +List<Nat>, +tree: C.Tree) -> Type:
  {C.reads([tree], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool} & {List.length(&2, Nat, C.leaves([tree])) == List.length(&2, Nat, input) : Nat}

# The items can read nothing.
def Nullable(+grammar: +List<C.Production>, +items: +List<C.Sym>) -> Type:
  &f: +List<C.Tree> -> {C.fits(f, grammar, items) == True{} : Bool} & {C.leaves(f) == [] : +List<Nat>}

# The items can begin with `next`.
def FirstIs(+grammar: +List<C.Production>, +items: +List<C.Sym>, +next: Maybe<&2, Nat>) -> Type:
  &f: +List<C.Tree> -> &t: Nat -> &r: +List<Nat> ->
    {C.fits(f, grammar, items) == True{} : Bool} & {C.leaves(f) == t <> r : +List<Nat>} & {next == Some{t} : Maybe<&2, Nat>}

# In some parse tree, production q's last step ends at j, and the token at j is `next`.
def FollowIs(+grammar: +List<C.Production>, +start: Nat, +q: Nat, +next: Maybe<&2, Nat>) -> Type:
  &input: +List<Nat> -> &tree: C.Tree -> &i: Nat -> &k: Nat -> &j: Nat ->
    ParseTree(grammar, start, input, tree) &
    {C.member(C.Bsr{q, List.length(&2, C.Sym, C.rhsOf(grammar, q)), i, k, j}, C.steps([tree], 0n)) == True{} : Bool} &
    {C.tokAt(input, j) == next : Maybe<&2, Nat>}

# Production q can begin with `next`: through FIRST, or it reads nothing and FOLLOW has it.
def Predicts(+grammar: +List<C.Production>, +start: Nat, +q: Nat, +next: Maybe<&2, Nat>) -> Type:
  Either<FirstIs(grammar, C.rhsOf(grammar, q), next), Nullable(grammar, C.rhsOf(grammar, q)) & FollowIs(grammar, start, q, next)>

# LL(1): no two productions of one nonterminal can begin with the same next token.
def LL1(+grammar: +List<C.Production>, +start: Nat) -> Type:
  @q1: Nat -> @q2: Nat -> @x: Nat -> @next: Maybe<&2, Nat> ->
    {Nat.is_eq(q1, q2) == False{} : Bool} -> {C.lhsIs(grammar, q1, x) == True{} : Bool} -> {C.lhsIs(grammar, q2, x) == True{} : Bool} ->
    Predicts(grammar, start, q1, next) -> Predicts(grammar, start, q2, next) -> Empty

# ======== THE COMPARISON: EQUAL, OR A CLASH ========
#
# Two forests reading the same items from the same position are equal, or somewhere two
# different productions of one nonterminal both predict the token there. The comparison
# does not use LL(1); the law uses it once, on the clash.

def Clash(+grammar: +List<C.Production>, +start: Nat) -> Type:
  &q1: Nat -> &q2: Nat -> &x: Nat -> &next: Maybe<&2, Nat> ->
    {Nat.is_eq(q1, q2) == False{} : Bool} & {C.lhsIs(grammar, q1, x) == True{} : Bool} & {C.lhsIs(grammar, q2, x) == True{} : Bool} &
    Predicts(grammar, start, q1, next) & Predicts(grammar, start, q2, next)

def Same(+grammar: +List<C.Production>, +start: Nat, f1: +List<C.Tree>, f2: +List<C.Tree>) -> Type:
  Either<{f1 == f2 : +List<C.Tree>}, Clash(grammar, start)>

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
  for e: {C.tokIs(m, a) == True{} : Bool}
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

# ======== WHAT READS GIVES ========

law reads_fits:
  for f: +List<C.Tree>
  for items: +List<C.Sym>
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +r: {C.reads(f, grammar, items, input, k) == True{} : Bool}
  {C.fits(f, grammar, items) == True{} : Bool}

def reads_fits(f, items, grammar, input, k, r):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({C.fits([], grammar, s <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{C.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({C.fits(C.Leaf{a} <> ts, grammar, []) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{C.Leaf{+a}, +ts} Con{C.Terminal{+t}, +rest}:
      +rest1 = {Bool.and(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      Lemma.and_true_intro(Nat.is_eq(a, t), C.fits(ts, grammar, rest), Lemma.and_true_left(Nat.is_eq(a, t), rest1, r),
        reads_fits(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), rest1, r))))
    case Con{C.Leaf{+a}, +ts} Con{C.Nonterminal{+x}, +rest}:
      Empty.absurd({C.fits(C.Leaf{a} <> ts, grammar, C.Nonterminal{x} <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({C.fits(C.Node{q, ch} <> ts, grammar, []) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Terminal{+t}, +rest}:
      Empty.absurd({C.fits(C.Node{q, ch} <> ts, grammar, C.Terminal{t} <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Nonterminal{+x}, +rest}:
      +own = {Bool.and(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k)) : Bool}
      +after = {C.reads(ts, grammar, rest, input, Nat.add(k, C.width(C.Node{q, ch}))) : Bool}
      +left = Lemma.and_true_left(own, after, r)
      Lemma.and_true_intro(Bool.and(C.lhsIs(grammar, q, x), C.fits(ch, grammar, C.rhsOf(grammar, q))), C.fits(ts, grammar, rest),
        Lemma.and_true_intro(C.lhsIs(grammar, q, x), C.fits(ch, grammar, C.rhsOf(grammar, q)), Lemma.and_true_left(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k), left),
          reads_fits(ch, C.rhsOf(grammar, q), grammar, input, k, Lemma.and_true_right_side(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k), left))),
        reads_fits(ts, rest, grammar, input, Nat.add(k, C.width(C.Node{q, ch})), Lemma.and_true_right_side(own, after, r)))

law reads_length:
  for f: +List<C.Tree>
  for items: +List<C.Sym>
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +k: Nat
  for r: {C.reads(f, grammar, items, input, k) == True{} : Bool}
  {List.length(&2, C.Tree, f) == List.length(&2, C.Sym, items) : Nat}

def reads_length(f, items, grammar, input, k, r):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({0n == 1n+List.length(&2, C.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{C.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({1n+List.length(&2, C.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(r))
    case Con{C.Leaf{+a}, +ts} Con{C.Terminal{+t}, +rest}:
      +rest1 = {Bool.and(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +n = reads_length(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), rest1, r)))
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, C.Tree, ts), List.length(&2, C.Sym, rest), n)
    case Con{C.Leaf{+a}, +ts} Con{C.Nonterminal{+x}, +rest}:
      Empty.absurd({1n+List.length(&2, C.Tree, ts) == 1n+List.length(&2, C.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({1n+List.length(&2, C.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Terminal{+t}, +rest}:
      Empty.absurd({1n+List.length(&2, C.Tree, ts) == 1n+List.length(&2, C.Sym, rest) : Nat}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Nonterminal{+x}, +rest}:
      +own = {Bool.and(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k)) : Bool}
      +after = {C.reads(ts, grammar, rest, input, Nat.add(k, C.width(C.Node{q, ch}))) : Bool}
      +n = reads_length(ts, rest, grammar, input, Nat.add(k, C.width(C.Node{q, ch})), Lemma.and_true_right_side(own, after, r))
      Equal.cong(Nat, Nat, v => 1n+v, List.length(&2, C.Tree, ts), List.length(&2, C.Sym, rest), n)

# A node that reads nothing ends where it starts.
law width_zero:
  for +q: Nat
  for +ch: +List<C.Tree>
  for +k: Nat
  for +e: {C.leaves(ch) == [] : +List<Nat>}
  {Nat.add(k, C.width(C.Node{q, ch})) == k : Nat}

def width_zero(q, ch, k, e):
  Equal.trans(Nat, Nat.add(k, C.width(C.Node{q, ch})), Nat.add(k, 0n), k,
    Equal.cong(+List<Nat>, Nat, v => Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, v, []))), C.leaves(ch), [], e),
    Lemma.add_zero_right(k))

# ======== THE LAST STEP OF A NODE THAT READS NOTHING ========

law own_end_in:
  for rest: +List<C.Tree>
  for t: C.Tree
  for +q: Nat
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +set: +List<C.Bsr>
  for +e: {C.leaves(t <> rest) == [] : +List<Nat>}
  for h: {C.allIn(C.own(q, t <> rest, dot, i, k), set) == True{} : Bool}
  {C.member(C.Bsr{q, Nat.add(dot, List.length(&2, C.Tree, t <> rest)), i, k, k}, set) == True{} : Bool}

def own_end_in(rest, t, q, dot, i, k, set, e, h):
  match rest t:
    case +rs C.Leaf{+a}:
      Empty.absurd({C.member(C.Bsr{q, Nat.add(dot, List.length(&2, C.Tree, C.Leaf{a} <> rs)), i, k, k}, set) == True{} : Bool}, cons_not_nil(a, C.leaves(rs), e))
    case Nil{} C.Node{+q2, +ch2}:
      +lz = append_nil_left(C.leaves(ch2), [], e)
      +kz = width_zero(q2, ch2, k, lz)
      +far = {Nat.add(k, C.width(C.Node{q2, ch2})) : Nat}
      +m = Lemma.and_true_left(C.member(C.Bsr{q, 1n+dot, i, k, far}, set), True{}, h)
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {C.member(C.Bsr{q, _, i, k, k}, set) == True{} : Bool}
      %kz : {C.member(C.Bsr{q, 1n+dot, i, k, _}, set) == True{} : Bool}
      m
    case Con{+t2, +rest2} C.Node{+q2, +ch2}:
      +lz = append_nil_left(C.leaves(ch2), C.leaves(t2 <> rest2), e)
      +e2 = append_nil_right(C.leaves(ch2), C.leaves(t2 <> rest2), e)
      +kz = width_zero(q2, ch2, k, lz)
      +far = {Nat.add(k, C.width(C.Node{q2, ch2})) : Nat}
      +len = {List.length(&2, C.Tree, t2 <> rest2) : Nat}
      +tail = Lemma.and_true_right_side(C.member(C.Bsr{q, 1n+dot, i, k, far}, set), C.allIn(C.own(q, t2 <> rest2, 1n+dot, i, far), set), h)
      %Equal.sym(Nat, Nat.add(dot, 1n+len), 1n+Nat.add(dot, len), Lemma.add_succ_right(dot, len)) : {C.member(C.Bsr{q, _, i, k, k}, set) == True{} : Bool}
      %kz : {C.member(C.Bsr{q, 1n+Nat.add(dot, len), i, _, _}, set) == True{} : Bool}
      own_end_in(rest2, t2, q, 1n+dot, i, far, set, e2, tail)

law own_end:
  for ch: +List<C.Tree>
  for +q: Nat
  for +k: Nat
  for +set: +List<C.Bsr>
  for +e: {C.leaves(ch) == [] : +List<Nat>}
  for h: {C.allIn(C.own(q, ch, 0n, k, k), set) == True{} : Bool}
  {C.member(C.Bsr{q, List.length(&2, C.Tree, ch), k, k, k}, set) == True{} : Bool}

def own_end(ch, q, k, set, e, h):
  match ch:
    case Nil{}:
      Lemma.and_true_left(C.member(C.Bsr{q, 0n, k, k, k}, set), True{}, h)
    case Con{+t, +rest}:
      own_end_in(rest, t, q, 0n, k, k, set, e, h)

# ======== THE FIRST TOKEN ========

# A node whose children start with t2: through its children, or, when they read nothing,
# through what follows.
def node_head(w: +List<Nat>, +ch: +List<C.Tree>, +ts: +List<C.Tree>, +q: Nat, +input: +List<Nat>, +k: Nat, +t: Nat, +rest: +List<Nat>,
  +ew: {C.leaves(ch) == w : +List<Nat>},
  +e: {List.append(&2, Nat, C.leaves(ch), C.leaves(ts)) == t <> rest : +List<Nat>},
  recCh: @t2: Nat -> @r2: +List<Nat> -> {C.leaves(ch) == t2 <> r2 : +List<Nat>} -> {C.tokAt(input, k) == Some{t2} : Maybe<&2, Nat>},
  recTs: {C.leaves(ts) == t <> rest : +List<Nat>} -> {C.tokAt(input, Nat.add(k, C.width(C.Node{q, ch}))) == Some{t} : Maybe<&2, Nat>})
  -> {C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}:
  match w:
    case Nil{}:
      +e2 = Equal.trans(+List<Nat>, C.leaves(ts), List.append(&2, Nat, C.leaves(ch), C.leaves(ts)), t <> rest,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, C.leaves(ts)), [], C.leaves(ch), Equal.sym(+List<Nat>, C.leaves(ch), [], ew)), e)
      %width_zero(q, ch, k, ew) : {C.tokAt(input, _) == Some{t} : Maybe<&2, Nat>}
      recTs(e2)
    case Con{+t2, +r2}:
      +e2 = Equal.trans(+List<Nat>, t2 <> List.append(&2, Nat, r2, C.leaves(ts)), List.append(&2, Nat, C.leaves(ch), C.leaves(ts)), t <> rest,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, C.leaves(ts)), t2 <> r2, C.leaves(ch), Equal.sym(+List<Nat>, C.leaves(ch), t2 <> r2, ew)), e)
      Equal.trans(Maybe<&2, Nat>, C.tokAt(input, k), Some{t2}, Some{t}, recCh(t2, r2, ew),
        Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, t2, t, cons_head(t2, t, List.append(&2, Nat, r2, C.leaves(ts)), rest, e2)))

law reads_head:
  for f: +List<C.Tree>
  for items: +List<C.Sym>
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +t: Nat
  for +rest: +List<Nat>
  for +r: {C.reads(f, grammar, items, input, k) == True{} : Bool}
  for +e: {C.leaves(f) == t <> rest : +List<Nat>}
  {C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}

def reads_head(f, items, grammar, input, k, t, rest, r, e):
  match f items:
    case Nil{} +its:
      Empty.absurd({C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, cons_not_nil(t, rest, Equal.sym(+List<Nat>, [], t <> rest, e)))
    case Con{C.Leaf{+a}, +ts} Con{C.Terminal{+s}, +rs}:
      +rest1 = {Bool.and(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rs, input, 1n+k)) : Bool}
      +tok = tok_is_some(C.tokAt(input, k), a, Lemma.and_true_left(C.tokIs(C.tokAt(input, k), a), C.reads(ts, grammar, rs, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, s), rest1, r)))
      Equal.trans(Maybe<&2, Nat>, C.tokAt(input, k), Some{a}, Some{t}, tok, Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, a, t, cons_head(a, t, C.leaves(ts), rest, e)))
    case Con{C.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{C.Leaf{+a}, +ts} Con{C.Nonterminal{+x}, +rs}:
      Empty.absurd({C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Nonterminal{+x}, +rs}:
      +own = {Bool.and(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k)) : Bool}
      +far = {Nat.add(k, C.width(C.Node{q, ch})) : Nat}
      +after = {C.reads(ts, grammar, rs, input, far) : Bool}
      +rc = Lemma.and_true_right_side(C.lhsIs(grammar, q, x), C.reads(ch, grammar, C.rhsOf(grammar, q), input, k), Lemma.and_true_left(own, after, r))
      +rt = Lemma.and_true_right_side(own, after, r)
      node_head(C.leaves(ch), ch, ts, q, input, k, t, rest, {==}, e,
        t2 => r2 => h => reads_head(ch, C.rhsOf(grammar, q), grammar, input, k, t2, r2, rc, h),
        h => reads_head(ts, rs, grammar, input, far, t, rest, rt, h))
    case Con{C.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))
    case Con{C.Node{+q, +ch}, +ts} Con{C.Terminal{+s}, +rs}:
      Empty.absurd({C.tokAt(input, k) == Some{t} : Maybe<&2, Nat>}, Lemma.false_is_not_true(r))

# ======== WHAT A NODE PREDICTS ========

law bsr_eq_refl:
  for b: C.Bsr
  {C.bsrEq(b, b) == True{} : Bool}

def bsr_eq_refl(b):
  match b:
    case C.Bsr{+q, +d, +i, +k, +j}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), Lemma.nat_eq_refl(d),
          Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
            Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j)))))

law all_in_cons:
  for xs: +List<C.Bsr>
  for +y: C.Bsr
  for +set: +List<C.Bsr>
  for h: {C.allIn(xs, set) == True{} : Bool}
  {C.allIn(xs, y <> set) == True{} : Bool}

def all_in_cons(xs, y, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = h
      Lemma.and_true_intro(Bool.or(C.bsrEq(x, y), C.member(x, set)), C.allIn(rest, y <> set),
        Lemma.or_true_right_intro(C.bsrEq(x, y), C.member(x, set), Lemma.and_true_left(C.member(x, set), C.allIn(rest, set), both)),
        all_in_cons(rest, y, set, Lemma.and_true_right_side(C.member(x, set), C.allIn(rest, set), both)))

law all_in_refl:
  for xs: +List<C.Bsr>
  {C.allIn(xs, xs) == True{} : Bool}

def all_in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Bool.or(C.bsrEq(x, x), C.member(x, rest)), C.allIn(rest, x <> rest),
        Lemma.or_true_left_intro(C.bsrEq(x, x), C.member(x, rest), bsr_eq_refl(x)),
        all_in_cons(rest, x, rest, all_in_refl(rest)))

# The last step of a node of q that reads nothing is a step of the tree.
law end_step:
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +q: Nat
  for +ch: +List<C.Tree>
  for +k: Nat
  for +set: +List<C.Bsr>
  for +e: {C.leaves(ch) == [] : +List<Nat>}
  for +rc: {C.reads(ch, grammar, C.rhsOf(grammar, q), input, k) == True{} : Bool}
  for io: {C.allIn(C.own(q, ch, 0n, k, k), set) == True{} : Bool}
  {C.member(C.Bsr{q, List.length(&2, C.Sym, C.rhsOf(grammar, q)), k, k, k}, set) == True{} : Bool}

def end_step(grammar, input, q, ch, k, set, e, rc, io):
  %reads_length(ch, C.rhsOf(grammar, q), grammar, input, k, rc) : {C.member(C.Bsr{q, _, k, k, k}, set) == True{} : Bool}
  own_end(ch, q, k, set, e, io)

# A node of q at k predicts the token at k: by its first token, or it reads nothing and
# the tree itself shows that token after q.
def predicts_node(w: +List<Nat>, +grammar: +List<C.Production>, +start: Nat, +input: +List<Nat>, +root: C.Tree,
  +rr: {C.reads([root], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, C.leaves([root])) == List.length(&2, Nat, input) : Nat},
  +q: Nat, +ch: +List<C.Tree>, +k: Nat,
  +ew: {C.leaves(ch) == w : +List<Nat>},
  +rc: {C.reads(ch, grammar, C.rhsOf(grammar, q), input, k) == True{} : Bool},
  +io: {C.allIn(C.own(q, ch, 0n, k, k), C.steps([root], 0n)) == True{} : Bool})
  -> Predicts(grammar, start, q, C.tokAt(input, k)):
  match w:
    case Nil{}:
      +fit = reads_fits(ch, C.rhsOf(grammar, q), grammar, input, k, rc)
      Inr{((ch, (fit, ew)), (input, (root, (k, (k, (k, ((rr, rl), (end_step(grammar, input, q, ch, k, C.steps([root], 0n), ew, rc, io), {==}))))))))}
    case Con{+t, +r}:
      +fit = reads_fits(ch, C.rhsOf(grammar, q), grammar, input, k, rc)
      Inl{(ch, (t, (r, (fit, (ew, reads_head(ch, C.rhsOf(grammar, q), grammar, input, k, t, r, rc, ew))))))}

# ======== COMPARING TWO FORESTS ========

def then_same(+grammar: +List<C.Production>, +start: Nat, -t1: +List<C.Tree>, -t2: +List<C.Tree>, -f1: +List<C.Tree>, -f2: +List<C.Tree>,
  r: Same(grammar, start, t1, t2), mk: {t1 == t2 : +List<C.Tree>} -> {f1 == f2 : +List<C.Tree>}) -> Same(grammar, start, f1, f2):
  match r:
    case Inl{e}:
      Inl{mk(e)}
    case Inr{c}:
      Inr{c}

law leaf_eq:
  for +a: Nat
  for +b: Nat
  for +t: Nat
  for +ts1: +List<C.Tree>
  for +ts2: +List<C.Tree>
  for +ae: {a == t : Nat}
  for +be: {b == t : Nat}
  for +te: {ts1 == ts2 : +List<C.Tree>}
  {C.Leaf{a} <> ts1 == C.Leaf{b} <> ts2 : +List<C.Tree>}

def leaf_eq(a, b, t, ts1, ts2, ae, be, te):
  Equal.trans(+List<C.Tree>, C.Leaf{a} <> ts1, C.Leaf{t} <> ts1, C.Leaf{b} <> ts2, Equal.cong(Nat, +List<C.Tree>, v => C.Leaf{v} <> ts1, a, t, ae),
    Equal.trans(+List<C.Tree>, C.Leaf{t} <> ts1, C.Leaf{b} <> ts1, C.Leaf{b} <> ts2, Equal.cong(Nat, +List<C.Tree>, v => C.Leaf{v} <> ts1, t, b, Equal.sym(Nat, b, t, be)),
      Equal.cong(+List<C.Tree>, +List<C.Tree>, v => C.Leaf{b} <> v, ts1, ts2, te)))

law node_eq:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<C.Tree>
  for +ch2: +List<C.Tree>
  for +ts1: +List<C.Tree>
  for +ts2: +List<C.Tree>
  for +qe: {q1 == q2 : Nat}
  for +ce: {ch1 == ch2 : +List<C.Tree>}
  for +te: {ts1 == ts2 : +List<C.Tree>}
  {C.Node{q1, ch1} <> ts1 == C.Node{q2, ch2} <> ts2 : +List<C.Tree>}

def node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, ce, te):
  Equal.trans(+List<C.Tree>, C.Node{q1, ch1} <> ts1, C.Node{q2, ch1} <> ts1, C.Node{q2, ch2} <> ts2, Equal.cong(Nat, +List<C.Tree>, v => C.Node{v, ch1} <> ts1, q1, q2, qe),
    Equal.trans(+List<C.Tree>, C.Node{q2, ch1} <> ts1, C.Node{q2, ch2} <> ts1, C.Node{q2, ch2} <> ts2, Equal.cong(+List<C.Tree>, +List<C.Tree>, v => C.Node{q2, v} <> ts1, ch1, ch2, ce),
      Equal.cong(+List<C.Tree>, +List<C.Tree>, v => C.Node{q2, ch2} <> v, ts1, ts2, te)))

# The second tree's facts, moved to the first tree's production and children once they are equal.
law children_reads:
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +ch2: +List<C.Tree>
  for +k: Nat
  for +qe: {q1 == q2 : Nat}
  for +h: {C.reads(ch2, grammar, C.rhsOf(grammar, q2), input, k) == True{} : Bool}
  {C.reads(ch2, grammar, C.rhsOf(grammar, q1), input, k) == True{} : Bool}

def children_reads(grammar, input, q1, q2, ch2, k, qe, h):
  %Equal.sym(Nat, q1, q2, qe) : {C.reads(ch2, grammar, C.rhsOf(grammar, _), input, k) == True{} : Bool}
  h

law rest_reads:
  for +grammar: +List<C.Production>
  for +input: +List<Nat>
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<C.Tree>
  for +ch2: +List<C.Tree>
  for +ts2: +List<C.Tree>
  for +rest: +List<C.Sym>
  for +k: Nat
  for +ce: {ch1 == ch2 : +List<C.Tree>}
  for +h: {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q2, ch2}))) == True{} : Bool}
  {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q1, ch1}))) == True{} : Bool}

def rest_reads(grammar, input, q1, q2, ch1, ch2, ts2, rest, k, ce, h):
  %Equal.sym(+List<C.Tree>, ch1, ch2, ce) : {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q1, _}))) == True{} : Bool}
  h

law rest_in:
  for +q1: Nat
  for +q2: Nat
  for +ch1: +List<C.Tree>
  for +ch2: +List<C.Tree>
  for +ts2: +List<C.Tree>
  for +k: Nat
  for +set: +List<C.Bsr>
  for +ce: {ch1 == ch2 : +List<C.Tree>}
  for +h: {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q2, ch2}))), set) == True{} : Bool}
  {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q1, ch1}))), set) == True{} : Bool}

def rest_in(q1, q2, ch1, ch2, ts2, k, set, ce, h):
  %Equal.sym(+List<C.Tree>, ch1, ch2, ce) : {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q1, _}))), set) == True{} : Bool}
  h

# Equal children: go on with the rest of both sequences.
def children_then(+grammar: +List<C.Production>, +start: Nat, +input: +List<Nat>, +root2: C.Tree,
  +q1: Nat, +q2: Nat, +ch1: +List<C.Tree>, +ch2: +List<C.Tree>, +ts1: +List<C.Tree>, +ts2: +List<C.Tree>, +rest: +List<C.Sym>, +k: Nat,
  +qe: {q1 == q2 : Nat},
  +rt2: {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q2, ch2}))) == True{} : Bool},
  +it2: {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q2, ch2}))), C.steps([root2], 0n)) == True{} : Bool},
  rch: Same(grammar, start, ch1, ch2),
  recTs: {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q1, ch1}))) == True{} : Bool} -> {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q1, ch1}))), C.steps([root2], 0n)) == True{} : Bool} -> Same(grammar, start, ts1, ts2))
  -> Same(grammar, start, C.Node{q1, ch1} <> ts1, C.Node{q2, ch2} <> ts2):
  match rch:
    case Inl{+ce}:
      then_same(grammar, start, ts1, ts2, C.Node{q1, ch1} <> ts1, C.Node{q2, ch2} <> ts2,
        recTs(rest_reads(grammar, input, q1, q2, ch1, ch2, ts2, rest, k, ce, rt2), rest_in(q1, q2, ch1, ch2, ts2, k, C.steps([root2], 0n), ce, it2)),
        te => node_eq(q1, q2, ch1, ch2, ts1, ts2, qe, ce, te))
    case Inr{c}:
      Inr{c}

# Two nodes of x at k: the same production, or a clash.
def node_case(+grammar: +List<C.Production>, +start: Nat, +input: +List<Nat>, +root1: C.Tree, +root2: C.Tree,
  +rr1: {C.reads([root1], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool},
  +rl1: {List.length(&2, Nat, C.leaves([root1])) == List.length(&2, Nat, input) : Nat},
  +rr2: {C.reads([root2], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool},
  +rl2: {List.length(&2, Nat, C.leaves([root2])) == List.length(&2, Nat, input) : Nat},
  +q1: Nat, +q2: Nat, +ch1: +List<C.Tree>, +ch2: +List<C.Tree>, +ts1: +List<C.Tree>, +ts2: +List<C.Tree>, +x: Nat, +rest: +List<C.Sym>, +k: Nat,
  dec: Either<{q1 == q2 : Nat}, {Nat.is_eq(q1, q2) == False{} : Bool}>,
  +lhs1: {C.lhsIs(grammar, q1, x) == True{} : Bool},
  +lhs2: {C.lhsIs(grammar, q2, x) == True{} : Bool},
  +rc1: {C.reads(ch1, grammar, C.rhsOf(grammar, q1), input, k) == True{} : Bool},
  +rc2: {C.reads(ch2, grammar, C.rhsOf(grammar, q2), input, k) == True{} : Bool},
  +io1: {C.allIn(C.own(q1, ch1, 0n, k, k), C.steps([root1], 0n)) == True{} : Bool},
  +io2: {C.allIn(C.own(q2, ch2, 0n, k, k), C.steps([root2], 0n)) == True{} : Bool},
  +rt2: {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q2, ch2}))) == True{} : Bool},
  +it2: {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q2, ch2}))), C.steps([root2], 0n)) == True{} : Bool},
  recCh: {C.reads(ch2, grammar, C.rhsOf(grammar, q1), input, k) == True{} : Bool} -> Same(grammar, start, ch1, ch2),
  recTs: {C.reads(ts2, grammar, rest, input, Nat.add(k, C.width(C.Node{q1, ch1}))) == True{} : Bool} -> {C.allIn(C.steps(ts2, Nat.add(k, C.width(C.Node{q1, ch1}))), C.steps([root2], 0n)) == True{} : Bool} -> Same(grammar, start, ts1, ts2))
  -> Same(grammar, start, C.Node{q1, ch1} <> ts1, C.Node{q2, ch2} <> ts2):
  match dec:
    case Inl{+qe}:
      children_then(grammar, start, input, root2, q1, q2, ch1, ch2, ts1, ts2, rest, k, qe, rt2, it2, recCh(children_reads(grammar, input, q1, q2, ch2, k, qe, rc2)), recTs)
    case Inr{+neq}:
      Inr{(q1, (q2, (x, (C.tokAt(input, k), (neq, (lhs1, (lhs2,
        (predicts_node(C.leaves(ch1), grammar, start, input, root1, rr1, rl1, q1, ch1, k, {==}, rc1, io1),
         predicts_node(C.leaves(ch2), grammar, start, input, root2, rr2, rl2, q2, ch2, k, {==}, rc2, io2)))))))))}

law compare:
  for f1: +List<C.Tree>
  for f2: +List<C.Tree>
  for items: +List<C.Sym>
  for +grammar: +List<C.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +root1: C.Tree
  for +root2: C.Tree
  for +rr1: {C.reads([root1], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, C.leaves([root1])) == List.length(&2, Nat, input) : Nat}
  for +rr2: {C.reads([root2], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, C.leaves([root2])) == List.length(&2, Nat, input) : Nat}
  for +k: Nat
  for +r1: {C.reads(f1, grammar, items, input, k) == True{} : Bool}
  for +r2: {C.reads(f2, grammar, items, input, k) == True{} : Bool}
  for +in1: {C.allIn(C.steps(f1, k), C.steps([root1], 0n)) == True{} : Bool}
  for +in2: {C.allIn(C.steps(f2, k), C.steps([root2], 0n)) == True{} : Bool}
  Same(grammar, start, f1, f2)

def compare(f1, f2, items, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, k, r1, r2, in1, in2):
  match f1 f2 items:
    case Nil{} Nil{} Nil{}:
      Inl{{==}}
    case Nil{} Con{C.Leaf{+b}, +ts2} Nil{}:
      Empty.absurd(Same(grammar, start, [], C.Leaf{b} <> ts2), Lemma.false_is_not_true(r2))
    case Nil{} Con{C.Node{+q2, +ch2}, +ts2} Nil{}:
      Empty.absurd(Same(grammar, start, [], C.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(r2))
    case Nil{} +g2 Con{+s, +rest}:
      Empty.absurd(Same(grammar, start, [], g2), Lemma.false_is_not_true(r1))
    case Con{C.Leaf{+a}, +ts1} +g2 Nil{}:
      Empty.absurd(Same(grammar, start, C.Leaf{a} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{C.Leaf{+a}, +ts1} +g2 Con{C.Nonterminal{+x}, +rest}:
      Empty.absurd(Same(grammar, start, C.Leaf{a} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{C.Leaf{+a}, +ts1} Nil{} Con{C.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, C.Leaf{a} <> ts1, []), Lemma.false_is_not_true(r2))
    case Con{C.Leaf{+a}, +ts1} Con{C.Node{+q2, +ch2}, +ts2} Con{C.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, C.Leaf{a} <> ts1, C.Node{q2, ch2} <> ts2), Lemma.false_is_not_true(r2))
    case Con{C.Leaf{+a}, +ts1} Con{C.Leaf{+b}, +ts2} Con{C.Terminal{+t}, +rest}:
      +more1 = {Bool.and(C.tokIs(C.tokAt(input, k), a), C.reads(ts1, grammar, rest, input, 1n+k)) : Bool}
      +more2 = {Bool.and(C.tokIs(C.tokAt(input, k), b), C.reads(ts2, grammar, rest, input, 1n+k)) : Bool}
      +ae = Lemma.nat_eq_sound(a, t, Lemma.and_true_left(Nat.is_eq(a, t), more1, r1))
      +be = Lemma.nat_eq_sound(b, t, Lemma.and_true_left(Nat.is_eq(b, t), more2, r2))
      +rt1 = Lemma.and_true_right_side(C.tokIs(C.tokAt(input, k), a), C.reads(ts1, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more1, r1))
      +rt2 = Lemma.and_true_right_side(C.tokIs(C.tokAt(input, k), b), C.reads(ts2, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(b, t), more2, r2))
      then_same(grammar, start, ts1, ts2, C.Leaf{a} <> ts1, C.Leaf{b} <> ts2,
        compare(ts1, ts2, rest, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, 1n+k, rt1, rt2, in1, in2),
        te => leaf_eq(a, b, t, ts1, ts2, ae, be, te))
    case Con{C.Node{+q1, +ch1}, +ts1} +g2 Nil{}:
      Empty.absurd(Same(grammar, start, C.Node{q1, ch1} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{C.Node{+q1, +ch1}, +ts1} +g2 Con{C.Terminal{+t}, +rest}:
      Empty.absurd(Same(grammar, start, C.Node{q1, ch1} <> ts1, g2), Lemma.false_is_not_true(r1))
    case Con{C.Node{+q1, +ch1}, +ts1} Nil{} Con{C.Nonterminal{+x}, +rest}:
      Empty.absurd(Same(grammar, start, C.Node{q1, ch1} <> ts1, []), Lemma.false_is_not_true(r2))
    case Con{C.Node{+q1, +ch1}, +ts1} Con{C.Leaf{+b}, +ts2} Con{C.Nonterminal{+x}, +rest}:
      Empty.absurd(Same(grammar, start, C.Node{q1, ch1} <> ts1, C.Leaf{b} <> ts2), Lemma.false_is_not_true(r2))
    case Con{C.Node{+q1, +ch1}, +ts1} Con{C.Node{+q2, +ch2}, +ts2} Con{C.Nonterminal{+x}, +rest}:
      +S1 = {C.steps([root1], 0n) : +List<C.Bsr>}
      +S2 = {C.steps([root2], 0n) : +List<C.Bsr>}
      +far1 = {Nat.add(k, C.width(C.Node{q1, ch1})) : Nat}
      +far2 = {Nat.add(k, C.width(C.Node{q2, ch2})) : Nat}
      +own1 = {Bool.and(C.lhsIs(grammar, q1, x), C.reads(ch1, grammar, C.rhsOf(grammar, q1), input, k)) : Bool}
      +own2 = {Bool.and(C.lhsIs(grammar, q2, x), C.reads(ch2, grammar, C.rhsOf(grammar, q2), input, k)) : Bool}
      +left1 = Lemma.and_true_left(own1, C.reads(ts1, grammar, rest, input, far1), r1)
      +left2 = Lemma.and_true_left(own2, C.reads(ts2, grammar, rest, input, far2), r2)
      +lhs1 = Lemma.and_true_left(C.lhsIs(grammar, q1, x), C.reads(ch1, grammar, C.rhsOf(grammar, q1), input, k), left1)
      +lhs2 = Lemma.and_true_left(C.lhsIs(grammar, q2, x), C.reads(ch2, grammar, C.rhsOf(grammar, q2), input, k), left2)
      +rc1 = Lemma.and_true_right_side(C.lhsIs(grammar, q1, x), C.reads(ch1, grammar, C.rhsOf(grammar, q1), input, k), left1)
      +rc2 = Lemma.and_true_right_side(C.lhsIs(grammar, q2, x), C.reads(ch2, grammar, C.rhsOf(grammar, q2), input, k), left2)
      +rt1 = Lemma.and_true_right_side(own1, C.reads(ts1, grammar, rest, input, far1), r1)
      +rt2 = Lemma.and_true_right_side(own2, C.reads(ts2, grammar, rest, input, far2), r2)
      +below1 = C.in_app_right(C.own(q1, ch1, 0n, k, k), List.append(&2, C.Bsr, C.steps(ch1, k), C.steps(ts1, far1)), S1, in1)
      +below2 = C.in_app_right(C.own(q2, ch2, 0n, k, k), List.append(&2, C.Bsr, C.steps(ch2, k), C.steps(ts2, far2)), S2, in2)
      +io1 = C.in_app_left(C.own(q1, ch1, 0n, k, k), List.append(&2, C.Bsr, C.steps(ch1, k), C.steps(ts1, far1)), S1, in1)
      +io2 = C.in_app_left(C.own(q2, ch2, 0n, k, k), List.append(&2, C.Bsr, C.steps(ch2, k), C.steps(ts2, far2)), S2, in2)
      +ic1 = C.in_app_left(C.steps(ch1, k), C.steps(ts1, far1), S1, below1)
      +ic2 = C.in_app_left(C.steps(ch2, k), C.steps(ts2, far2), S2, below2)
      +it1 = C.in_app_right(C.steps(ch1, k), C.steps(ts1, far1), S1, below1)
      +it2 = C.in_app_right(C.steps(ch2, k), C.steps(ts2, far2), S2, below2)
      node_case(grammar, start, input, root1, root2, rr1, rl1, rr2, rl2,
        q1, q2, ch1, ch2, ts1, ts2, x, rest, k, decide(Nat.is_eq(q1, q2), q1, q2, {==}), lhs1, lhs2, rc1, rc2, io1, io2, rt2, it2,
        h => compare(ch1, ch2, C.rhsOf(grammar, q1), grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, k, rc1, h, ic1, ic2),
        h => g => compare(ts1, ts2, rest, grammar, start, input, root1, root2, rr1, rl1, rr2, rl2, far1, rt1, h, it1, g))

# ======== THE LAW ========

def treeOr(ts: +List<C.Tree>, +d: C.Tree) -> C.Tree:
  match ts:
    case Nil{}:
      d
    case Con{t, rest}:
      t

law no_clash:
  for +grammar: +List<C.Production>
  for +start: Nat
  for +t1: C.Tree
  for +t2: C.Tree
  for r: Same(grammar, start, [t1], [t2])
  for ll1: LL1(grammar, start)
  {t1 == t2 : C.Tree}

def no_clash(grammar, start, t1, t2, r, ll1):
  match r:
    case Inl{e}:
      Equal.cong(+List<C.Tree>, C.Tree, v => treeOr(v, t1), [t1], [t2], e)
    case Inr{c}:
      match c:
        case (q1, (q2, (x, (next, (neq, (lhs1, (lhs2, (p1, p2)))))))):
          Empty.absurd({t1 == t2 : C.Tree}, ll1(q1, q2, x, next, neq, lhs1, lhs2, p1, p2))

# AN LL(1) GRAMMAR IS UNAMBIGUOUS: two parse trees of the same input are the same tree.
law ll1_unambiguous:
  for +grammar: +List<C.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree1: C.Tree
  for +tree2: C.Tree
  for ll1: LL1(grammar, start)
  for +rr1: {C.reads([tree1], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool}
  for +rl1: {List.length(&2, Nat, C.leaves([tree1])) == List.length(&2, Nat, input) : Nat}
  for +rr2: {C.reads([tree2], grammar, [C.Nonterminal{start}], input, 0n) == True{} : Bool}
  for +rl2: {List.length(&2, Nat, C.leaves([tree2])) == List.length(&2, Nat, input) : Nat}
  {tree1 == tree2 : C.Tree}

def ll1_unambiguous(grammar, start, input, tree1, tree2, ll1, rr1, rl1, rr2, rl2):
  no_clash(grammar, start, tree1, tree2,
    compare([tree1], [tree2], [C.Nonterminal{start}], grammar, start, input, tree1, tree2, rr1, rl1, rr2, rl2, 0n, rr1, rr2,
      all_in_refl(C.steps([tree1], 0n)), all_in_refl(C.steps([tree2], 0n))),
    ll1)
