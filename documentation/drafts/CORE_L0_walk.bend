import Base
import /Users/janwillem/Developer/Xcode/ApusApus/Bend/LEMMAS.bend as Lemma

# L0, THE BNF CORE (measurement draft, not installed).

type Sym is Data:
  Terminal{kind: Nat}
  Nonterminal{id: Nat}

type Production is Data:
  Production{lhs: Nat, rhs: +List<Sym>}

type Tree is Data:
  Leaf{kind: Nat}
  Node{index: Nat, children: +List<Tree>}

type Bsr is Data:
  Bsr{index: Nat, dot: Nat, i: Nat, k: Nat, j: Nat}

def rhsOf(+grammar: +List<Production>, index: Nat) -> +List<Sym>:
  match grammar index:
    case Nil{} _:
      []
    case Con{Production{lhs, +rhs}, rest} 0n:
      rhs
    case Con{p, rest} 1n+n:
      rhsOf(rest, n)

def lhsIs(+grammar: +List<Production>, index: Nat, +id: Nat) -> Bool:
  match grammar index:
    case Nil{} _:
      False{}
    case Con{Production{+lhs, rhs}, rest} 0n:
      Nat.is_eq(lhs, id)
    case Con{p, rest} 1n+n:
      lhsIs(rest, n, id)

def leaves(forest: +List<Tree>) -> +List<Nat>:
  match forest:
    case Nil{}:
      []
    case Con{Leaf{+k}, ts}:
      k <> leaves(ts)
    case Con{Node{q, +ch}, ts}:
      List.append(&2, Nat, leaves(ch), leaves(ts))

def fits(forest: +List<Tree>, +grammar: +List<Production>, items: +List<Sym>) -> Bool:
  match forest items:
    case Nil{} Nil{}:
      True{}
    case Con{Leaf{kind}, ts} Con{Terminal{k}, rest}:
      Bool.and(Nat.is_eq(kind, k), fits(ts, grammar, rest))
    case Con{Node{+q, ch}, ts} Con{Nonterminal{id}, rest}:
      Bool.and(Bool.and(lhsIs(grammar, q, id), fits(ch, grammar, rhsOf(grammar, q))), fits(ts, grammar, rest))
    case _ _:
      False{}

def tokAt(input: +List<Nat>, n: Nat) -> Maybe<&2, Nat>:
  match input n:
    case Nil{} _:
      None{}
    case Con{+x, rest} 0n:
      Some{x}
    case Con{x, rest} 1n+m:
      tokAt(rest, m)

def tokIs(found: Maybe<&2, Nat>, +t: Nat) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, t)

def width(+t: Tree) -> Nat:
  List.length(&2, Nat, leaves([t]))

def emptyAt(dot: Nat, +q: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match dot:
    case 0n:
      [Bsr{q, 0n, i, k, k}]
    case 1n+d:
      []

# The forest fits the items and reads the input from position k on.
def reads(forest: +List<Tree>, +grammar: +List<Production>, items: +List<Sym>, +input: +List<Nat>, +k: Nat) -> Bool:
  match forest items:
    case Nil{} Nil{}:
      True{}
    case Con{Leaf{+kind}, ts} Con{Terminal{t}, rest}:
      Bool.and(Nat.is_eq(kind, t), Bool.and(tokIs(tokAt(input, k), kind), reads(ts, grammar, rest, input, 1n+k)))
    case Con{Node{+q, +ch}, ts} Con{Nonterminal{id}, rest}:
      Bool.and(Bool.and(lhsIs(grammar, q, id), reads(ch, grammar, rhsOf(grammar, q), input, k)), reads(ts, grammar, rest, input, Nat.add(k, width(Node{q, ch}))))
    case _ _:
      False{}

# A node's own steps: one per child (the slot after it), or the empty step of an empty
# right side.
def own(+q: Nat, ch: +List<Tree>, +dot: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match ch:
    case Nil{}:
      emptyAt(dot, q, i, k)
    case Con{+t, rest}:
      Bsr{q, 1n+dot, i, k, Nat.add(k, width(t))} <> own(q, rest, 1n+dot, i, Nat.add(k, width(t)))

# All steps of a forest starting at k: each node's own steps, then its children's.
def steps(forest: +List<Tree>, +k: Nat) -> +List<Bsr>:
  match forest:
    case Nil{}:
      []
    case Con{Leaf{kind}, ts}:
      steps(ts, 1n+k)
    case Con{Node{+q, +ch}, ts}:
      List.append(&2, Bsr, own(q, ch, 0n, k, k), List.append(&2, Bsr, steps(ch, k), steps(ts, Nat.add(k, width(Node{q, ch})))))

# ---- Sets ----

def bsrEq(a: Bsr, b: Bsr) -> Bool:
  match a b:
    case Bsr{q1, d1, i1, k1, j1} Bsr{q2, d2, i2, k2, j2}:
      Bool.and(Nat.is_eq(q1, q2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(i1, i2), Bool.and(Nat.is_eq(k1, k2), Nat.is_eq(j1, j2)))))

def member(+x: Bsr, set: +List<Bsr>) -> Bool:
  match set:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(bsrEq(x, y), member(x, rest))

def allIn(xs: +List<Bsr>, +set: +List<Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(member(x, set), allIn(rest, set))

law all_in_app:
  for xs: +List<Bsr>
  for +ys: +List<Bsr>
  for +set: +List<Bsr>
  for hx: {allIn(xs, set) == True{} : Bool}
  for hy: {allIn(ys, set) == True{} : Bool}
  {allIn(List.append(&2, Bsr, xs, ys), set) == True{} : Bool}

def all_in_app(xs, ys, set, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      +both = hx
      Lemma.and_true_intro(member(x, set), allIn(List.append(&2, Bsr, rest, ys), set),
        Lemma.and_true_left(member(x, set), allIn(rest, set), both),
        all_in_app(rest, ys, set, Lemma.and_true_right_side(member(x, set), allIn(rest, set), both), hy))

law in_app_left:
  for xs: +List<Bsr>
  for +ys: +List<Bsr>
  for +set: +List<Bsr>
  for h: {allIn(List.append(&2, Bsr, xs, ys), set) == True{} : Bool}
  {allIn(xs, set) == True{} : Bool}

def in_app_left(xs, ys, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = h
      Lemma.and_true_intro(member(x, set), allIn(rest, set),
        Lemma.and_true_left(member(x, set), allIn(List.append(&2, Bsr, rest, ys), set), both),
        in_app_left(rest, ys, set, Lemma.and_true_right_side(member(x, set), allIn(List.append(&2, Bsr, rest, ys), set), both)))

law in_app_right:
  for xs: +List<Bsr>
  for +ys: +List<Bsr>
  for +set: +List<Bsr>
  for h: {allIn(List.append(&2, Bsr, xs, ys), set) == True{} : Bool}
  {allIn(ys, set) == True{} : Bool}

def in_app_right(xs, ys, set, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      in_app_right(rest, ys, set, Lemma.and_true_right_side(member(x, set), allIn(List.append(&2, Bsr, rest, ys), set), h))

# ---- One walk for every phase ----
#
# A phase is a rule P on nodes, read in a context c (grammar, annotations, input): a
# production q, its children ch, its start k. A forest is admissible for P when every
# node keeps P. A phase's oracle maps the parser's set s to the steps it keeps; the
# phase supplies two lemmas about one node whose children fit its right side: d1 (its
# own steps kept: P holds) and d2 (P holds, its own steps in s: they are kept). The walk
# then proves, for every forest that fits: its steps are all kept exactly when every
# node keeps P.

def Adm(~C: Data, ~P: C -> Nat -> +List<Tree> -> Nat -> Type, +c: C, forest: +List<Tree>, +k: Nat) -> Type:
  match forest:
    case Nil{}:
      Unit
    case Con{Leaf{kind}, +ts}:
      Adm(~C, ~P, c, ts, 1n+k)
    case Con{Node{+q, +ch}, +ts}:
      P(c, q, ch, k) & Adm(~C, ~P, c, ch, k) & Adm(~C, ~P, c, ts, Nat.add(k, width(Node{q, ch})))

# The parts of a fitting node: its children fit its right side, and the rest fits the rest.
law reads_children:
  for +q: Nat
  for +ch: +List<Tree>
  for +ts: +List<Tree>
  for +grammar: +List<Production>
  for +id: Nat
  for +rest: +List<Sym>
  for +input: +List<Nat>
  for +k: Nat
  for f: {reads(Node{q, ch} <> ts, grammar, Nonterminal{id} <> rest, input, k) == True{} : Bool}
  {reads(ch, grammar, rhsOf(grammar, q), input, k) == True{} : Bool}

def reads_children(q, ch, ts, grammar, id, rest, input, k, f):
  Lemma.and_true_right_side(lhsIs(grammar, q, id), reads(ch, grammar, rhsOf(grammar, q), input, k),
    Lemma.and_true_left(Bool.and(lhsIs(grammar, q, id), reads(ch, grammar, rhsOf(grammar, q), input, k)), reads(ts, grammar, rest, input, Nat.add(k, width(Node{q, ch}))), f))

law reads_after:
  for +q: Nat
  for +ch: +List<Tree>
  for +ts: +List<Tree>
  for +grammar: +List<Production>
  for +id: Nat
  for +rest: +List<Sym>
  for +input: +List<Nat>
  for +k: Nat
  for f: {reads(Node{q, ch} <> ts, grammar, Nonterminal{id} <> rest, input, k) == True{} : Bool}
  {reads(ts, grammar, rest, input, Nat.add(k, width(Node{q, ch}))) == True{} : Bool}

def reads_after(q, ch, ts, grammar, id, rest, input, k, f):
  Lemma.and_true_right_side(Bool.and(lhsIs(grammar, q, id), reads(ch, grammar, rhsOf(grammar, q), input, k)), reads(ts, grammar, rest, input, Nat.add(k, width(Node{q, ch}))), f)

law reads_leaf:
  for +kind: Nat
  for +ts: +List<Tree>
  for +grammar: +List<Production>
  for +t: Nat
  for +rest: +List<Sym>
  for +input: +List<Nat>
  for +k: Nat
  for f: {reads(Leaf{kind} <> ts, grammar, Terminal{t} <> rest, input, k) == True{} : Bool}
  {reads(ts, grammar, rest, input, 1n+k) == True{} : Bool}

def reads_leaf(kind, ts, grammar, t, rest, input, k, f):
  Lemma.and_true_right_side(tokIs(tokAt(input, k), kind), reads(ts, grammar, rest, input, 1n+k),
    Lemma.and_true_right_side(Nat.is_eq(kind, t), Bool.and(tokIs(tokAt(input, k), kind), reads(ts, grammar, rest, input, 1n+k)), f))

# Rules hold, so every step is kept.
def keepAll(~C: Data, ~P: C -> Nat -> +List<Tree> -> Nat -> Type, ~Pre: C -> +List<Bsr> -> Data, ~oracle: C -> +List<Bsr> -> +List<Bsr>,
            ~d2: @c:C -> @grammar:+List<Production> -> @input:+List<Nat> -> @s:+List<Bsr> -> @pre:Pre(c, s) -> @q:Nat -> @ch:+List<Tree> -> @k:Nat -> {reads(ch, grammar, rhsOf(grammar, q), input, k) == True{} : Bool} -> {allIn(own(q, ch, 0n, k, k), s) == True{} : Bool} -> P(c, q, ch, k) -> {allIn(own(q, ch, 0n, k, k), oracle(c, s)) == True{} : Bool},
            +c: C, +grammar: +List<Production>, +input: +List<Nat>, +s: +List<Bsr>, +pre: Pre(c, s), forest: +List<Tree>, items: +List<Sym>, +k: Nat,
            fit: {reads(forest, grammar, items, input, k) == True{} : Bool}, inS: {allIn(steps(forest, k), s) == True{} : Bool}, adm: Adm(~C, ~P, c, forest, k)) -> {allIn(steps(forest, k), oracle(c, s)) == True{} : Bool}:
  match forest items:
    case Nil{} _:
      {==}
    case Con{Leaf{kind}, +ts} Nil{}:
      Empty.absurd({allIn(steps(Leaf{kind} <> ts, k), oracle(c, s)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({allIn(steps(Node{q, ch} <> ts, k), oracle(c, s)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Leaf{kind}, +ts} Con{Nonterminal{id}, +rest}:
      Empty.absurd({allIn(steps(Leaf{kind} <> ts, k), oracle(c, s)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Node{+q, +ch}, +ts} Con{Terminal{t}, +rest}:
      Empty.absurd({allIn(steps(Node{q, ch} <> ts, k), oracle(c, s)) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Leaf{+kind}, +ts} Con{Terminal{+t}, +rest}:
      keepAll(~C, ~P, ~Pre, ~oracle, ~d2, c, grammar, input, s, pre, ts, rest, 1n+k, reads_leaf(kind, ts, grammar, t, rest, input, k, fit), inS, adm)
    case Con{Node{+q, +ch}, +ts} Con{Nonterminal{+id}, +rest}:
      match adm:
        case (hP, (hCh, hTs)):
          +fitAll = fit
          +fCh2 = reads_children(q, ch, ts, grammar, id, rest, input, k, fitAll)
          +fTs = reads_after(q, ch, ts, grammar, id, rest, input, k, fitAll)
          +end = Nat.add(k, width(Node{q, ch}))
          +more = List.append(&2, Bsr, steps(ch, k), steps(ts, end))
          +all = inS
          +inMore = in_app_right(own(q, ch, 0n, k, k), more, s, all)
          all_in_app(own(q, ch, 0n, k, k), more, oracle(c, s),
            d2(c, grammar, input, s, pre, q, ch, k, fCh2, in_app_left(own(q, ch, 0n, k, k), more, s, all), hP),
            all_in_app(steps(ch, k), steps(ts, end), oracle(c, s),
              keepAll(~C, ~P, ~Pre, ~oracle, ~d2, c, grammar, input, s, pre, ch, rhsOf(grammar, q), k, fCh2, in_app_left(steps(ch, k), steps(ts, end), s, inMore), hCh),
              keepAll(~C, ~P, ~Pre, ~oracle, ~d2, c, grammar, input, s, pre, ts, rest, end, fTs, in_app_right(steps(ch, k), steps(ts, end), s, inMore), hTs)))

# Every step is kept, so the rules hold.
def admAll(~C: Data, ~P: C -> Nat -> +List<Tree> -> Nat -> Type, ~oracle: C -> +List<Bsr> -> +List<Bsr>,
           ~d1: @c:C -> @grammar:+List<Production> -> @input:+List<Nat> -> @s:+List<Bsr> -> @q:Nat -> @ch:+List<Tree> -> @k:Nat -> {reads(ch, grammar, rhsOf(grammar, q), input, k) == True{} : Bool} -> {allIn(own(q, ch, 0n, k, k), oracle(c, s)) == True{} : Bool} -> P(c, q, ch, k),
           +c: C, +grammar: +List<Production>, +input: +List<Nat>, +s: +List<Bsr>, forest: +List<Tree>, items: +List<Sym>, +k: Nat,
           fit: {reads(forest, grammar, items, input, k) == True{} : Bool}, h: {allIn(steps(forest, k), oracle(c, s)) == True{} : Bool}) -> Adm(~C, ~P, c, forest, k):
  match forest items:
    case Nil{} _:
      Unit{}
    case Con{Leaf{kind}, +ts} Nil{}:
      Empty.absurd(Adm(~C, ~P, c, Leaf{kind} <> ts, k), Lemma.false_is_not_true(fit))
    case Con{Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd(Adm(~C, ~P, c, Node{q, ch} <> ts, k), Lemma.false_is_not_true(fit))
    case Con{Leaf{kind}, +ts} Con{Nonterminal{id}, +rest}:
      Empty.absurd(Adm(~C, ~P, c, Leaf{kind} <> ts, k), Lemma.false_is_not_true(fit))
    case Con{Node{+q, +ch}, +ts} Con{Terminal{t}, +rest}:
      Empty.absurd(Adm(~C, ~P, c, Node{q, ch} <> ts, k), Lemma.false_is_not_true(fit))
    case Con{Leaf{+kind}, +ts} Con{Terminal{+t}, +rest}:
      admAll(~C, ~P, ~oracle, ~d1, c, grammar, input, s, ts, rest, 1n+k, reads_leaf(kind, ts, grammar, t, rest, input, k, fit), h)
    case Con{Node{+q, +ch}, +ts} Con{Nonterminal{+id}, +rest}:
      +fitAll = fit
      +fCh2 = reads_children(q, ch, ts, grammar, id, rest, input, k, fitAll)
      +fTs = reads_after(q, ch, ts, grammar, id, rest, input, k, fitAll)
      +end = Nat.add(k, width(Node{q, ch}))
      +more = List.append(&2, Bsr, steps(ch, k), steps(ts, end))
      +all = h
      +hMore = in_app_right(own(q, ch, 0n, k, k), more, oracle(c, s), all)
      (d1(c, grammar, input, s, q, ch, k, fCh2, in_app_left(own(q, ch, 0n, k, k), more, oracle(c, s), all)),
       (admAll(~C, ~P, ~oracle, ~d1, c, grammar, input, s, ch, rhsOf(grammar, q), k, fCh2, in_app_left(steps(ch, k), steps(ts, end), oracle(c, s), hMore)),
        admAll(~C, ~P, ~oracle, ~d1, c, grammar, input, s, ts, rest, end, fTs, in_app_right(steps(ch, k), steps(ts, end), oracle(c, s), hMore))))

# ---- A trivial phase, to instantiate the walk ----

def NoRule(c: Nat, q: Nat, ch: +List<Tree>, k: Nat) -> Type:
  Unit

def NoPre(c: Nat, s: +List<Bsr>) -> Data:
  Unit

def keepAllSteps(c: Nat, s: +List<Bsr>) -> +List<Bsr>:
  s

def noRuleKept(c: Nat, grammar: +List<Production>, input: +List<Nat>, s: +List<Bsr>, pre: NoPre(c, s), q: Nat, ch: +List<Tree>, k: Nat, f: {reads(ch, grammar, rhsOf(grammar, q), input, k) == True{} : Bool}, inS: {allIn(own(q, ch, 0n, k, k), s) == True{} : Bool}, u: NoRule(c, q, ch, k)) -> {allIn(own(q, ch, 0n, k, k), keepAllSteps(c, s)) == True{} : Bool}:
  inS

def noRuleHolds(c: Nat, grammar: +List<Production>, input: +List<Nat>, s: +List<Bsr>, q: Nat, ch: +List<Tree>, k: Nat, f: {reads(ch, grammar, rhsOf(grammar, q), input, k) == True{} : Bool}, h: {allIn(own(q, ch, 0n, k, k), keepAllSteps(c, s)) == True{} : Bool}) -> NoRule(c, q, ch, k):
  Unit{}

law trivial_keep:
  for +c: Nat
  for +grammar: +List<Production>
  for +input: +List<Nat>
  for +s: +List<Bsr>
  for forest: +List<Tree>
  for items: +List<Sym>
  for +k: Nat
  for fit: {reads(forest, grammar, items, input, k) == True{} : Bool}
  for inS: {allIn(steps(forest, k), s) == True{} : Bool}
  for adm: Adm(~Nat, ~NoRule, c, forest, k)
  {allIn(steps(forest, k), keepAllSteps(c, s)) == True{} : Bool}

def trivial_keep(c, grammar, input, s, forest, items, k, fit, inS, adm):
  keepAll(~Nat, ~NoRule, ~NoPre, ~keepAllSteps, ~noRuleKept, c, grammar, input, s, Unit{}, forest, items, k, fit, inS, adm)

law trivial_adm:
  for +c: Nat
  for +grammar: +List<Production>
  for +input: +List<Nat>
  for +s: +List<Bsr>
  for forest: +List<Tree>
  for items: +List<Sym>
  for +k: Nat
  for fit: {reads(forest, grammar, items, input, k) == True{} : Bool}
  for h: {allIn(steps(forest, k), keepAllSteps(c, s)) == True{} : Bool}
  Adm(~Nat, ~NoRule, c, forest, k)

def trivial_adm(c, grammar, input, s, forest, items, k, fit, h):
  admAll(~Nat, ~NoRule, ~keepAllSteps, ~noRuleHolds, c, grammar, input, s, forest, items, k, fit, h)
