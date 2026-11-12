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

def width(+t: Tree) -> Nat:
  List.length(&2, Nat, leaves([t]))

def emptyAt(dot: Nat, +q: Nat, +i: Nat, +k: Nat) -> +List<Bsr>:
  match dot:
    case 0n:
      [Bsr{q, 0n, i, k, k}]
    case 1n+d:
      []

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
# A phase is a rule P on nodes: a production q, its children ch, its start k. A forest is
# admissible for P when every node keeps P. An oracle keeps a set of steps; it is exact for
# P when, at every node, P holds exactly when the node's own steps are kept (d1, d2: the
# phase's own lemmas). Then a forest is admissible exactly when all its steps are kept.

def Adm(~P: Nat -> +List<Tree> -> Nat -> Type, forest: +List<Tree>, +k: Nat) -> Type:
  match forest:
    case Nil{}:
      Unit
    case Con{Leaf{kind}, +ts}:
      Adm(~P, ts, 1n+k)
    case Con{Node{+q, +ch}, +ts}:
      P(q, ch, k) & Adm(~P, ch, k) & Adm(~P, ts, Nat.add(k, width(Node{q, ch})))

# Rules hold, so every step is kept: a tree whose steps are in the parser's set s and
# whose nodes keep P has all its steps in the phase's set oracle(s).
def keepAll(~P: Nat -> +List<Tree> -> Nat -> Type, ~oracle: +List<Bsr> -> +List<Bsr>,
            ~d2: @s:+List<Bsr> -> @q:Nat -> @ch:+List<Tree> -> @k:Nat -> {allIn(own(q, ch, 0n, k, k), s) == True{} : Bool} -> P(q, ch, k) -> {allIn(own(q, ch, 0n, k, k), oracle(s)) == True{} : Bool},
            +s: +List<Bsr>, forest: +List<Tree>, +k: Nat, inS: {allIn(steps(forest, k), s) == True{} : Bool}, adm: Adm(~P, forest, k)) -> {allIn(steps(forest, k), oracle(s)) == True{} : Bool}:
  match forest:
    case Nil{}:
      {==}
    case Con{Leaf{kind}, +ts}:
      keepAll(~P, ~oracle, ~d2, s, ts, 1n+k, inS, adm)
    case Con{Node{+q, +ch}, +ts}:
      match adm:
        case (hP, (hCh, hTs)):
          +end = Nat.add(k, width(Node{q, ch}))
          +rest = List.append(&2, Bsr, steps(ch, k), steps(ts, end))
          +all = inS
          +inRest = in_app_right(own(q, ch, 0n, k, k), rest, s, all)
          all_in_app(own(q, ch, 0n, k, k), rest, oracle(s),
            d2(s, q, ch, k, in_app_left(own(q, ch, 0n, k, k), rest, s, all), hP),
            all_in_app(steps(ch, k), steps(ts, end), oracle(s),
              keepAll(~P, ~oracle, ~d2, s, ch, k, in_app_left(steps(ch, k), steps(ts, end), s, inRest), hCh),
              keepAll(~P, ~oracle, ~d2, s, ts, end, in_app_right(steps(ch, k), steps(ts, end), s, inRest), hTs)))

# Every step is kept, so the rules hold.
def admAll(~P: Nat -> +List<Tree> -> Nat -> Type, ~oracle: +List<Bsr> -> +List<Bsr>,
           ~d1: @s:+List<Bsr> -> @q:Nat -> @ch:+List<Tree> -> @k:Nat -> {allIn(own(q, ch, 0n, k, k), oracle(s)) == True{} : Bool} -> P(q, ch, k),
           +s: +List<Bsr>, forest: +List<Tree>, +k: Nat, h: {allIn(steps(forest, k), oracle(s)) == True{} : Bool}) -> Adm(~P, forest, k):
  match forest:
    case Nil{}:
      Unit{}
    case Con{Leaf{kind}, +ts}:
      admAll(~P, ~oracle, ~d1, s, ts, 1n+k, h)
    case Con{Node{+q, +ch}, +ts}:
      +end = Nat.add(k, width(Node{q, ch}))
      +rest = List.append(&2, Bsr, steps(ch, k), steps(ts, end))
      +hAll = h
      +hRest = in_app_right(own(q, ch, 0n, k, k), rest, oracle(s), hAll)
      (d1(s, q, ch, k, in_app_left(own(q, ch, 0n, k, k), rest, oracle(s), hAll)),
       (admAll(~P, ~oracle, ~d1, s, ch, k, in_app_left(steps(ch, k), steps(ts, end), oracle(s), hRest)),
        admAll(~P, ~oracle, ~d1, s, ts, end, in_app_right(steps(ch, k), steps(ts, end), oracle(s), hRest))))

# ---- A trivial phase, to instantiate the walk ----

def NoRule(q: Nat, ch: +List<Tree>, k: Nat) -> Type:
  Unit

def keepAllSteps(s: +List<Bsr>) -> +List<Bsr>:
  s

def noRuleKept(s: +List<Bsr>, q: Nat, ch: +List<Tree>, k: Nat, inS: {allIn(own(q, ch, 0n, k, k), s) == True{} : Bool}, u: NoRule(q, ch, k)) -> {allIn(own(q, ch, 0n, k, k), keepAllSteps(s)) == True{} : Bool}:
  inS

def noRuleHolds(s: +List<Bsr>, q: Nat, ch: +List<Tree>, k: Nat, h: {allIn(own(q, ch, 0n, k, k), keepAllSteps(s)) == True{} : Bool}) -> NoRule(q, ch, k):
  Unit{}

law trivial_keep:
  for +s: +List<Bsr>
  for forest: +List<Tree>
  for +k: Nat
  for inS: {allIn(steps(forest, k), s) == True{} : Bool}
  for adm: Adm(~NoRule, forest, k)
  {allIn(steps(forest, k), keepAllSteps(s)) == True{} : Bool}

def trivial_keep(s, forest, k, inS, adm):
  keepAll(~NoRule, ~keepAllSteps, ~noRuleKept, s, forest, k, inS, adm)

law trivial_adm:
  for +s: +List<Bsr>
  for forest: +List<Tree>
  for +k: Nat
  for h: {allIn(steps(forest, k), keepAllSteps(s)) == True{} : Bool}
  Adm(~NoRule, forest, k)

def trivial_adm(s, forest, k, h):
  admAll(~NoRule, ~keepAllSteps, ~noRuleHolds, s, forest, k, h)
