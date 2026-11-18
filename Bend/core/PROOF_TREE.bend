import Base
import ../LEMMAS.bend as Lemma
import ./PROOF_BASICS.bend as B
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./SUPPORT.bend as Sup
import ./TABLES.bend as T
import ./PREDICT.bend as Pr
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_DECIDE.bend as D
import ./PROOF_LL1.bend as L
import ./PROOF_TABLES.bend as PT
import ./PROOF_PREDICT.bend as Pp
import ./PROOF_HOLD.bend as H
import ./SETS.bend as Sets
import ./LL1.bend as LL

# THE RULES KEEP A PARSE TREE OF AN LL(1) GRAMMAR: every fact a rule of the predicting
# engine gives from facts on the tree lies on the tree too (PROOF_HOLD.bend, `onTree`).
# Descriptors, steps and pops by the tree's nodes; seeds because only the tree's production
# gets past prediction (else the tables have a conflict); resumes because a nonterminal's
# node at a position is unique in the tree (`compare`).

# ======== FINDING A STEP ========

def bStart(b: Core.Bsr) -> Nat:
  match b:
    case Core.Bsr{q, d, +i, k, j}:
      i

def ask_moved(+ask: H.Ask, +grammar: +List<Core.Production>, +y: Core.Bsr, +z: Core.Bsr,
  +e: {y == z : Core.Bsr}, +h: {H.askAt(ask, y, grammar) == True{} : Bool}) -> {H.askAt(ask, z, grammar) == True{} : Bool}:
  %e : {H.askAt(ask, _, grammar) == True{} : Bool}
  h

def intro_pick(+z: Core.Bsr, +rest: +List<Core.Bsr>, +ask: H.Ask, +grammar: +List<Core.Production>, +y: Core.Bsr,
  +h: {H.askAt(ask, y, grammar) == True{} : Bool},
  cases: Either<{Core.bsrEq(y, z) == True{} : Bool}, {Core.member(y, rest) == True{} : Bool}>,
  later: {Core.member(y, rest) == True{} : Bool} -> {H.anyStep(rest, ask, grammar) == True{} : Bool}) -> {H.anyStep(z <> rest, ask, grammar) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(H.askAt(ask, z, grammar), H.anyStep(rest, ask, grammar), ask_moved(ask, grammar, y, z, G.bsr_eq_sound(y, z, e), h))
    case Inr{m}:
      Lemma.or_true_right_intro(H.askAt(ask, z, grammar), H.anyStep(rest, ask, grammar), later(m))

# A step of the set that answers the ask: the ask is answered in the set.
law any_intro:
  for ys: +List<Core.Bsr>
  for +ask: H.Ask
  for +grammar: +List<Core.Production>
  for +y: Core.Bsr
  for +m: {Core.member(y, ys) == True{} : Bool}
  for +h: {H.askAt(ask, y, grammar) == True{} : Bool}
  {H.anyStep(ys, ask, grammar) == True{} : Bool}

def any_intro(ys, ask, grammar, y, m, h):
  match ys:
    case Nil{}:
      Empty.absurd({H.anyStep([], ask, grammar) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+z, +rest}:
      intro_pick(z, rest, ask, grammar, y, h, Lemma.or_true_cases(Core.bsrEq(y, z), Core.member(y, rest), m), m2 => any_intro(rest, ask, grammar, y, m2, h))

def Found(+ys: +List<Core.Bsr>, +ask: H.Ask, +grammar: +List<Core.Production>) -> Type:
  &y: Core.Bsr -> {Core.member(y, ys) == True{} : Bool} & {H.askAt(ask, y, grammar) == True{} : Bool}

def found_later(+z: Core.Bsr, +rest: +List<Core.Bsr>, +ask: H.Ask, +grammar: +List<Core.Production>, f: Found(rest, ask, grammar)) -> Found(z <> rest, ask, grammar):
  match f:
    case (+y, (+m, +a)):
      (y, (Lemma.or_true_right_intro(Core.bsrEq(y, z), Core.member(y, rest), m), a))

def elim_pick(+z: Core.Bsr, +rest: +List<Core.Bsr>, +ask: H.Ask, +grammar: +List<Core.Production>,
  cases: Either<{H.askAt(ask, z, grammar) == True{} : Bool}, {H.anyStep(rest, ask, grammar) == True{} : Bool}>,
  later: {H.anyStep(rest, ask, grammar) == True{} : Bool} -> Found(rest, ask, grammar)) -> Found(z <> rest, ask, grammar):
  match cases:
    case Inl{a}:
      (z, (Lemma.or_true_left_intro(Core.bsrEq(z, z), Core.member(z, rest), D.bsr_eq_refl(z)), a))
    case Inr{h}:
      found_later(z, rest, ask, grammar, later(h))

# An answered ask has a step that answers it.
law any_elim:
  for ys: +List<Core.Bsr>
  for +ask: H.Ask
  for +grammar: +List<Core.Production>
  for +h: {H.anyStep(ys, ask, grammar) == True{} : Bool}
  Found(ys, ask, grammar)

def any_elim(ys, ask, grammar, h):
  match ys:
    case Nil{}:
      Empty.absurd(Found([], ask, grammar), Lemma.false_is_not_true(h))
    case Con{+z, +rest}:
      elim_pick(z, rest, ask, grammar, Lemma.or_true_cases(H.askAt(ask, z, grammar), H.anyStep(rest, ask, grammar), h), h2 => any_elim(rest, ask, grammar, h2))

# ======== THE NODE OF A STEP ========

def start_pick(+hd: Core.Bsr, +tail: +List<Core.Bsr>, +x: Core.Bsr, +i: Nat, +he: {bStart(hd) == i : Nat},
  cases: Either<{Core.bsrEq(x, hd) == True{} : Bool}, {Core.member(x, tail) == True{} : Bool}>,
  later: {Core.member(x, tail) == True{} : Bool} -> {bStart(x) == i : Nat}) -> {bStart(x) == i : Nat}:
  match cases:
    case Inl{e}:
      Equal.trans(Nat, bStart(x), bStart(hd), i, Equal.cong(Core.Bsr, Nat, v => bStart(v), x, hd, G.bsr_eq_sound(x, hd, e)), he)
    case Inr{m}:
      later(m)

def empty_start(d0: Nat, +p: Nat, +i: Nat, +k: Nat, +x: Core.Bsr, +m: {Core.member(x, Core.emptyAt(d0, p, i, k)) == True{} : Bool}) -> {bStart(x) == i : Nat}:
  match d0:
    case 0n:
      +hd = {Core.Bsr{p, 0n, i, k, k} : Core.Bsr}
      start_pick(hd, [], x, i, {==}, Lemma.or_true_cases(Core.bsrEq(x, hd), False{}, m), m2 => Empty.absurd({bStart(x) == i : Nat}, Lemma.false_is_not_true(m2)))
    case 1n+(+e):
      Empty.absurd({bStart(x) == i : Nat}, Lemma.false_is_not_true(m))

# Every own step of a node starts where the node starts.
law own_start:
  for cs: +List<Core.Tree>
  for +p: Nat
  for +d0: Nat
  for +i: Nat
  for +k: Nat
  for +x: Core.Bsr
  for +m: {Core.member(x, Core.own(p, cs, d0, i, k)) == True{} : Bool}
  {bStart(x) == i : Nat}

def own_start(cs, p, d0, i, k, x, m):
  match cs:
    case Nil{}:
      empty_start(d0, p, i, k, x, m)
    case Con{+t, +rest}:
      +far = Nat.add(k, Core.width(t))
      +hd = {Core.Bsr{p, 1n+d0, i, k, far} : Core.Bsr}
      +tail = Core.own(p, rest, 1n+d0, i, far)
      start_pick(hd, tail, x, i, {==}, Lemma.or_true_cases(Core.bsrEq(x, hd), Core.member(x, tail), m), m2 => own_start(rest, p, 1n+d0, i, far, x, m2))

# A node of q at i whose own steps include y, inside the set.
def NodeOf(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +y: Core.Bsr) -> Type:
  &ch: +List<Core.Tree> ->
    {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, i) == True{} : Bool} &
    {Core.allIn(Core.own(q, ch, 0n, i, i), set) == True{} : Bool} &
    {Core.allIn(Core.steps(ch, i), set) == True{} : Bool} &
    {Core.member(y, Core.own(q, ch, 0n, i, i)) == True{} : Bool} &
    {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == True{} : Bool}

def node_moved(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +y: Core.Bsr,
  +eq: {PT.bIndex(y) == q : Nat}, +ei: {bStart(y) == i : Nat}, n: NodeOf(grammar, input, set, q, i, y)) -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y):
  %Equal.sym(Nat, PT.bIndex(y), q, eq) : NodeOf(grammar, input, set, _, bStart(y), y)
  %Equal.sym(Nat, bStart(y), i, ei) : NodeOf(grammar, input, set, q, _, y)
  n

# A production used in a tree is in the grammar: it is a production of its own left side.
def valid_of(+grammar: +List<Core.Production>, +q: Nat, +z: Nat, +h: {Core.lhsIs(grammar, q, z) == True{} : Bool}) -> {Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) == True{} : Bool}:
  %Equal.sym(Nat, Gll.lhsOf(grammar, q), z, G.lhs_of(grammar, q, z, h)) : {Core.lhsIs(grammar, q, _) == True{} : Bool}
  h

def node_rest(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +q: Nat, +k: Nat, +y: Core.Bsr,
  c2: Either<{Core.member(y, Core.steps(ch, k)) == True{} : Bool}, {Core.member(y, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q, ch})))) == True{} : Bool}>,
  inCh: {Core.member(y, Core.steps(ch, k)) == True{} : Bool} -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y),
  inTs: {Core.member(y, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q, ch})))) == True{} : Bool} -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y))
  -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y):
  match c2:
    case Inl{m}:
      inCh(m)
    case Inr{m}:
      inTs(m)

def node_split(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +z: Nat, +k: Nat, +y: Core.Bsr,
  +hl: {Core.lhsIs(grammar, q, z) == True{} : Bool},
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, ch, 0n, k, k), set) == True{} : Bool},
  +ic: {Core.allIn(Core.steps(ch, k), set) == True{} : Bool},
  c1: Either<{Core.member(y, Core.own(q, ch, 0n, k, k)) == True{} : Bool}, {Core.member(y, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q, ch}))))) == True{} : Bool}>,
  inCh: {Core.member(y, Core.steps(ch, k)) == True{} : Bool} -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y),
  inTs: {Core.member(y, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q, ch})))) == True{} : Bool} -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y))
  -> NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y):
  match c1:
    case Inl{+m1}:
      node_moved(grammar, input, set, q, k, y, PT.own_index(ch, q, 0n, k, k, y, m1), own_start(ch, q, 0n, k, k, y, m1),
        (ch, (rc, (io, (ic, (m1, valid_of(grammar, q, z, hl)))))))
    case Inr{+m2}:
      node_rest(grammar, input, set, ch, ts, q, k, y, PT.member_split(Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q, ch}))), y, m2), inCh, inTs)

# Every step of a forest that reads the input is an own step of a node of the forest.
law node_of:
  for forest: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +set: +List<Core.Bsr>
  for +y: Core.Bsr
  for +rd: {Core.reads(forest, grammar, items, input, k) == True{} : Bool}
  for +inS: {Core.allIn(Core.steps(forest, k), set) == True{} : Bool}
  for +m: {Core.member(y, Core.steps(forest, k)) == True{} : Bool}
  NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y)

def node_of(forest, items, grammar, input, k, set, y, rd, inS, m):
  match forest items:
    case Nil{} +its:
      Empty.absurd(NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y), Lemma.false_is_not_true(m))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, rd))
      node_of(ts, rest, grammar, input, 1n+k, set, y, rt, inS, m)
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd(NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y), Lemma.false_is_not_true(rd))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      Empty.absurd(NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y), Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd(NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y), Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd(NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y), Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+z, +need}, +rest}:
      +far = Nat.add(k, Core.width(Core.Node{q, ch}))
      +head = {Bool.and(Core.lhsIs(grammar, q, z), Core.needOk(need, Core.width(Core.Node{q, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), rd)
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, q, z), Core.needOk(need, Core.width(Core.Node{q, ch})), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), rd)
      +below = P.in_app_right(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), set, inS)
      +io = P.in_app_left(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), set, inS)
      +ic = P.in_app_left(Core.steps(ch, k), Core.steps(ts, far), set, below)
      +it = P.in_app_right(Core.steps(ch, k), Core.steps(ts, far), set, below)
      node_split(grammar, input, set, q, ch, ts, z, k, y, hl, rc, io, ic,
        PT.member_split(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), y, m),
        m2 => node_of(ch, Core.rhsOf(grammar, q), grammar, input, k, set, y, rc, ic, m2),
        m3 => node_of(ts, rest, grammar, input, far, set, y, rt, it, m3))

# ======== A CURSOR IN A NODE ========

# The step that ended the cursor's last item is in the set (none before the first item).
# Some step of the set ends the item before dot d of a node of q at i at j.
def Ended(+set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat) -> Type:
  &kk: Nat -> {Core.member(Core.Bsr{q, d, i, kk, j}, set) == True{} : Bool}

def Last(+set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat) -> Type:
  Either<{d == 0n : Nat}, Ended(set, q, i, d, j)>

# A node of q at i, read up to dot d, which ends at j: the children still to read read the
# rest of q's right side from j, and their own and inner steps are in the set.
def Cursor(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat) -> Type:
  &rest: +List<Core.Tree> ->
    {Core.reads(rest, grammar, G.dropFrom(d, Core.rhsOf(grammar, q)), input, j) == True{} : Bool} &
    {Core.allIn(Core.own(q, rest, d, i, j), set) == True{} : Bool} &
    {Core.allIn(Core.steps(rest, j), set) == True{} : Bool} &
    {Nat.add(d, List.length(&2, Core.Sym, G.dropFrom(d, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat} &
    Last(set, q, i, d, j)

def Next(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +far: Nat, +ts: +List<Core.Tree>, +y: Core.Bsr) -> Type:
  {Core.reads(ts, grammar, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), input, far) == True{} : Bool} ->
  {Core.allIn(Core.own(q, ts, 1n+d, i, far), set) == True{} : Bool} ->
  {Core.allIn(Core.steps(ts, far), set) == True{} : Bool} ->
  {Nat.add(1n+d, List.length(&2, Core.Sym, G.dropFrom(1n+d, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat} ->
  Last(set, q, i, 1n+d, far) ->
  {Core.member(y, Core.own(q, ts, 1n+d, i, far)) == True{} : Bool} ->
  Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y))

def reads_items(+ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +pos: Nat, +a: +List<Core.Sym>, +b: +List<Core.Sym>,
  +e: {a == b : +List<Core.Sym>}, +h: {Core.reads(ts, grammar, b, input, pos) == True{} : Bool}) -> {Core.reads(ts, grammar, a, input, pos) == True{} : Bool}:
  %Equal.sym(+List<Core.Sym>, a, b, e) : {Core.reads(ts, grammar, _, input, pos) == True{} : Bool}
  h

def reads_pos(+ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +items: +List<Core.Sym>, +input: +List<Nat>, +a: Nat, +b: Nat,
  +e: {a == b : Nat}, +h: {Core.reads(ts, grammar, items, input, b) == True{} : Bool}) -> {Core.reads(ts, grammar, items, input, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.reads(ts, grammar, items, input, _) == True{} : Bool}
  h

def steps_pos(+ts: +List<Core.Tree>, +set: +List<Core.Bsr>, +a: Nat, +b: Nat,
  +e: {a == b : Nat}, +h: {Core.allIn(Core.steps(ts, b), set) == True{} : Bool}) -> {Core.allIn(Core.steps(ts, a), set) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Core.allIn(Core.steps(ts, _), set) == True{} : Bool}
  h

def rest_reads(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +d: Nat, +s: Core.Sym, +r: +List<Core.Sym>, +ts: +List<Core.Tree>, +far: Nat,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == s <> r : +List<Core.Sym>},
  +h: {Core.reads(ts, grammar, r, input, far) == True{} : Bool}) -> {Core.reads(ts, grammar, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), input, far) == True{} : Bool}:
  reads_items(ts, grammar, input, far, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), r, G.drop_next(Core.rhsOf(grammar, q), d, s, r, ie), h)

def next_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat, +far: Nat, +ts: +List<Core.Tree>, +y: Core.Bsr,
  +hdIn: {Core.member(Core.Bsr{q, 1n+d, i, j, far}, set) == True{} : Bool},
  +rdN: {Core.reads(ts, grammar, G.dropFrom(1n+d, Core.rhsOf(grammar, q)), input, far) == True{} : Bool},
  +ioT: {Core.allIn(Core.own(q, ts, 1n+d, i, far), set) == True{} : Bool},
  +isN: {Core.allIn(Core.steps(ts, far), set) == True{} : Bool},
  +invN: {Nat.add(1n+d, List.length(&2, Core.Sym, G.dropFrom(1n+d, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  cases: Either<{Core.bsrEq(y, Core.Bsr{q, 1n+d, i, j, far}) == True{} : Bool}, {Core.member(y, Core.own(q, ts, 1n+d, i, far)) == True{} : Bool}>,
  later: Next(grammar, input, set, q, i, d, far, ts, y)) -> Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)):
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, y, Core.Bsr{q, 1n+d, i, j, far}, G.bsr_eq_sound(y, Core.Bsr{q, 1n+d, i, j, far}, e)) : Cursor(grammar, input, set, q, i, PT.bDot(_), PT.bEnd(_))
      (ts, (rdN, (ioT, (isN, (invN, Inr{(j, hdIn)})))))
    case Inr{m2}:
      later(rdN, ioT, isN, invN, Inr{(j, hdIn)}, m2)

# One child further: the cursor after it, or the walk goes on.
def step_next(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat, +far: Nat, +ts: +List<Core.Tree>, +y: Core.Bsr,
  +s: Core.Sym, +r: +List<Core.Sym>,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == s <> r : +List<Core.Sym>},
  +inv: {Nat.add(d, List.length(&2, Core.Sym, s <> r)) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  +rt: {Core.reads(ts, grammar, r, input, far) == True{} : Bool},
  +io: {Core.allIn(Core.Bsr{q, 1n+d, i, j, far} <> Core.own(q, ts, 1n+d, i, far), set) == True{} : Bool},
  +isN: {Core.allIn(Core.steps(ts, far), set) == True{} : Bool},
  +m: {Core.member(y, Core.Bsr{q, 1n+d, i, j, far} <> Core.own(q, ts, 1n+d, i, far)) == True{} : Bool},
  later: Next(grammar, input, set, q, i, d, far, ts, y)) -> Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)):
  +hd = {Core.Bsr{q, 1n+d, i, j, far} : Core.Bsr}
  +tail = Core.own(q, ts, 1n+d, i, far)
  next_pick(grammar, input, set, q, i, d, j, far, ts, y,
    Lemma.and_true_left(Core.member(hd, set), Core.allIn(tail, set), io),
    rest_reads(grammar, input, q, d, s, r, ts, far, ie, rt),
    Lemma.and_true_right_side(Core.member(hd, set), Core.allIn(tail, set), io),
    isN, G.inv_next(grammar, q, d, s, r, ie, inv),
    Lemma.or_true_cases(Core.bsrEq(y, hd), Core.member(y, tail), m), later)

def nil_pick(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +j: Nat, +y: Core.Bsr,
  +rd: {Core.reads([], grammar, G.dropFrom(0n, Core.rhsOf(grammar, q)), input, j) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, [], 0n, i, j), set) == True{} : Bool},
  +inv: {Nat.add(0n, List.length(&2, Core.Sym, G.dropFrom(0n, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  last: Last(set, q, i, 0n, j),
  cases: Either<{Core.bsrEq(y, Core.Bsr{q, 0n, i, j, j}) == True{} : Bool}, {False{} == True{} : Bool}>) -> Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)):
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, y, Core.Bsr{q, 0n, i, j, j}, G.bsr_eq_sound(y, Core.Bsr{q, 0n, i, j, j}, e)) : Cursor(grammar, input, set, q, i, PT.bDot(_), PT.bEnd(_))
      ([], (rd, (io, ({==}, (inv, last)))))
    case Inr{f}:
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(f))

def walk_nil(d: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +j: Nat, +y: Core.Bsr,
  +rd: {Core.reads([], grammar, G.dropFrom(d, Core.rhsOf(grammar, q)), input, j) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, [], d, i, j), set) == True{} : Bool},
  +inv: {Nat.add(d, List.length(&2, Core.Sym, G.dropFrom(d, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  last: Last(set, q, i, d, j),
  +m: {Core.member(y, Core.own(q, [], d, i, j)) == True{} : Bool}) -> Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)):
  match d:
    case 0n:
      nil_pick(grammar, input, set, q, i, j, y, rd, io, inv, last, Lemma.or_true_cases(Core.bsrEq(y, Core.Bsr{q, 0n, i, j, j}), False{}, m))
    case 1n+(+e):
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(m))

def walk_con(t: Core.Tree, items: +List<Core.Sym>, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +q: Nat, +i: Nat, +d: Nat, +j: Nat, +y: Core.Bsr,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>},
  +rd: {Core.reads(t <> ts, grammar, items, input, j) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, t <> ts, d, i, j), set) == True{} : Bool},
  +inSt: {Core.allIn(Core.steps(t <> ts, j), set) == True{} : Bool},
  +inv: {Nat.add(d, List.length(&2, Core.Sym, items)) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  +m: {Core.member(y, Core.own(q, t <> ts, d, i, j)) == True{} : Bool},
  later: Next(grammar, input, set, q, i, d, Nat.add(j, Core.width(t)), ts, y)) -> Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)):
  match t items:
    case Core.Leaf{+a} Con{Core.Terminal{+tt}, +r}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, j), a), Core.reads(ts, grammar, r, input, 1n+j)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, j), a), Core.reads(ts, grammar, r, input, 1n+j), Lemma.and_true_right_side(Nat.is_eq(a, tt), more, rd))
      +far = Nat.add(j, Core.width(Core.Leaf{a}))
      +ef = {Lemma.add_one_right(j) : {far == 1n+j : Nat}}
      step_next(grammar, input, set, q, i, d, j, far, ts, y, Core.Terminal{tt}, r, ie, inv,
        reads_pos(ts, grammar, r, input, far, 1n+j, ef, rt), io, steps_pos(ts, set, far, 1n+j, ef, inSt), m, later)
    case Core.Node{+q2, +ch2} Con{Core.Nonterminal{+x, +need}, +r}:
      +far = Nat.add(j, Core.width(Core.Node{q2, ch2}))
      +own2 = {Bool.and(Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch2}))), Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, j)) : Bool}
      +rt = Lemma.and_true_right_side(own2, Core.reads(ts, grammar, r, input, far), rd)
      +below = P.in_app_right(Core.own(q2, ch2, 0n, j, j), List.append(&2, Core.Bsr, Core.steps(ch2, j), Core.steps(ts, far)), set, inSt)
      step_next(grammar, input, set, q, i, d, j, far, ts, y, Core.Nonterminal{x, need}, r, ie, inv, rt, io,
        P.in_app_right(Core.steps(ch2, j), Core.steps(ts, far), set, below), m, later)
    case Core.Leaf{+a} Nil{}:
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(rd))
    case Core.Leaf{+a} Con{Core.Nonterminal{+x, +need}, +r}:
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(rd))
    case Core.Node{+q2, +ch2} Nil{}:
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(rd))
    case Core.Node{+q2, +ch2} Con{Core.Terminal{+tt}, +r}:
      Empty.absurd(Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y)), Lemma.false_is_not_true(rd))

# From a cursor, the own step y of the rest of the node gives the cursor after y.
law cursor_walk:
  for rest: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +set: +List<Core.Bsr>
  for +q: Nat
  for +i: Nat
  for +d: Nat
  for +j: Nat
  for +y: Core.Bsr
  for +rd: {Core.reads(rest, grammar, G.dropFrom(d, Core.rhsOf(grammar, q)), input, j) == True{} : Bool}
  for +io: {Core.allIn(Core.own(q, rest, d, i, j), set) == True{} : Bool}
  for +inSt: {Core.allIn(Core.steps(rest, j), set) == True{} : Bool}
  for +inv: {Nat.add(d, List.length(&2, Core.Sym, G.dropFrom(d, Core.rhsOf(grammar, q)))) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}
  for last: Last(set, q, i, d, j)
  for +m: {Core.member(y, Core.own(q, rest, d, i, j)) == True{} : Bool}
  Cursor(grammar, input, set, q, i, PT.bDot(y), PT.bEnd(y))

def cursor_walk(rest, grammar, input, set, q, i, d, j, y, rd, io, inSt, inv, last, m):
  match rest:
    case Nil{}:
      walk_nil(d, grammar, input, set, q, i, j, y, rd, io, inv, last, m)
    case Con{+t, +ts}:
      walk_con(t, G.dropFrom(d, Core.rhsOf(grammar, q)), ts, grammar, input, set, q, i, d, j, y, {==}, rd, io, inSt, inv, m,
        a => b => c => e => l => m2 => cursor_walk(ts, grammar, input, set, q, i, 1n+d, Nat.add(j, Core.width(t)), y, a, b, c, e, l, m2))

# ======== A DESCRIPTOR ON THE TREE ========

def Steps(tree: Core.Tree) -> +List<Core.Bsr>:
  Core.steps([tree], 0n)

# The node of a step of a parse tree.
def node_in(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +y: Core.Bsr, +m: {Core.member(y, Steps(tree)) == True{} : Bool}) -> NodeOf(grammar, input, Steps(tree), PT.bIndex(y), bStart(y), y):
  node_of([tree], [Core.Nonterminal{start, Core.Anything{}}], grammar, input, 0n, Steps(tree), y, rr, L.all_in_refl(Steps(tree)), m)

def cursor_dot(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +y: Core.Bsr,
  node: NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y)) -> Cursor(grammar, input, set, PT.bIndex(y), bStart(y), PT.bDot(y), PT.bEnd(y)):
  match node:
    case (+ch, (+rc, (+io, (+ic, (+my, valid))))):
      cursor_walk(ch, grammar, input, set, PT.bIndex(y), bStart(y), 0n, bStart(y), y, rc, io, ic, {==}, Inl{{==}}, my)

def cursor_zero(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +y: Core.Bsr,
  node: NodeOf(grammar, input, set, PT.bIndex(y), bStart(y), y)) -> Cursor(grammar, input, set, PT.bIndex(y), bStart(y), 0n, bStart(y)):
  match node:
    case (+ch, (+rc, (+io, (+ic, (+my, valid))))):
      (ch, (rc, (io, (ic, ({==}, Inl{{==}})))))

def desc_cases(+grammar: +List<Core.Production>, +input: +List<Nat>, +set: +List<Core.Bsr>, +yq: Nat, +yd: Nat, +yi: Nat, +yk: Nat, +yj: Nat, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +eq: {yq == q : Nat}, +ek: {yi == k : Nat},
  cases: Either<{Bool.and(Nat.is_eq(yd, d), Nat.is_eq(yj, i)) == True{} : Bool}, {Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k)) == True{} : Bool}>,
  node: NodeOf(grammar, input, set, yq, yi, Core.Bsr{yq, yd, yi, yk, yj})) -> Cursor(grammar, input, set, q, k, d, i):
  match cases:
    case Inl{+h}:
      +ed = Lemma.nat_eq_sound(yd, d, Lemma.and_true_left(Nat.is_eq(yd, d), Nat.is_eq(yj, i), h))
      +ej = Lemma.nat_eq_sound(yj, i, Lemma.and_true_right_side(Nat.is_eq(yd, d), Nat.is_eq(yj, i), h))
      %ed : Cursor(grammar, input, set, q, k, _, i)
      %ej : Cursor(grammar, input, set, q, k, yd, _)
      %eq : Cursor(grammar, input, set, _, k, yd, yj)
      %ek : Cursor(grammar, input, set, yq, _, yd, yj)
      cursor_dot(grammar, input, set, Core.Bsr{yq, yd, yi, yk, yj}, node)
    case Inr{+h}:
      +e0 = Lemma.nat_eq_sound(d, 0n, Lemma.and_true_left(Nat.is_eq(d, 0n), Nat.is_eq(i, k), h))
      +eik = Lemma.nat_eq_sound(i, k, Lemma.and_true_right_side(Nat.is_eq(d, 0n), Nat.is_eq(i, k), h))
      %Equal.sym(Nat, d, 0n, e0) : Cursor(grammar, input, set, q, k, _, i)
      %Equal.sym(Nat, i, k, eik) : Cursor(grammar, input, set, q, k, 0n, _)
      %eq : Cursor(grammar, input, set, _, k, 0n, k)
      %ek : Cursor(grammar, input, set, yq, _, 0n, _)
      cursor_zero(grammar, input, set, Core.Bsr{yq, yd, yi, yk, yj}, node)

def desc_found(y: Core.Bsr, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +m: {Core.member(y, Steps(tree)) == True{} : Bool},
  +a: {H.askAt(H.AskDesc{q, d, k, i}, y, grammar) == True{} : Bool}) -> Cursor(grammar, input, Steps(tree), q, k, d, i):
  match y:
    case Core.Bsr{+yq, +yd, +yi, +yk, +yj}:
      +either = {Bool.or(Bool.and(Nat.is_eq(yd, d), Nat.is_eq(yj, i)), Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k))) : Bool}
      +rest = {Bool.and(Nat.is_eq(yi, k), either) : Bool}
      +eq = Lemma.nat_eq_sound(yq, q, Lemma.and_true_left(Nat.is_eq(yq, q), rest, a))
      +r2 = Lemma.and_true_right_side(Nat.is_eq(yq, q), rest, a)
      +ek = Lemma.nat_eq_sound(yi, k, Lemma.and_true_left(Nat.is_eq(yi, k), either, r2))
      +r3 = Lemma.and_true_right_side(Nat.is_eq(yi, k), either, r2)
      desc_cases(grammar, input, Steps(tree), yq, yd, yi, yk, yj, q, d, k, i, eq, ek,
        Lemma.or_true_cases(Bool.and(Nat.is_eq(yd, d), Nat.is_eq(yj, i)), Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k)), r3),
        node_in(grammar, start, input, tree, rr, Core.Bsr{yq, yd, yi, yk, yj}, m))

def found_desc(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +q: Nat, +d: Nat, +k: Nat, +i: Nat, f: Found(Steps(tree), H.AskDesc{q, d, k, i}, grammar)) -> Cursor(grammar, input, Steps(tree), q, k, d, i):
  match f:
    case (+y, (+m, +a)):
      desc_found(y, grammar, start, input, tree, rr, q, d, k, i, m, a)

# A descriptor on the tree gives a cursor in a node of the tree.
law cursor_of:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +i: Nat
  for +h: {H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar) == True{} : Bool}
  Cursor(grammar, input, Steps(tree), q, k, d, i)

def cursor_of(grammar, start, input, tree, rr, q, d, k, i, h):
  found_desc(grammar, start, input, tree, rr, q, d, k, i, any_elim(Steps(tree), H.AskDesc{q, d, k, i}, grammar, h))

# ======== THE RULES ON A DESCRIPTOR ========

# The facts all lie on the tree whose steps are `set`.
def allOn(fs: +List<Sup.Fact>, +grammar: +List<Core.Production>, +set: +List<Core.Bsr>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, rest}:
      Bool.and(H.onTree(f, grammar, set), allOn(rest, grammar, set))

def eq_true(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Lemma.nat_eq_refl(a)

def desc_ask(+grammar: +List<Core.Production>, +q: Nat, +d: Nat, +k: Nat, +kk: Nat, +i: Nat) -> {H.askAt(H.AskDesc{q, d, k, i}, Core.Bsr{q, d, k, kk, i}, grammar) == True{} : Bool}:
  +dot = {Bool.and(Nat.is_eq(d, d), Nat.is_eq(i, i)) : Bool}
  +either = {Bool.or(dot, Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k))) : Bool}
  Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(k, k), either), Lemma.nat_eq_refl(q),
    Lemma.and_true_intro(Nat.is_eq(k, k), either, Lemma.nat_eq_refl(k),
      Lemma.or_true_left_intro(dot, Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, k)), Lemma.and_true_intro(Nat.is_eq(d, d), Nat.is_eq(i, i), Lemma.nat_eq_refl(d), Lemma.nat_eq_refl(i)))))

def pop_ask(+grammar: +List<Core.Production>, +q: Nat, +d: Nat, +k: Nat, +kk: Nat, +i: Nat,
  +e: {d == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}) -> {H.askAt(H.AskPop{Gll.lhsOf(grammar, q), k, i}, Core.Bsr{q, d, k, kk, i}, grammar) == True{} : Bool}:
  +len = {List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}
  +tail = {Bool.and(Nat.is_eq(d, len), Nat.is_eq(i, i)) : Bool}
  Lemma.and_true_intro(Nat.is_eq(Gll.lhsOf(grammar, q), Gll.lhsOf(grammar, q)), Bool.and(Nat.is_eq(k, k), tail), Lemma.nat_eq_refl(Gll.lhsOf(grammar, q)),
    Lemma.and_true_intro(Nat.is_eq(k, k), tail, Lemma.nat_eq_refl(k),
      Lemma.and_true_intro(Nat.is_eq(d, len), Nat.is_eq(i, i), eq_true(d, len, e), Lemma.nat_eq_refl(i))))

def last_pop(+grammar: +List<Core.Production>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +elen: {d == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  p: Ended(Steps(tree), q, k, d, i))
  -> {H.anyStep(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar) == True{} : Bool}:
  match p:
    case (+kk, mm):
      any_intro(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar, Core.Bsr{q, d, k, kk, i}, mm, pop_ask(grammar, q, d, k, kk, i, elen))

def end_last(+grammar: +List<Core.Production>, +tree: Core.Tree, +q: Nat, +e: Nat, +k: Nat, +i: Nat,
  +elen: {1n+e == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat}, last: Last(Steps(tree), q, k, 1n+e, i))
  -> {H.anyStep(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar) == True{} : Bool}:
  match last:
    case Inl{z}:
      Empty.absurd({H.anyStep(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar) == True{} : Bool}, B.succ_not_zero(e, z))
    case Inr{p}:
      last_pop(grammar, tree, q, 1n+e, k, i, elen, p)

# At the end of a right side: the pop and the step of an empty right side lie on the tree.
def end_dot(d: Nat, +grammar: +List<Core.Production>, +tree: Core.Tree, +q: Nat, +k: Nat, +i: Nat,
  +io: {Core.allIn(Core.own(q, [], d, k, i), Steps(tree)) == True{} : Bool},
  +inv: {Nat.add(d, 0n) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  last: Last(Steps(tree), q, k, d, i))
  -> {allOn(Sup.FPop{Gll.CKey{Gll.lhsOf(grammar, q), k}, i} <> Sup.emptyGives(d, q, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match d:
    case 0n:
      +hd = {Core.Bsr{q, 0n, k, i, i} : Core.Bsr}
      +mem = Lemma.and_true_left(Core.member(hd, Steps(tree)), True{}, io)
      Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar), Bool.and(Core.member(hd, Steps(tree)), True{}),
        any_intro(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar, hd, mem, pop_ask(grammar, q, 0n, k, i, i, inv)),
        Lemma.and_true_intro(Core.member(hd, Steps(tree)), True{}, mem, {==}))
    case 1n+(+e):
      +elen = Equal.trans(Nat, 1n+e, Nat.add(1n+e, 0n), List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), Equal.sym(Nat, Nat.add(1n+e, 0n), 1n+e, Lemma.add_zero_right(1n+e)), inv)
      Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskPop{Gll.lhsOf(grammar, q), k, i}, grammar), True{},
        end_last(grammar, tree, q, e, k, i, elen, last), {==})

def end_on(rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +rd: {Core.reads(rest, grammar, [], input, i) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, i), Steps(tree)) == True{} : Bool},
  +inv: {Nat.add(d, 0n) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  last: Last(Steps(tree), q, k, d, i))
  -> {allOn(Sup.FPop{Gll.CKey{Gll.lhsOf(grammar, q), k}, i} <> Sup.emptyGives(d, q, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match rest:
    case Nil{}:
      end_dot(d, grammar, tree, q, k, i, io, inv, last)
    case Con{Core.Leaf{+a}, +ts}:
      Empty.absurd({allOn(Sup.FPop{Gll.CKey{Gll.lhsOf(grammar, q), k}, i} <> Sup.emptyGives(d, q, k, i), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Node{+q2, +ch2}, +ts}:
      Empty.absurd({allOn(Sup.FPop{Gll.CKey{Gll.lhsOf(grammar, q), k}, i} <> Sup.emptyGives(d, q, k, i), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))

def member_end(+set: +List<Core.Bsr>, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +a: Nat,
  +m: {Core.member(Core.Bsr{q, 1n+d, k, i, Nat.add(i, Core.width(Core.Leaf{a}))}, set) == True{} : Bool}) -> {Core.member(Core.Bsr{q, 1n+d, k, i, 1n+i}, set) == True{} : Bool}:
  %Lemma.add_one_right(i) : {Core.member(Core.Bsr{q, 1n+d, k, i, _}, set) == True{} : Bool}
  m

def token_on(b: Bool, rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +t: Nat, +r: +List<Core.Sym>,
  +rd: {Core.reads(rest, grammar, Core.Terminal{t} <> r, input, i) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, i), Steps(tree)) == True{} : Bool})
  -> {allOn(Sup.tokenGives(b, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match b rest:
    case False{} +rs:
      {==}
    case True{} Con{Core.Leaf{+a}, +ts}:
      +hd = {Core.Bsr{q, 1n+d, k, i, Nat.add(i, Core.width(Core.Leaf{a}))} : Core.Bsr}
      +mem = member_end(Steps(tree), q, d, k, i, a, Lemma.and_true_left(Core.member(hd, Steps(tree)), Core.allIn(Core.own(q, ts, 1n+d, k, Nat.add(i, Core.width(Core.Leaf{a}))), Steps(tree)), io))
      +y = {Core.Bsr{q, 1n+d, k, i, 1n+i} : Core.Bsr}
      +ask = {H.AskDesc{q, 1n+d, k, 1n+i} : H.Ask}
      Lemma.and_true_intro(H.anyStep(Steps(tree), ask, grammar), Bool.and(Core.member(y, Steps(tree)), True{}),
        any_intro(Steps(tree), ask, grammar, y, mem, desc_ask(grammar, q, 1n+d, k, i, 1n+i)),
        Lemma.and_true_intro(Core.member(y, Steps(tree)), True{}, mem, {==}))
    case True{} Nil{}:
      Empty.absurd({allOn(Sup.tokenGives(True{}, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case True{} Con{Core.Node{+q2, +ch2}, +ts}:
      Empty.absurd({allOn(Sup.tokenGives(True{}, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))

# The first own step of a node of x at i: a step of a node of x at i lies on the tree.
def first_step(ch: +List<Core.Tree>, +grammar: +List<Core.Production>, +tree: Core.Tree, +q2: Nat, +x: Nat, +i: Nat,
  +io: {Core.allIn(Core.own(q2, ch, 0n, i, i), Steps(tree)) == True{} : Bool},
  +ok: {Bool.and(Nat.is_eq(Gll.lhsOf(grammar, q2), x), Nat.is_eq(i, i)) == True{} : Bool}) -> {H.anyStep(Steps(tree), H.AskCluster{x, i}, grammar) == True{} : Bool}:
  match ch:
    case Nil{}:
      +hd = {Core.Bsr{q2, 0n, i, i, i} : Core.Bsr}
      any_intro(Steps(tree), H.AskCluster{x, i}, grammar, hd, Lemma.and_true_left(Core.member(hd, Steps(tree)), True{}, io), ok)
    case Con{+t, +rest}:
      +hd = {Core.Bsr{q2, 1n, i, i, Nat.add(i, Core.width(t))} : Core.Bsr}
      any_intro(Steps(tree), H.AskCluster{x, i}, grammar, hd, Lemma.and_true_left(Core.member(hd, Steps(tree)), Core.allIn(Core.own(q2, rest, 1n, i, Nat.add(i, Core.width(t))), Steps(tree)), io), ok)

def own_first(+ch: +List<Core.Tree>, +grammar: +List<Core.Production>, +tree: Core.Tree, +q2: Nat, +x: Nat, +i: Nat,
  +io: {Core.allIn(Core.own(q2, ch, 0n, i, i), Steps(tree)) == True{} : Bool},
  +hx: {Gll.lhsOf(grammar, q2) == x : Nat}) -> {H.anyStep(Steps(tree), H.AskCluster{x, i}, grammar) == True{} : Bool}:
  first_step(ch, grammar, tree, q2, x, i, io,
    Lemma.and_true_intro(Nat.is_eq(Gll.lhsOf(grammar, q2), x), Nat.is_eq(i, i), eq_true(Gll.lhsOf(grammar, q2), x, hx), Lemma.nat_eq_refl(i)))

def nt_is(+grammar: +List<Core.Production>, +q: Nat, +d: Nat, +x: Nat, +need: Core.Need,
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>}) -> {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), Some{Core.Nonterminal{x, need}}, en) : {H.ntIs(_, x) == True{} : Bool}
  Lemma.nat_eq_refl(x)

def call_on(rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat, +x: Nat, +need: Core.Need, +r: +List<Core.Sym>,
  +rd: {Core.reads(rest, grammar, Core.Nonterminal{x, need} <> r, input, i) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, i), Steps(tree)) == True{} : Bool},
  +hf: {H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar) == True{} : Bool},
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{Core.Nonterminal{x, need}} : Maybe<&2, Core.Sym>})
  -> {allOn([Sup.FCluster{Gll.CKey{x, i}}, Sup.FRet{Gll.CKey{x, i}, Gll.Edge{q, d, k}}], grammar, Steps(tree)) == True{} : Bool}:
  match rest:
    case Con{Core.Node{+q2, +ch2}, +ts}:
      +w = Core.width(Core.Node{q2, ch2})
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, w)) : Bool}
      +own = {Bool.and(head, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, i)) : Bool}
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, q2, x), Core.needOk(need, w), Lemma.and_true_left(head, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, i), Lemma.and_true_left(own, Core.reads(ts, grammar, r, input, Nat.add(i, w)), rd)))
      +io2 = P.in_app_left(Core.own(q2, ch2, 0n, i, i), List.append(&2, Core.Bsr, Core.steps(ch2, i), Core.steps(ts, Nat.add(i, w))), Steps(tree), ist)
      +nt = {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) : Bool}
      +ret = {Bool.and(H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar), nt) : Bool}
      Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskCluster{x, i}, grammar), Bool.and(ret, True{}),
        own_first(ch2, grammar, tree, q2, x, i, io2, G.lhs_of(grammar, q2, x, hl)),
        Lemma.and_true_intro(ret, True{}, Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar), nt, hf, nt_is(grammar, q, d, x, need, en)), {==}))
    case Nil{}:
      Empty.absurd({allOn([Sup.FCluster{Gll.CKey{x, i}}, Sup.FRet{Gll.CKey{x, i}, Gll.Edge{q, d, k}}], grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Leaf{+a}, +ts}:
      Empty.absurd({allOn([Sup.FCluster{Gll.CKey{x, i}}, Sup.FRet{Gll.CKey{x, i}, Gll.Edge{q, d, k}}], grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))

def sym_on(s: Core.Sym, +r: +List<Core.Sym>, +rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +rd: {Core.reads(rest, grammar, s <> r, input, i) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, i), Steps(tree)) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, i), Steps(tree)) == True{} : Bool},
  +hf: {H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar) == True{} : Bool},
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{s} : Maybe<&2, Core.Sym>})
  -> {allOn(Sup.itemGives(Some{s}, grammar, input, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match s:
    case Core.Terminal{+t}:
      token_on(Core.tokIs(Core.tokAt(input, i), t), rest, grammar, input, tree, q, d, k, i, t, r, rd, io)
    case Core.Nonterminal{+x, +need}:
      call_on(rest, grammar, input, tree, q, d, k, i, x, need, r, rd, ist, hf, en)

def item_on(items: +List<Core.Sym>, +rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>},
  +rd: {Core.reads(rest, grammar, items, input, i) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, i), Steps(tree)) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, i), Steps(tree)) == True{} : Bool},
  +inv: {Nat.add(d, List.length(&2, Core.Sym, items)) == List.length(&2, Core.Sym, Core.rhsOf(grammar, q)) : Nat},
  last: Last(Steps(tree), q, k, d, i),
  +hf: {H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar) == True{} : Bool})
  -> {allOn(Sup.itemGives(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match items:
    case Nil{}:
      %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), None{}, G.nth_none(Core.rhsOf(grammar, q), d, ie)) : {allOn(Sup.itemGives(_, grammar, input, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}
      end_on(rest, grammar, input, tree, q, d, k, i, rd, io, inv, last)
    case Con{+s, +r}:
      %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), Some{s}, G.nth_drop(Core.rhsOf(grammar, q), d, s, r, ie)) : {allOn(Sup.itemGives(_, grammar, input, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}
      sym_on(s, r, rest, grammar, input, tree, q, d, k, i, rd, io, ist, hf, G.nth_drop(Core.rhsOf(grammar, q), d, s, r, ie))

def cursor_on(+grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +i: Nat,
  c: Cursor(grammar, input, Steps(tree), q, k, d, i),
  +hf: {H.anyStep(Steps(tree), H.AskDesc{q, d, k, i}, grammar) == True{} : Bool})
  -> {allOn(Sup.itemGives(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, q, d, k, i), grammar, Steps(tree)) == True{} : Bool}:
  match c:
    case (+rest, (+rd, (+io, (+ist, (+inv, last))))):
      item_on(G.dropFrom(d, Core.rhsOf(grammar, q)), rest, grammar, input, tree, q, d, k, i, {==}, rd, io, ist, inv, last, hf)

# A descriptor on the tree gives only facts on the tree.
law desc_on:
  for d: Gll.Desc
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +hf: {H.onTree(Sup.FDesc{d}, grammar, Steps(tree)) == True{} : Bool}
  {allOn(Sup.descGives(d, grammar, input), grammar, Steps(tree)) == True{} : Bool}

def desc_on(d, grammar, start, input, tree, rr, hf):
  match d:
    case Gll.Desc{+q, +dot, +k, +i}:
      cursor_on(grammar, input, tree, q, dot, k, i, cursor_of(grammar, start, input, tree, rr, q, dot, k, i, hf), hf)

# ======== THE SEEDS OF A CLUSTER ON THE TREE ========

def maybe_eq_of(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +h: {Gll.tokEq(a, b) == True{} : Bool}) -> {T.maybeEq(a, b) == True{} : Bool}:
  match a b:
    case None{} None{}:
      {==}
    case Some{+x} Some{+y}:
      h
    case None{} Some{+y}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Some{+x} None{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

def maybe_pick(+y: Maybe<&2, Nat>, +rest: +List<Maybe<&2, Nat>>, +n: Maybe<&2, Nat>,
  cases: Either<{Gll.tokEq(n, y) == True{} : Bool}, {Gll.tokIn(n, rest) == True{} : Bool}>,
  later: {Gll.tokIn(n, rest) == True{} : Bool} -> {T.maybeIn(n, rest) == True{} : Bool}) -> {T.maybeIn(n, y <> rest) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(T.maybeEq(n, y), T.maybeIn(n, rest), maybe_eq_of(n, y, e))
    case Inr{m}:
      Lemma.or_true_right_intro(T.maybeEq(n, y), T.maybeIn(n, rest), later(m))

# The engine's token set test is the tables' one.
law maybe_in_of:
  for xs: +List<Maybe<&2, Nat>>
  for +n: Maybe<&2, Nat>
  for +h: {Gll.tokIn(n, xs) == True{} : Bool}
  {T.maybeIn(n, xs) == True{} : Bool}

def maybe_in_of(xs, n, h):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      maybe_pick(y, rest, n, Lemma.or_true_cases(Gll.tokEq(n, y), Gll.tokIn(n, rest), h), m => maybe_in_of(rest, n, m))

# The LL(1) check, part by part.
def pairs_of(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}) -> {T.pairsOk(grammar, firsts, follows, nulls) == True{} : Bool}:
  +a1 = {Sets.nullsClosed(grammar, nulls) : Bool}
  +a2 = {T.firstsClosed(grammar, firsts, nulls) : Bool}
  +a3 = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
  +a4 = {T.followHas(start, None{}, follows) : Bool}
  +a5 = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
  +a6 = {T.pairsOk(grammar, firsts, follows, nulls) : Bool}
  +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +r4 = Lemma.and_true_right_side(a4, Bool.and(a5, a6), r3)
  Lemma.and_true_right_side(a5, a6, r4)

# The token is predicted for production q: by the closed tables.
def predicted(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}, +q: Nat, +next: Maybe<&2, Nat>, p: LL.Predicts(grammar, start, q, next))
  -> {T.maybeIn(next, PT.Pred(grammar, q, firsts, follows, nulls)) == True{} : Bool}:
  +a1 = {Sets.nullsClosed(grammar, nulls) : Bool}
  +a2 = {T.firstsClosed(grammar, firsts, nulls) : Bool}
  +a3 = {T.followsClosed(grammar, firsts, follows, nulls) : Bool}
  +a4 = {T.followHas(start, None{}, follows) : Bool}
  +a5 = {T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls) : Bool}
  +a6 = {T.pairsOk(grammar, firsts, follows, nulls) : Bool}
  +r1 = Lemma.and_true_right_side(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok)
  +r2 = Lemma.and_true_right_side(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1)
  +r3 = Lemma.and_true_right_side(a3, Bool.and(a4, Bool.and(a5, a6)), r2)
  +r4 = Lemma.and_true_right_side(a4, Bool.and(a5, a6), r3)
  PT.predicts_in(grammar, start, firsts, follows, nulls, q, next,
    Lemma.and_true_left(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6)))), ok),
    Lemma.and_true_left(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, a6))), r1),
    Lemma.and_true_left(a3, Bool.and(a4, Bool.and(a5, a6)), r2),
    Lemma.and_true_left(a4, Bool.and(a5, a6), r3),
    Lemma.and_true_left(a5, a6, r4), p)

def apart_no(+grammar: +List<Core.Production>, +q1: Nat, +q2: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +tok: Maybe<&2, Nat>,
  ap: PT.Apart(grammar, q1, q2, firsts, follows, nulls),
  +m1: {T.maybeIn(tok, PT.Pred(grammar, q1, firsts, follows, nulls)) == True{} : Bool},
  +m2: {T.maybeIn(tok, PT.Pred(grammar, q2, firsts, follows, nulls)) == True{} : Bool}) -> Empty:
  match ap:
    case Inl{d}:
      PT.disjoint_no(PT.Pred(grammar, q1, firsts, follows, nulls), PT.Pred(grammar, q2, firsts, follows, nulls), tok, d, m1, m2)
    case Inr{d}:
      PT.disjoint_no(PT.Pred(grammar, q2, firsts, follows, nulls), PT.Pred(grammar, q1, firsts, follows, nulls), tok, d, m2, m1)


def lhs_succ(+grammar: +List<Core.Production>, +base: Nat, +p: Nat, +x: Nat,
  +h: {Core.lhsIs(grammar, Nat.add(base, 1n+p), x) == True{} : Bool}) -> {Core.lhsIs(grammar, 1n+Nat.add(base, p), x) == True{} : Bool}:
  %Lemma.add_succ_right(base, p) : {Core.lhsIs(grammar, _, x) == True{} : Bool}
  h

def desc_same(+grammar: +List<Core.Production>, +tree: Core.Tree, +base: Nat, +q0: Nat, +i: Nat,
  +e: {base == q0 : Nat}, +hq0: {H.anyStep(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar) == True{} : Bool})
  -> {H.anyStep(Steps(tree), H.AskDesc{base, 0n, i, i}, grammar) == True{} : Bool}:
  %Equal.sym(Nat, base, q0, e) : {H.anyStep(Steps(tree), H.AskDesc{_, 0n, i, i}, grammar) == True{} : Bool}
  hq0

# A seed that gets past prediction: the tree's production, or the tables have a conflict.
def seed_here(+grammar: +List<Core.Production>, +start: Nat, +tree: Core.Tree, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}, +base: Nat, +q0: Nat, +x: Nat, +i: Nat, +tok: Maybe<&2, Nat>,
  +hb: {Core.lhsIs(grammar, base, x) == True{} : Bool},
  +lq0: {Core.lhsIs(grammar, q0, x) == True{} : Bool},
  +mb: {T.maybeIn(tok, PT.Pred(grammar, base, firsts, follows, nulls)) == True{} : Bool},
  +m0: {T.maybeIn(tok, PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool},
  +hq0: {H.anyStep(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar) == True{} : Bool},
  dec: Either<{base == q0 : Nat}, {Nat.is_eq(base, q0) == False{} : Bool}>)
  -> {H.anyStep(Steps(tree), H.AskDesc{base, 0n, i, i}, grammar) == True{} : Bool}:
  match dec:
    case Inl{e}:
      desc_same(grammar, tree, base, q0, i, e, hq0)
    case Inr{neq}:
      Empty.absurd({H.anyStep(Steps(tree), H.AskDesc{base, 0n, i, i}, grammar) == True{} : Bool},
        apart_no(grammar, base, q0, firsts, follows, nulls, tok, PT.pairs_at(grammar, base, q0, x, firsts, follows, nulls, pairs_of(grammar, start, nulls, firsts, follows, ok), hb, lq0, neq), mb, m0))

def admitted_in(+grammar: +List<Core.Production>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +base: Nat, +x: Nat, +tok: Maybe<&2, Nat>,
  +hb: {Core.lhsIs(grammar, base, x) == True{} : Bool},
  +ha: {Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, base, tok) == True{} : Bool})
  -> {T.maybeIn(tok, PT.Pred(grammar, base, firsts, follows, nulls)) == True{} : Bool}:
  +ti = {(%Pp.set_at(grammar, base, x, firsts, follows, nulls, hb) : {Gll.tokIn(tok, _) == True{} : Bool}
    ha) : {Gll.tokIn(tok, PT.Pred(grammar, base, firsts, follows, nulls)) == True{} : Bool}}
  maybe_in_of(PT.Pred(grammar, base, firsts, follows, nulls), tok, ti)

def seed_pick(a: Bool, b: Bool, +grammar: +List<Core.Production>, +start: Nat, +tree: Core.Tree, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}, +base: Nat, +q0: Nat, +x: Nat, +i: Nat, +tok: Maybe<&2, Nat>, +more: +List<Gll.Desc>,
  +ea: {a == Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, base, tok) : Bool},
  hbOf: {b == True{} : Bool} -> {Core.lhsIs(grammar, base, x) == True{} : Bool},
  +lq0: {Core.lhsIs(grammar, q0, x) == True{} : Bool},
  +m0: {T.maybeIn(tok, PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool},
  +hq0: {H.anyStep(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar) == True{} : Bool},
  +later: {allOn(Sup.descFacts(more), grammar, Steps(tree)) == True{} : Bool})
  -> {allOn(Sup.descFacts(Gll.keepDesc(Bool.and(a, b), Gll.Desc{base, 0n, i, i}, more)), grammar, Steps(tree)) == True{} : Bool}:
  match a b:
    case True{} True{}:
      +hb = hbOf({==})
      +mb = admitted_in(grammar, nulls, firsts, follows, base, x, tok, hb, Equal.sym(Bool, True{}, Gll.admits(Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, base, tok), ea))
      Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskDesc{base, 0n, i, i}, grammar), allOn(Sup.descFacts(more), grammar, Steps(tree)),
        seed_here(grammar, start, tree, nulls, firsts, follows, ok, base, q0, x, i, tok, hb, lq0, mb, m0, hq0, L.decide(Nat.is_eq(base, q0), base, q0, {==})), later)
    case True{} False{}:
      later
    case False{} True{}:
      later
    case False{} False{}:
      later








law seeds_on:
  for g: +List<Core.Production>
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +tree: Core.Tree
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +q0: Nat
  for +x: Nat
  for +i: Nat
  for +tok: Maybe<&2, Nat>
  for +hg: {G.dropProds(base, grammar) == g : +List<Core.Production>}
  for +lq0: {Core.lhsIs(grammar, q0, x) == True{} : Bool}
  for +m0: {T.maybeIn(tok, PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool}
  for +hq0: {H.anyStep(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar) == True{} : Bool}
  {allOn(Sup.descFacts(Gll.productionsOf(g, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, tok, x, base, i)), grammar, Steps(tree)) == True{} : Bool}

def seeds_on(g, base, grammar, start, tree, nulls, firsts, follows, ok, q0, x, i, tok, hg, lq0, m0, hq0):
  match g:
    case Nil{}:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest}:
      +pred = {Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)} : Gll.Pred}
      seed_pick(Gll.admits(pred, base, tok), Nat.is_eq(lhs, x), grammar, start, tree, nulls, firsts, follows, ok, base, q0, x, i, tok,
        Gll.productionsOf(rest, pred, tok, x, 1n+base, i), {==},
        hb => G.head_lhs(grammar, base, x, lhs, rhs, rest, hg, hb), lq0, m0, hq0,
        seeds_on(rest, 1n+base, grammar, start, tree, nulls, firsts, follows, ok, q0, x, i, tok, G.drop_step(base, grammar, lhs, rhs, rest, hg), lq0, m0, hq0))

def tok_moved(+grammar: +List<Core.Production>, +input: +List<Nat>, +q0: Nat, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>, +i0: Nat, +i: Nat,
  +ei: {i0 == i : Nat}, +h: {T.maybeIn(Core.tokAt(input, i0), PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool})
  -> {T.maybeIn(Core.tokAt(input, i), PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool}:
  %ei : {T.maybeIn(Core.tokAt(input, _), PT.Pred(grammar, q0, firsts, follows, nulls)) == True{} : Bool}
  h

def lhs_valid(+grammar: +List<Core.Production>, +q0: Nat, +x: Nat, +elx: {Gll.lhsOf(grammar, q0) == x : Nat},
  +valid: {Core.lhsIs(grammar, q0, Gll.lhsOf(grammar, q0)) == True{} : Bool}) -> {Core.lhsIs(grammar, q0, x) == True{} : Bool}:
  %elx : {Core.lhsIs(grammar, q0, _) == True{} : Bool}
  valid

def zero_ask(+grammar: +List<Core.Production>, +q0: Nat, +d0: Nat, +i0: Nat, +k0: Nat, +j0: Nat, +i: Nat,
  +ei: {Nat.is_eq(i0, i) == True{} : Bool}) -> {H.askAt(H.AskDesc{q0, 0n, i, i}, Core.Bsr{q0, d0, i0, k0, j0}, grammar) == True{} : Bool}:
  +zero = {Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(i, i)) : Bool}
  +either = {Bool.or(Bool.and(Nat.is_eq(d0, 0n), Nat.is_eq(j0, i)), zero) : Bool}
  Lemma.and_true_intro(Nat.is_eq(q0, q0), Bool.and(Nat.is_eq(i0, i), either), Lemma.nat_eq_refl(q0),
    Lemma.and_true_intro(Nat.is_eq(i0, i), either, ei,
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(d0, 0n), Nat.is_eq(j0, i)), zero, Lemma.and_true_intro(Nat.is_eq(0n, 0n), Nat.is_eq(i, i), {==}, Lemma.nat_eq_refl(i)))))

def cluster_node(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +x: Nat, +i: Nat, +q0: Nat, +i0: Nat, +y: Core.Bsr,
  +elx: {Gll.lhsOf(grammar, q0) == x : Nat}, +ei: {i0 == i : Nat},
  +hq0: {H.anyStep(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar) == True{} : Bool},
  node: NodeOf(grammar, input, Steps(tree), q0, i0, y))
  -> {allOn(Sup.descFacts(Gll.productionsOf(grammar, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, Core.tokAt(input, i), x, 0n, i)), grammar, Steps(tree)) == True{} : Bool}:
  match node:
    case (+ch, (+rc, (+io, (+ic, (my, valid))))):
      p = L.predicts_node(Core.leaves(ch), grammar, start, input, tree, rr, rl, q0, ch, i0, {==}, rc, io)
      +m0 = tok_moved(grammar, input, q0, firsts, follows, nulls, i0, i, ei, predicted(grammar, start, nulls, firsts, follows, ok, q0, Core.tokAt(input, i0), p))
      seeds_on(grammar, 0n, grammar, start, tree, nulls, firsts, follows, ok, q0, x, i, Core.tokAt(input, i), {==}, lhs_valid(grammar, q0, x, elx, valid), m0, hq0)

def cluster_found(y: Core.Bsr, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +x: Nat, +i: Nat,
  +m: {Core.member(y, Steps(tree)) == True{} : Bool},
  +a: {H.askAt(H.AskCluster{x, i}, y, grammar) == True{} : Bool})
  -> {allOn(Sup.descFacts(Gll.productionsOf(grammar, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, Core.tokAt(input, i), x, 0n, i)), grammar, Steps(tree)) == True{} : Bool}:
  match y:
    case Core.Bsr{+q0, +d0, +i0, +k0, +j0}:
      +hx = Lemma.and_true_left(Nat.is_eq(Gll.lhsOf(grammar, q0), x), Nat.is_eq(i0, i), a)
      +hi = Lemma.and_true_right_side(Nat.is_eq(Gll.lhsOf(grammar, q0), x), Nat.is_eq(i0, i), a)
      +y0 = {Core.Bsr{q0, d0, i0, k0, j0} : Core.Bsr}
      cluster_node(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, i, q0, i0, y0,
        Lemma.nat_eq_sound(Gll.lhsOf(grammar, q0), x, hx), Lemma.nat_eq_sound(i0, i, hi),
        any_intro(Steps(tree), H.AskDesc{q0, 0n, i, i}, grammar, y0, m, zero_ask(grammar, q0, d0, i0, k0, j0, i, hi)),
        node_in(grammar, start, input, tree, rr, y0, m))

def cluster_pick(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +x: Nat, +i: Nat, f: Found(Steps(tree), H.AskCluster{x, i}, grammar))
  -> {allOn(Sup.descFacts(Gll.productionsOf(grammar, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, Core.tokAt(input, i), x, 0n, i)), grammar, Steps(tree)) == True{} : Bool}:
  match f:
    case (+y, (+m, +a)):
      cluster_found(y, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, i, m, a)

# A cluster on the tree seeds only descriptors on the tree.
law cluster_on:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +x: Nat
  for +i: Nat
  for +hf: {H.anyStep(Steps(tree), H.AskCluster{x, i}, grammar) == True{} : Bool}
  {allOn(Sup.descFacts(Gll.productionsOf(grammar, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, Core.tokAt(input, i), x, 0n, i)), grammar, Steps(tree)) == True{} : Bool}

def cluster_on(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, i, hf):
  cluster_pick(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, i, any_elim(Steps(tree), H.AskCluster{x, i}, grammar, hf))

# ======== RESUMING AFTER A POP ON THE TREE ========

def node_reads(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ch: +List<Core.Tree>, +x: Nat, +k: Nat,
  +hl: {Core.lhsIs(grammar, q, x) == True{} : Bool},
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k) == True{} : Bool})
  -> {Core.reads([Core.Node{q, ch}], grammar, [Core.Nonterminal{x, Core.Anything{}}], input, k) == True{} : Bool}:
  +head = {Bool.and(Core.lhsIs(grammar, q, x), True{}) : Bool}
  Lemma.and_true_intro(Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)), True{},
    Lemma.and_true_intro(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), Lemma.and_true_intro(Core.lhsIs(grammar, q, x), True{}, hl, {==}), rc), {==})

def node_steps(+q: Nat, +ch: +List<Core.Tree>, +k: Nat, +set: +List<Core.Bsr>,
  +io: {Core.allIn(Core.own(q, ch, 0n, k, k), set) == True{} : Bool},
  +ic: {Core.allIn(Core.steps(ch, k), set) == True{} : Bool}) -> {Core.allIn(Core.steps([Core.Node{q, ch}], k), set) == True{} : Bool}:
  G.all_in_app(Core.own(q, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), []), set, io,
    G.all_in_app(Core.steps(ch, k), [], set, ic, {==}))

# The child of x at kc that the caller is waiting for ends where the pop of x at kc says:
# the tree has one node of x at kc (LL(1), `compare`).
def pop_node(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +x: Nat, +kc: Nat, +j: Nat, +q2: Nat, +ch2: +List<Core.Tree>,
  +r1: {Core.reads([Core.Node{q2, ch2}], grammar, [Core.Nonterminal{x, Core.Anything{}}], input, kc) == True{} : Bool},
  +in1: {Core.allIn(Core.steps([Core.Node{q2, ch2}], kc), Steps(tree)) == True{} : Bool},
  +q3: Nat, +d3: Nat, +i3: Nat, +k3: Nat, +j3: Nat,
  +elx: {Gll.lhsOf(grammar, q3) == x : Nat}, +ei: {i3 == kc : Nat},
  +ed: {d3 == List.length(&2, Core.Sym, Core.rhsOf(grammar, q3)) : Nat}, +ej: {j3 == j : Nat},
  node: NodeOf(grammar, input, Steps(tree), q3, i3, Core.Bsr{q3, d3, i3, k3, j3}))
  -> {Nat.add(kc, Core.width(Core.Node{q2, ch2})) == j : Nat}:
  match node:
    case (+ch3, (+rc3, (+io3, (+ic3, (my3, valid3))))):
      +S = Steps(tree)
      +nt = {[Core.Nonterminal{x, Core.Anything{}}] : +List<Core.Sym>}
      +n2 = {Core.Node{q2, ch2} : Core.Tree}
      +n3 = {Core.Node{q3, ch3} : Core.Tree}
      +ek = Equal.sym(Nat, i3, kc, ei)
      +r2 = reads_pos([n3], grammar, nt, input, kc, i3, ek, node_reads(grammar, input, q3, ch3, x, i3, lhs_valid(grammar, q3, x, elx, valid3), rc3))
      +in2 = steps_pos([n3], S, kc, i3, ek, node_steps(q3, ch3, i3, S, io3, ic3))
      +same = L.no_clash(grammar, start, n2, n3, L.compare([n2], [n3], nt, grammar, start, input, tree, tree, rr, rl, rr, rl, kc, r1, r2, in1, in2), ll1)
      +w2 = Core.width(n2)
      +w3 = Core.width(n3)
      +ew = Equal.cong(Core.Tree, Nat, v => Core.width(v), n2, n3, same)
      +xd = Equal.trans(Nat, d3, List.length(&2, Core.Sym, Core.rhsOf(grammar, q3)), List.length(&2, Core.Tree, ch3), ed,
        Equal.sym(Nat, List.length(&2, Core.Tree, ch3), List.length(&2, Core.Sym, Core.rhsOf(grammar, q3)), P.reads_length(ch3, Core.rhsOf(grammar, q3), grammar, input, i3, rc3)))
      +e4 = Equal.sym(Nat, j3, G.endOf(ch3, i3), PT.own_last(ch3, q3, 0n, i3, i3, Core.Bsr{q3, d3, i3, k3, j3}, my3, xd))
      Equal.trans(Nat, Nat.add(kc, w2), Nat.add(kc, w3), j, Equal.cong(Nat, Nat, v => Nat.add(kc, v), w2, w3, ew),
        Equal.trans(Nat, Nat.add(kc, w3), Nat.add(i3, w3), j, Equal.cong(Nat, Nat, v => Nat.add(v, w3), kc, i3, ek),
          Equal.trans(Nat, Nat.add(i3, w3), G.endOf(ch3, i3), j, Equal.sym(Nat, G.endOf(ch3, i3), Nat.add(i3, w3), G.end_node(q3, ch3, i3)),
            Equal.trans(Nat, G.endOf(ch3, i3), j3, j, e4, ej))))

def pop_found(y: Core.Bsr, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +x: Nat, +kc: Nat, +j: Nat, +q2: Nat, +ch2: +List<Core.Tree>,
  +r1: {Core.reads([Core.Node{q2, ch2}], grammar, [Core.Nonterminal{x, Core.Anything{}}], input, kc) == True{} : Bool},
  +in1: {Core.allIn(Core.steps([Core.Node{q2, ch2}], kc), Steps(tree)) == True{} : Bool},
  +m: {Core.member(y, Steps(tree)) == True{} : Bool},
  +a: {H.askAt(H.AskPop{x, kc, j}, y, grammar) == True{} : Bool})
  -> {Nat.add(kc, Core.width(Core.Node{q2, ch2})) == j : Nat}:
  match y:
    case Core.Bsr{+q3, +d3, +i3, +k3, +j3}:
      +len = {List.length(&2, Core.Sym, Core.rhsOf(grammar, q3)) : Nat}
      +t3 = {Bool.and(Nat.is_eq(d3, len), Nat.is_eq(j3, j)) : Bool}
      +t2 = {Bool.and(Nat.is_eq(i3, kc), t3) : Bool}
      +b1 = Lemma.and_true_right_side(Nat.is_eq(Gll.lhsOf(grammar, q3), x), t2, a)
      +b2 = Lemma.and_true_right_side(Nat.is_eq(i3, kc), t3, b1)
      pop_node(grammar, start, input, tree, rr, rl, ll1, x, kc, j, q2, ch2, r1, in1, q3, d3, i3, k3, j3,
        Lemma.nat_eq_sound(Gll.lhsOf(grammar, q3), x, Lemma.and_true_left(Nat.is_eq(Gll.lhsOf(grammar, q3), x), t2, a)),
        Lemma.nat_eq_sound(i3, kc, Lemma.and_true_left(Nat.is_eq(i3, kc), t3, b1)),
        Lemma.nat_eq_sound(d3, len, Lemma.and_true_left(Nat.is_eq(d3, len), Nat.is_eq(j3, j), b2)),
        Lemma.nat_eq_sound(j3, j, Lemma.and_true_right_side(Nat.is_eq(d3, len), Nat.is_eq(j3, j), b2)),
        node_in(grammar, start, input, tree, rr, Core.Bsr{q3, d3, i3, k3, j3}, m))

def pop_pick(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +x: Nat, +kc: Nat, +j: Nat, +q2: Nat, +ch2: +List<Core.Tree>,
  +r1: {Core.reads([Core.Node{q2, ch2}], grammar, [Core.Nonterminal{x, Core.Anything{}}], input, kc) == True{} : Bool},
  +in1: {Core.allIn(Core.steps([Core.Node{q2, ch2}], kc), Steps(tree)) == True{} : Bool},
  f: Found(Steps(tree), H.AskPop{x, kc, j}, grammar)) -> {Nat.add(kc, Core.width(Core.Node{q2, ch2})) == j : Nat}:
  match f:
    case (+y, (+m, +a)):
      pop_found(y, grammar, start, input, tree, rr, rl, ll1, x, kc, j, q2, ch2, r1, in1, m, a)

def resume_out(b: Bool, +grammar: +List<Core.Production>, +tree: Core.Tree, +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat,
  +mem: {Core.member(Core.Bsr{q, 1n+d, k, kc, j}, Steps(tree)) == True{} : Bool})
  -> {allOn(Sup.resumeOk(b, q, d, k, kc, j), grammar, Steps(tree)) == True{} : Bool}:
  match b:
    case True{}:
      +y = {Core.Bsr{q, 1n+d, k, kc, j} : Core.Bsr}
      +ask = {H.AskDesc{q, 1n+d, k, j} : H.Ask}
      Lemma.and_true_intro(H.anyStep(Steps(tree), ask, grammar), Bool.and(Core.member(y, Steps(tree)), True{}),
        any_intro(Steps(tree), ask, grammar, y, mem, desc_ask(grammar, q, 1n+d, k, kc, j)),
        Lemma.and_true_intro(Core.member(y, Steps(tree)), True{}, mem, {==}))
    case False{}:
      {==}

def lhs_to(+grammar: +List<Core.Production>, +q: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {Core.lhsIs(grammar, q, a) == True{} : Bool}) -> {Core.lhsIs(grammar, q, b) == True{} : Bool}:
  %e : {Core.lhsIs(grammar, q, _) == True{} : Bool}
  h

def member_to(+set: +List<Core.Bsr>, +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat},
  +h: {Core.member(Core.Bsr{q, d, k, kc, a}, set) == True{} : Bool}) -> {Core.member(Core.Bsr{q, d, k, kc, b}, set) == True{} : Bool}:
  %e : {Core.member(Core.Bsr{q, d, k, kc, _}, set) == True{} : Bool}
  h

def resume_child(rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat, +x: Nat, +x2: Nat, +need: Core.Need, +r: +List<Core.Sym>,
  +ex: {x2 == x : Nat},
  +rd: {Core.reads(rest, grammar, Core.Nonterminal{x2, need} <> r, input, kc) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, kc), Steps(tree)) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, kc), Steps(tree)) == True{} : Bool},
  hpop: {H.anyStep(Steps(tree), H.AskPop{x, kc, j}, grammar) == True{} : Bool})
  -> {allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}:
  match rest:
    case Con{Core.Node{+q2, +ch2}, +ts}:
      +S = Steps(tree)
      +w = Core.width(Core.Node{q2, ch2})
      +head = {Bool.and(Core.lhsIs(grammar, q2, x2), Core.needOk(need, w)) : Bool}
      +own = {Bool.and(head, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, kc)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, r, input, Nat.add(kc, w)), rd)
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, q2, x2), Core.needOk(need, w), Lemma.and_true_left(head, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, kc), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch2, grammar, Core.rhsOf(grammar, q2), input, kc), left)
      +io2 = P.in_app_left(Core.own(q2, ch2, 0n, kc, kc), List.append(&2, Core.Bsr, Core.steps(ch2, kc), Core.steps(ts, Nat.add(kc, w))), S, ist)
      +below = P.in_app_right(Core.own(q2, ch2, 0n, kc, kc), List.append(&2, Core.Bsr, Core.steps(ch2, kc), Core.steps(ts, Nat.add(kc, w))), S, ist)
      +ic2 = P.in_app_left(Core.steps(ch2, kc), Core.steps(ts, Nat.add(kc, w)), S, below)
      +r1 = node_reads(grammar, input, q2, ch2, x, kc, lhs_to(grammar, q2, x2, x, ex, hl), rc)
      +ej = pop_pick(grammar, start, input, tree, rr, rl, ll1, x, kc, j, q2, ch2, r1, node_steps(q2, ch2, kc, S, io2, ic2), any_elim(S, H.AskPop{x, kc, j}, grammar, hpop))
      +hd = {Core.Bsr{q, 1n+d, k, kc, Nat.add(kc, w)} : Core.Bsr}
      +hdIn = Lemma.and_true_left(Core.member(hd, S), Core.allIn(Core.own(q, ts, 1n+d, k, Nat.add(kc, w)), S), io)
      resume_out(Gll.needHolds(Gll.needAt(grammar, q, d), kc, j), grammar, tree, q, d, k, kc, j, member_to(S, q, 1n+d, k, kc, Nat.add(kc, w), j, ej, hdIn))
    case Nil{}:
      Empty.absurd({allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))
    case Con{Core.Leaf{+a}, +ts}:
      Empty.absurd({allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}, Lemma.false_is_not_true(rd))

# The caller's item is not x: no return edge of x was on the tree.
def not_nt(+grammar: +List<Core.Production>, +q: Nat, +d: Nat, +x: Nat, +item: Maybe<&2, Core.Sym>,
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == item : Maybe<&2, Core.Sym>},
  +hn: {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) == True{} : Bool}) -> {H.ntIs(item, x) == True{} : Bool}:
  Equal.trans(Bool, H.ntIs(item, x), H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x), True{},
    Equal.sym(Bool, H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x), H.ntIs(item, x), Equal.cong(Maybe<&2, Core.Sym>, Bool, v => H.ntIs(v, x), Gll.nthSym(Core.rhsOf(grammar, q), d), item, en)), hn)

def resume_sym(s: Core.Sym, +r: +List<Core.Sym>, +rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat, +x: Nat,
  +en: {Gll.nthSym(Core.rhsOf(grammar, q), d) == Some{s} : Maybe<&2, Core.Sym>},
  +hn: {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) == True{} : Bool},
  +rd: {Core.reads(rest, grammar, s <> r, input, kc) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, kc), Steps(tree)) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, kc), Steps(tree)) == True{} : Bool},
  hpop: {H.anyStep(Steps(tree), H.AskPop{x, kc, j}, grammar) == True{} : Bool})
  -> {allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}:
  match s:
    case Core.Nonterminal{+x2, +need}:
      +ex = Lemma.nat_eq_sound(x2, x, not_nt(grammar, q, d, x, Some{Core.Nonterminal{x2, need}}, en, hn))
      resume_child(rest, grammar, start, input, tree, rr, rl, ll1, q, d, k, kc, j, x, x2, need, r, ex, rd, io, ist, hpop)
    case Core.Terminal{+t}:
      Empty.absurd({allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool},
        Lemma.false_is_not_true(not_nt(grammar, q, d, x, Some{Core.Terminal{t}}, en, hn)))

def resume_items(items: +List<Core.Sym>, +rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat, +x: Nat,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>},
  +hn: {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) == True{} : Bool},
  +rd: {Core.reads(rest, grammar, items, input, kc) == True{} : Bool},
  +io: {Core.allIn(Core.own(q, rest, d, k, kc), Steps(tree)) == True{} : Bool},
  +ist: {Core.allIn(Core.steps(rest, kc), Steps(tree)) == True{} : Bool},
  hpop: {H.anyStep(Steps(tree), H.AskPop{x, kc, j}, grammar) == True{} : Bool})
  -> {allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}:
  match items:
    case Nil{}:
      Empty.absurd({allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool},
        Lemma.false_is_not_true(not_nt(grammar, q, d, x, None{}, G.nth_none(Core.rhsOf(grammar, q), d, ie), hn)))
    case Con{+s, +r}:
      resume_sym(s, r, rest, grammar, start, input, tree, rr, rl, ll1, q, d, k, kc, j, x, G.nth_drop(Core.rhsOf(grammar, q), d, s, r, ie), hn, rd, io, ist, hpop)

def resume_cursor(+grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  ll1: LL.LL1(grammar, start),
  +q: Nat, +d: Nat, +k: Nat, +kc: Nat, +j: Nat, +x: Nat,
  +hn: {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) == True{} : Bool},
  hpop: {H.anyStep(Steps(tree), H.AskPop{x, kc, j}, grammar) == True{} : Bool},
  c: Cursor(grammar, input, Steps(tree), q, k, d, kc))
  -> {allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}:
  match c:
    case (+rest, (+rd, (+io, (+ist, (+inv, last))))):
      resume_items(G.dropFrom(d, Core.rhsOf(grammar, q)), rest, grammar, start, input, tree, rr, rl, ll1, q, d, k, kc, j, x, {==}, hn, rd, io, ist, hpop)

# A return edge of x and a pop of x at kc, both on the tree, resume only on the tree.
law joined_on:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +x: Nat
  for +kc: Nat
  for +q: Nat
  for +d: Nat
  for +k: Nat
  for +j: Nat
  for +hret: {H.onTree(Sup.FRet{Gll.CKey{x, kc}, Gll.Edge{q, d, k}}, grammar, Steps(tree)) == True{} : Bool}
  for +hpop: {H.onTree(Sup.FPop{Gll.CKey{x, kc}, j}, grammar, Steps(tree)) == True{} : Bool}
  {allOn(Sup.resumeGives(Gll.Edge{q, d, k}, grammar, kc, j), grammar, Steps(tree)) == True{} : Bool}

def joined_on(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, kc, q, d, k, j, hret, hpop):
  +hd = {H.anyStep(Steps(tree), H.AskDesc{q, d, k, kc}, grammar) : Bool}
  +hn = {H.ntIs(Gll.nthSym(Core.rhsOf(grammar, q), d), x) : Bool}
  resume_cursor(grammar, start, input, tree, rr, rl, PT.sound_with(grammar, start, nulls, firsts, follows, ok), q, d, k, kc, j, x, Lemma.and_true_right_side(hd, hn, hret), hpop,
    cursor_of(grammar, start, input, tree, rr, q, d, k, kc, Lemma.and_true_left(hd, hn, hret)))

# ======== RETURN EDGES AND POPS AGAINST THE FACTS REACHED ========

law on_join:
  for a: +List<Sup.Fact>
  for +b: +List<Sup.Fact>
  for +grammar: +List<Core.Production>
  for +set: +List<Core.Bsr>
  for +ha: {allOn(a, grammar, set) == True{} : Bool}
  for +hb: {allOn(b, grammar, set) == True{} : Bool}
  {allOn(Sup.joinFacts(a, b), grammar, set) == True{} : Bool}

def on_join(a, b, grammar, set, ha, hb):
  match a:
    case Nil{}:
      hb
    case Con{+f, +rest}:
      +hf = {H.onTree(f, grammar, set) : Bool}
      Lemma.and_true_intro(hf, allOn(Sup.joinFacts(rest, b), grammar, set), Lemma.and_true_left(hf, allOn(rest, grammar, set), ha),
        on_join(rest, b, grammar, set, Lemma.and_true_right_side(hf, allOn(rest, grammar, set), ha), hb))

def on_if(b: Bool, +fs: +List<Sup.Fact>, +grammar: +List<Core.Production>, +set: +List<Core.Bsr>,
  hb: {b == True{} : Bool} -> {allOn(fs, grammar, set) == True{} : Bool}) -> {allOn(Sup.factsIf(b, fs), grammar, set) == True{} : Bool}:
  match b:
    case True{}:
      hb({==})
    case False{}:
      {==}

def joined_key(key: Gll.CKey, edge: Gll.Edge, +j: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +tree: Core.Tree,
  +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat},
  +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>,
  +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool},
  +hret: {H.onTree(Sup.FRet{key, edge}, grammar, Steps(tree)) == True{} : Bool},
  +hpop: {H.onTree(Sup.FPop{key, j}, grammar, Steps(tree)) == True{} : Bool})
  -> {allOn(Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), grammar, Steps(tree)) == True{} : Bool}:
  match key edge:
    case Gll.CKey{+x, +kc} Gll.Edge{+q, +d, +k}:
      joined_on(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, kc, q, d, k, j, hret, hpop)

def pop_moved(+grammar: +List<Core.Production>, +tree: Core.Tree, +key: Gll.CKey, +k2: Gll.CKey, +j: Nat, +e: {key == k2 : Gll.CKey},
  +h: {H.onTree(Sup.FPop{k2, j}, grammar, Steps(tree)) == True{} : Bool}) -> {H.onTree(Sup.FPop{key, j}, grammar, Steps(tree)) == True{} : Bool}:
  %Equal.sym(Gll.CKey, key, k2, e) : {H.onTree(Sup.FPop{_, j}, grammar, Steps(tree)) == True{} : Bool}
  h

def ret_moved(+grammar: +List<Core.Production>, +tree: Core.Tree, +key: Gll.CKey, +k2: Gll.CKey, +edge: Gll.Edge, +e: {key == k2 : Gll.CKey},
  +h: {H.onTree(Sup.FRet{k2, edge}, grammar, Steps(tree)) == True{} : Bool}) -> {H.onTree(Sup.FRet{key, edge}, grammar, Steps(tree)) == True{} : Bool}:
  %Equal.sym(Gll.CKey, key, k2, e) : {H.onTree(Sup.FRet{_, edge}, grammar, Steps(tree)) == True{} : Bool}
  h

law ret_on:
  for rs: +List<Sup.Fact>
  for +key: Gll.CKey
  for +edge: Gll.Edge
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +hret: {H.onTree(Sup.FRet{key, edge}, grammar, Steps(tree)) == True{} : Bool}
  for +hr: {allOn(rs, grammar, Steps(tree)) == True{} : Bool}
  {allOn(Sup.retGives(rs, grammar, key, edge), grammar, Steps(tree)) == True{} : Bool}

def ret_on(rs, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FPop{+k2, +j}, +rest}:
      +S = Steps(tree)
      +hp = {H.onTree(Sup.FPop{k2, j}, grammar, S) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      on_join(mine, Sup.retGives(rest, grammar, key, edge), grammar, S,
        on_if(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), grammar, S,
          eb => joined_key(key, edge, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret,
            pop_moved(grammar, tree, key, k2, j, G.key_eq_sound(key, k2, eb), Lemma.and_true_left(hp, allOn(rest, grammar, S), hr)))),
        ret_on(rest, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, Lemma.and_true_right_side(hp, allOn(rest, grammar, S), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      ret_on(rest, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, Lemma.and_true_right_side(H.onTree(Sup.FDesc{d}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      ret_on(rest, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, Lemma.and_true_right_side(H.onTree(Sup.FCluster{c}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FRet{+k2, +e2}, +rest}:
      ret_on(rest, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, Lemma.and_true_right_side(H.onTree(Sup.FRet{k2, e2}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FStep{+y}, +rest}:
      ret_on(rest, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hret, Lemma.and_true_right_side(H.onTree(Sup.FStep{y}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))

law pop_on:
  for rs: +List<Sup.Fact>
  for +key: Gll.CKey
  for +j: Nat
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +hpop: {H.onTree(Sup.FPop{key, j}, grammar, Steps(tree)) == True{} : Bool}
  for +hr: {allOn(rs, grammar, Steps(tree)) == True{} : Bool}
  {allOn(Sup.popGives(rs, grammar, key, j), grammar, Steps(tree)) == True{} : Bool}

def pop_on(rs, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, hr):
  match rs:
    case Nil{}:
      {==}
    case Con{Sup.FRet{+k2, +edge}, +rest}:
      +S = Steps(tree)
      +hrt = {H.onTree(Sup.FRet{k2, edge}, grammar, S) : Bool}
      +mine = Sup.factsIf(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j))
      on_join(mine, Sup.popGives(rest, grammar, key, j), grammar, S,
        on_if(Gll.keyEq(key, k2), Sup.resumeGives(edge, grammar, Sup.keyPos(key), j), grammar, S,
          eb => joined_key(key, edge, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok,
            ret_moved(grammar, tree, key, k2, edge, G.key_eq_sound(key, k2, eb), Lemma.and_true_left(hrt, allOn(rest, grammar, S), hr)), hpop)),
        pop_on(rest, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, Lemma.and_true_right_side(hrt, allOn(rest, grammar, S), hr)))
    case Con{Sup.FDesc{+d}, +rest}:
      pop_on(rest, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, Lemma.and_true_right_side(H.onTree(Sup.FDesc{d}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FCluster{+c}, +rest}:
      pop_on(rest, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, Lemma.and_true_right_side(H.onTree(Sup.FCluster{c}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FPop{+k2, +j2}, +rest}:
      pop_on(rest, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, Lemma.and_true_right_side(H.onTree(Sup.FPop{k2, j2}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))
    case Con{Sup.FStep{+y}, +rest}:
      pop_on(rest, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hpop, Lemma.and_true_right_side(H.onTree(Sup.FStep{y}, grammar, Steps(tree)), allOn(rest, grammar, Steps(tree)), hr))

# ======== EVERY RULE KEEPS THE TREE ========

law rule_on:
  for f: Sup.Fact
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +nulls: +List<Nat>
  for +firsts: +List<T.FirstFact>
  for +follows: +List<T.FollowFact>
  for +ok: {T.checkWith(grammar, start, nulls, firsts, follows) == True{} : Bool}
  for +reached: +List<Sup.Fact>
  for +hf: {H.onTree(f, grammar, Steps(tree)) == True{} : Bool}
  for +hr: {allOn(reached, grammar, Steps(tree)) == True{} : Bool}
  {allOn(Sup.factGives(f, Gll.Allowed{Pr.predictSets(grammar, firsts, follows, nulls)}, grammar, input, reached), grammar, Steps(tree)) == True{} : Bool}

def rule_on(f, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, reached, hf, hr):
  match f:
    case Sup.FDesc{+d}:
      desc_on(d, grammar, start, input, tree, rr, hf)
    case Sup.FCluster{Gll.CKey{+x, +i}}:
      cluster_on(grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, x, i, hf)
    case Sup.FRet{+key, +edge}:
      ret_on(reached, key, edge, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hf, hr)
    case Sup.FPop{+key, +j}:
      pop_on(reached, key, j, grammar, start, input, tree, rr, rl, nulls, firsts, follows, ok, hf, hr)
    case Sup.FStep{+y}:
      {==}

def root_node(t: Core.Tree, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>,
  +rr: {Core.reads([t], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool})
  -> {H.anyStep(Core.steps([t], 0n), H.AskCluster{start, 0n}, grammar) == True{} : Bool}:
  match t:
    case Core.Node{+q, +ch}:
      +w = Core.width(Core.Node{q, ch})
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)) : Bool}
      +hl = Lemma.and_true_left(Core.lhsIs(grammar, q, start), True{}, Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), Lemma.and_true_left(own, True{}, rr)))
      +all = L.all_in_refl(Core.steps([Core.Node{q, ch}], 0n))
      +io = P.in_app_left(Core.own(q, ch, 0n, 0n, 0n), List.append(&2, Core.Bsr, Core.steps(ch, 0n), Core.steps([], Nat.add(0n, w))), Core.steps([Core.Node{q, ch}], 0n), all)
      own_first(ch, grammar, Core.Node{q, ch}, q, start, 0n, io, G.lhs_of(grammar, q, start, hl))
    case Core.Leaf{+a}:
      Empty.absurd({H.anyStep(Core.steps([Core.Leaf{a}], 0n), H.AskCluster{start, 0n}, grammar) == True{} : Bool}, Lemma.false_is_not_true(rr))

# The root's cluster lies on the tree.
law root_on:
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +tree: Core.Tree
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  {allOn(Sup.roots(start), grammar, Steps(tree)) == True{} : Bool}

def root_on(grammar, start, input, tree, rr):
  Lemma.and_true_intro(H.anyStep(Steps(tree), H.AskCluster{start, 0n}, grammar), True{}, root_node(tree, grammar, start, input, rr), {==})
