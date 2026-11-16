import Base
import /Users/janwillem/Developer/Xcode/ApusApus/Bend/LEMMAS.bend as Lemma
import ./CORE_L0_walk.bend as C

# PHASE 1 ON THE CORE (measurement draft): lookahead, @left, @right.

# ---- The meaning ----

def Derives(+grammar: +List<C.Production>, +items: +List<C.Sym>, +w: +List<Nat>) -> Type:
  &forest: +List<C.Tree> -> {C.fits(forest, grammar, items) == True{} : Bool} & {C.leaves(forest) == w : +List<Nat>}

def DerivesAhead(+grammar: +List<C.Production>, +x: Nat, +ahead: +List<Nat>) -> Type:
  &pre: +List<Nat> -> &post: +List<Nat> -> {List.append(&2, Nat, pre, post) == ahead : +List<Nat>} & Derives(grammar, [C.Nonterminal{x}], pre)

def AllAhead(+grammar: +List<C.Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      DerivesAhead(grammar, x, ahead) & AllAhead(grammar, rest, ahead)

def NoneAhead(+grammar: +List<C.Production>, xs: +List<Nat>, +ahead: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      (DerivesAhead(grammar, x, ahead) -> Empty) & NoneAhead(grammar, rest, ahead)

def NoneDerive(+grammar: +List<C.Production>, xs: +List<Nat>, +w: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, rest}:
      (Derives(grammar, [C.Nonterminal{x}], w) -> Empty) & NoneDerive(grammar, rest, w)

# Bare: the production's own right side must not derive w; listed: no listed nonterminal may.
def EdgeOk(+grammar: +List<C.Production>, ids: +List<Nat>, +q: Nat, +w: +List<Nat>) -> Type:
  match ids:
    case Nil{}:
      Derives(grammar, C.rhsOf(grammar, q), w) -> Empty
    case Con{+x, +rest}:
      NoneDerive(grammar, x <> rest, w)

def lastOf(ts: +List<C.Tree>, +t: C.Tree) -> C.Tree:
  match ts:
    case Nil{}:
      t
    case Con{+u, us}:
      lastOf(us, u)

def EdgeFirst(+grammar: +List<C.Production>, +ids: +List<Nat>, +q: Nat, ch: +List<C.Tree>) -> Type:
  match ch:
    case Nil{}:
      Unit
    case Con{+t, ts}:
      EdgeOk(grammar, ids, q, C.leaves([t]))

def EdgeLast(+grammar: +List<C.Production>, +ids: +List<Nat>, +q: Nat, ch: +List<C.Tree>) -> Type:
  match ch:
    case Nil{}:
      Unit
    case Con{+t, +ts}:
      EdgeOk(grammar, ids, q, C.leaves([lastOf(ts, t)]))

type Guard is Data:
  Ahead{ids: +List<Nat>}
  NotAhead{ids: +List<Nat>}
  LeftAssoc{ids: +List<Nat>}
  RightAssoc{ids: +List<Nat>}

# On the core every rule sits on a production.
type GuardMark is Data:
  GuardMark{index: Nat, guard: Guard}

def Holds(+grammar: +List<C.Production>, g: Guard, +q: Nat, +ch: +List<C.Tree>, +ahead: +List<Nat>) -> Type:
  match g:
    case Ahead{+ids}:
      AllAhead(grammar, ids, ahead)
    case NotAhead{+ids}:
      NoneAhead(grammar, ids, ahead)
    case LeftAssoc{+ids}:
      EdgeLast(grammar, ids, q, ch)
    case RightAssoc{+ids}:
      EdgeFirst(grammar, ids, q, ch)

def AllHold(+grammar: +List<C.Production>, gs: +List<Guard>, +q: Nat, +ch: +List<C.Tree>, +ahead: +List<Nat>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{+g, rest}:
      Holds(grammar, g, q, ch, ahead) & AllHold(grammar, rest, q, ch, ahead)

def guardIf(hit: Bool, +g: Guard, +rest: +List<Guard>) -> +List<Guard>:
  match hit:
    case True{}:
      g <> rest
    case False{}:
      rest

def guardsOf(marks: +List<GuardMark>, +q: Nat) -> +List<Guard>:
  match marks:
    case Nil{}:
      []
    case Con{GuardMark{+p, +g}, rest}:
      guardIf(Nat.is_eq(p, q), g, guardsOf(rest, q))

type Ctx is Data:
  Ctx{grammar: +List<C.Production>, marks: +List<GuardMark>, input: +List<Nat>}

def ctxGrammar(c: Ctx) -> +List<C.Production>:
  match c:
    case Ctx{+g, m, i}:
      g

def ctxMarks(c: Ctx) -> +List<GuardMark>:
  match c:
    case Ctx{g, +m, i}:
      m

def ctxInput(c: Ctx) -> +List<Nat>:
  match c:
    case Ctx{g, m, +i}:
      i

# The rule of phase 1 for one node: all its rules hold, over the tokens from its start.
def Rules(+c: Ctx, +q: Nat, +ch: +List<C.Tree>, +k: Nat) -> Type:
  AllHold(ctxGrammar(c), guardsOf(ctxMarks(c), q), q, ch, Lemma.dropN(k, ctxInput(c)))

# ---- The oracle ----

type Tri is Data:
  Yes{}
  No{}
  Unknown{}

def andTri(a: Tri, b: Tri) -> Tri:
  match a b:
    case Yes{} _:
      b
    case No{} _:
      No{}
    case Unknown{} No{}:
      No{}
    case Unknown{} _:
      Unknown{}

def orTri(a: Tri, b: Tri) -> Tri:
  match a b:
    case Yes{} _:
      Yes{}
    case No{} _:
      b
    case Unknown{} Yes{}:
      Yes{}
    case Unknown{} _:
      Unknown{}

def notTri(a: Tri) -> Tri:
  match a:
    case Yes{}:
      No{}
    case No{}:
      Yes{}
    case Unknown{}:
      Unknown{}

# Does x derive some prefix of pre ++ post that starts with pre? Every split is tried.
def aheadOn(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, +grammar: +List<C.Production>, +x: Nat, post: +List<Nat>, +pre: +List<Nat>) -> Tri:
  match post:
    case Nil{}:
      dec(grammar, [C.Nonterminal{x}], pre)
    case Con{+t, +rest}:
      orTri(dec(grammar, [C.Nonterminal{x}], pre), aheadOn(~dec, grammar, x, rest, List.append(&2, Nat, pre, [t])))

def allAhead(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(aheadOn(~dec, grammar, x, ahead, []), allAhead(~dec, rest, grammar, ahead))

def noneAhead(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(aheadOn(~dec, grammar, x, ahead, [])), noneAhead(~dec, rest, grammar, ahead))

def noneDerive(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, xs: +List<Nat>, +grammar: +List<C.Production>, +w: +List<Nat>) -> Tri:
  match xs:
    case Nil{}:
      Yes{}
    case Con{+x, rest}:
      andTri(notTri(dec(grammar, [C.Nonterminal{x}], w)), noneDerive(~dec, rest, grammar, w))

def edgeOk(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, ids: +List<Nat>, +grammar: +List<C.Production>, +q: Nat, +w: +List<Nat>) -> Tri:
  match ids:
    case Nil{}:
      notTri(dec(grammar, C.rhsOf(grammar, q), w))
    case Con{+x, +rest}:
      noneDerive(~dec, x <> rest, grammar, w)

def only(here: Bool, t: Tri) -> Tri:
  match here:
    case True{}:
      t
    case False{}:
      Yes{}

# The rules a step of production q decides: the last step (dot = n) lookahead and @left,
# the first step (dot = 1) @right. Its edge child spans k .. j.
def guardAt(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, g: Guard, +grammar: +List<C.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match g:
    case Ahead{+ids}:
      only(Nat.is_eq(d, n), allAhead(~dec, ids, grammar, Lemma.dropN(i, input)))
    case NotAhead{+ids}:
      only(Nat.is_eq(d, n), noneAhead(~dec, ids, grammar, Lemma.dropN(i, input)))
    case LeftAssoc{+ids}:
      only(Bool.and(Nat.is_eq(d, n), Nat.is_lt(0n, n)), edgeOk(~dec, ids, grammar, q, Lemma.takeN(Nat.sub(j, k), Lemma.dropN(k, input))))
    case RightAssoc{+ids}:
      only(Nat.is_eq(d, 1n), edgeOk(~dec, ids, grammar, q, Lemma.takeN(Nat.sub(j, k), Lemma.dropN(k, input))))

def guardsAt(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, gs: +List<Guard>, +grammar: +List<C.Production>, +input: +List<Nat>, +q: Nat, +n: Nat, +d: Nat, +i: Nat, +k: Nat, +j: Nat) -> Tri:
  match gs:
    case Nil{}:
      Yes{}
    case Con{+g, rest}:
      andTri(guardAt(~dec, g, grammar, input, q, n, d, i, k, j), guardsAt(~dec, rest, grammar, input, q, n, d, i, k, j))

def stepTri(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri, +c: Ctx, e: C.Bsr) -> Tri:
  match e:
    case C.Bsr{+q, +d, +i, +k, +j}:
      guardsAt(~dec, guardsOf(ctxMarks(c), q), ctxGrammar(c), ctxInput(c), q, List.length(&2, C.Sym, C.rhsOf(ctxGrammar(c), q)), d, i, k, j)

# ---- Proofs: three-valued answers ----

def NotYesM(t: Tri) -> Type:
  match t:
    case Yes{}:
      Empty
    case No{}:
      Unit
    case Unknown{}:
      Unit

def NotNoM(t: Tri) -> Type:
  match t:
    case Yes{}:
      Unit
    case No{}:
      Empty
    case Unknown{}:
      Unit

law no_not_yes:
  for e: {No{} == Yes{} : Tri}
  Empty

def no_not_yes(e):
  %e : NotYesM(_)
  Unit{}

law unknown_not_yes:
  for e: {Unknown{} == Yes{} : Tri}
  Empty

def unknown_not_yes(e):
  %e : NotYesM(_)
  Unit{}

law yes_not_no:
  for e: {Yes{} == No{} : Tri}
  Empty

def yes_not_no(e):
  %e : NotNoM(_)
  Unit{}

law unknown_not_no:
  for e: {Unknown{} == No{} : Tri}
  Empty

def unknown_not_no(e):
  %e : NotNoM(_)
  Unit{}

law and_yes_left:
  for a: Tri
  for b: Tri
  for e: {andTri(a, b) == Yes{} : Tri}
  {a == Yes{} : Tri}

def and_yes_left(a, b, e):
  match a b:
    case Yes{} _:
      {==}
    case No{} _:
      Empty.absurd({No{} == Yes{} : Tri}, no_not_yes(e))
    case Unknown{} Yes{}:
      Empty.absurd({Unknown{} == Yes{} : Tri}, unknown_not_yes(e))
    case Unknown{} No{}:
      Empty.absurd({Unknown{} == Yes{} : Tri}, no_not_yes(e))
    case Unknown{} Unknown{}:
      Empty.absurd({Unknown{} == Yes{} : Tri}, unknown_not_yes(e))

law and_yes_right:
  for a: Tri
  for b: Tri
  for e: {andTri(a, b) == Yes{} : Tri}
  {b == Yes{} : Tri}

def and_yes_right(a, b, e):
  match a b:
    case Yes{} _:
      e
    case No{} _:
      Empty.absurd({b == Yes{} : Tri}, no_not_yes(e))
    case Unknown{} Yes{}:
      Empty.absurd({Yes{} == Yes{} : Tri}, unknown_not_yes(e))
    case Unknown{} No{}:
      Empty.absurd({No{} == Yes{} : Tri}, no_not_yes(e))
    case Unknown{} Unknown{}:
      Empty.absurd({Unknown{} == Yes{} : Tri}, unknown_not_yes(e))

law and_not_no:
  for a: Tri
  for b: Tri
  for na: {a == No{} : Tri} -> Empty
  for nb: {b == No{} : Tri} -> Empty
  for e: {andTri(a, b) == No{} : Tri}
  Empty

def and_not_no(a, b, na, nb, e):
  match a b:
    case Yes{} _:
      nb(e)
    case No{} _:
      na({==})
    case Unknown{} No{}:
      nb({==})
    case Unknown{} Yes{}:
      unknown_not_no(e)
    case Unknown{} Unknown{}:
      unknown_not_no(e)

law not_yes:
  for t: Tri
  for e: {notTri(t) == Yes{} : Tri}
  {t == No{} : Tri}

def not_yes(t, e):
  match t:
    case Yes{}:
      Empty.absurd({Yes{} == No{} : Tri}, no_not_yes(e))
    case No{}:
      {==}
    case Unknown{}:
      Empty.absurd({Unknown{} == No{} : Tri}, unknown_not_yes(e))

law not_no:
  for t: Tri
  for e: {notTri(t) == No{} : Tri}
  {t == Yes{} : Tri}

def not_no(t, e):
  match t:
    case Yes{}:
      {==}
    case No{}:
      Empty.absurd({No{} == Yes{} : Tri}, yes_not_no(e))
    case Unknown{}:
      Empty.absurd({Unknown{} == Yes{} : Tri}, unknown_not_no(e))

law or_yes:
  for a: Tri
  for b: Tri
  for e: {orTri(a, b) == Yes{} : Tri}
  Either<{a == Yes{} : Tri}, {b == Yes{} : Tri}>

def or_yes(a, b, e):
  match a b:
    case Yes{} _:
      Inl{{==}}
    case No{} _:
      Inr{e}
    case Unknown{} Yes{}:
      Inr{{==}}
    case Unknown{} No{}:
      Empty.absurd(Either<{Unknown{} == Yes{} : Tri}, {No{} == Yes{} : Tri}>, unknown_not_yes(e))
    case Unknown{} Unknown{}:
      Empty.absurd(Either<{Unknown{} == Yes{} : Tri}, {Unknown{} == Yes{} : Tri}>, unknown_not_yes(e))

law or_no_left:
  for a: Tri
  for b: Tri
  for e: {orTri(a, b) == No{} : Tri}
  {a == No{} : Tri}

def or_no_left(a, b, e):
  match a b:
    case Yes{} _:
      Empty.absurd({Yes{} == No{} : Tri}, yes_not_no(e))
    case No{} _:
      {==}
    case Unknown{} Yes{}:
      Empty.absurd({Unknown{} == No{} : Tri}, yes_not_no(e))
    case Unknown{} No{}:
      Empty.absurd({Unknown{} == No{} : Tri}, unknown_not_no(e))
    case Unknown{} Unknown{}:
      Empty.absurd({Unknown{} == No{} : Tri}, unknown_not_no(e))

law or_no_right:
  for a: Tri
  for b: Tri
  for e: {orTri(a, b) == No{} : Tri}
  {b == No{} : Tri}

def or_no_right(a, b, e):
  match a b:
    case Yes{} _:
      Empty.absurd({b == No{} : Tri}, yes_not_no(e))
    case No{} _:
      e
    case Unknown{} Yes{}:
      Empty.absurd({Yes{} == No{} : Tri}, yes_not_no(e))
    case Unknown{} No{}:
      Empty.absurd({No{} == No{} : Tri}, unknown_not_no(e))
    case Unknown{} Unknown{}:
      Empty.absurd({Unknown{} == No{} : Tri}, unknown_not_no(e))

# ---- Proofs: edge rules (@left, @right) ----
# The decider answers "do these items derive w?" with Yes, No or Unknown; decYes and decNo
# say its Yes and No are right (the checked sub-parse, proved elsewhere).

def nd_yes(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
           ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
           xs: +List<Nat>, +grammar: +List<C.Production>, +w: +List<Nat>, e: {noneDerive(~dec, xs, grammar, w) == Yes{} : Tri}) -> NoneDerive(grammar, xs, w):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +both = e
      +a = notTri(dec(grammar, [C.Nonterminal{x}], w))
      +b = noneDerive(~dec, rest, grammar, w)
      (d => decNo(grammar, [C.Nonterminal{x}], w, not_yes(dec(grammar, [C.Nonterminal{x}], w), and_yes_left(a, b, both)), d),
       nd_yes(~dec, ~decNo, rest, grammar, w, and_yes_right(a, b, both)))

def nd_no(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
          ~decYes: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == Yes{} : Tri} -> Derives(g, items, w),
          xs: +List<Nat>, +grammar: +List<C.Production>, +w: +List<Nat>, e: {noneDerive(~dec, xs, grammar, w) == No{} : Tri}, h: NoneDerive(grammar, xs, w)) -> Empty:
  match xs:
    case Nil{}:
      yes_not_no(e)
    case Con{+x, +rest}:
      match h:
        case (hx, hr):
          and_not_no(notTri(dec(grammar, [C.Nonterminal{x}], w)), noneDerive(~dec, rest, grammar, w),
            n => hx(decYes(grammar, [C.Nonterminal{x}], w, not_no(dec(grammar, [C.Nonterminal{x}], w), n))),
            n => nd_no(~dec, ~decYes, rest, grammar, w, n, hr),
            e)

def edge_yes(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
             ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
             ids: +List<Nat>, +grammar: +List<C.Production>, +q: Nat, +w: +List<Nat>, e: {edgeOk(~dec, ids, grammar, q, w) == Yes{} : Tri}) -> EdgeOk(grammar, ids, q, w):
  match ids:
    case Nil{}:
      d => decNo(grammar, C.rhsOf(grammar, q), w, not_yes(dec(grammar, C.rhsOf(grammar, q), w), e), d)
    case Con{+x, +rest}:
      nd_yes(~dec, ~decNo, x <> rest, grammar, w, e)

def edge_no(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
            ~decYes: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == Yes{} : Tri} -> Derives(g, items, w),
            ids: +List<Nat>, +grammar: +List<C.Production>, +q: Nat, +w: +List<Nat>, e: {edgeOk(~dec, ids, grammar, q, w) == No{} : Tri}, h: EdgeOk(grammar, ids, q, w)) -> Empty:
  match ids:
    case Nil{}:
      h(decYes(grammar, C.rhsOf(grammar, q), w, not_no(dec(grammar, C.rhsOf(grammar, q), w), e)))
    case Con{+x, +rest}:
      nd_no(~dec, ~decYes, x <> rest, grammar, w, e, h)

# ---- A decider that never knows, to instantiate the templates ----

def decUnknown(g: +List<C.Production>, items: +List<C.Sym>, w: +List<Nat>) -> Tri:
  Unknown{}

def decUnknownYes(g: +List<C.Production>, items: +List<C.Sym>, w: +List<Nat>, e: {decUnknown(g, items, w) == Yes{} : Tri}) -> Derives(g, items, w):
  Empty.absurd(Derives(g, items, w), unknown_not_yes(e))

def decUnknownNo(g: +List<C.Production>, items: +List<C.Sym>, w: +List<Nat>, e: {decUnknown(g, items, w) == No{} : Tri}, d: Derives(g, items, w)) -> Empty:
  unknown_not_no(e)

law inst_edge_yes:
  for ids: +List<Nat>
  for +grammar: +List<C.Production>
  for +q: Nat
  for +w: +List<Nat>
  for e: {edgeOk(~decUnknown, ids, grammar, q, w) == Yes{} : Tri}
  EdgeOk(grammar, ids, q, w)

def inst_edge_yes(ids, grammar, q, w, e):
  edge_yes(~decUnknown, ~decUnknownNo, ids, grammar, q, w, e)

law inst_edge_no:
  for ids: +List<Nat>
  for +grammar: +List<C.Production>
  for +q: Nat
  for +w: +List<Nat>
  for e: {edgeOk(~decUnknown, ids, grammar, q, w) == No{} : Tri}
  for h: EdgeOk(grammar, ids, q, w)
  Empty

def inst_edge_no(ids, grammar, q, w, e, h):
  edge_no(~decUnknown, ~decUnknownYes, ids, grammar, q, w, e, h)

# ---- Proofs: lookahead ----

law app_snoc:
  for +pre: +List<Nat>
  for +t: Nat
  for +rest: +List<Nat>
  {List.append(&2, Nat, List.append(&2, Nat, pre, [t]), rest) == List.append(&2, Nat, pre, t <> rest) : +List<Nat>}

def app_snoc(pre, t, rest):
  match pre:
    case Nil{}:
      {==}
    case Con{+h, +p}:
      %app_snoc(p, t, rest) : {h <> List.append(&2, Nat, List.append(&2, Nat, p, [t]), rest) == h <> _ : +List<Nat>}
      {==}

law app_nil_left:
  for m: +List<Nat>
  for -s: +List<Nat>
  for e: {List.append(&2, Nat, m, s) == [] : +List<Nat>}
  {m == [] : +List<Nat>}

def app_nil_left(m, s, e):
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Empty.absurd({h <> t == [] : +List<Nat>}, Lemma.nil_is_not_cons(h, List.append(&2, Nat, t, s), Equal.sym(+List<Nat>, h <> List.append(&2, Nat, t, s), [], e)))

def tailOf(l: +List<Nat>) -> +List<Nat>:
  match l:
    case Nil{}:
      []
    case Con{h, +t}:
      t

law cons_head:
  for -a: Nat
  for -x: +List<Nat>
  for -b: Nat
  for -y: +List<Nat>
  for e: {a <> x == b <> y : +List<Nat>}
  {a == b : Nat}

def cons_head(a, x, b, y, e):
  Equal.cong(+List<Nat>, Nat, l => Lemma.headOr(l, 0n), a <> x, b <> y, e)

law cons_tail:
  for -a: Nat
  for -x: +List<Nat>
  for -b: Nat
  for -y: +List<Nat>
  for e: {a <> x == b <> y : +List<Nat>}
  {x == y : +List<Nat>}

def cons_tail(a, x, b, y, e):
  Equal.cong(+List<Nat>, +List<Nat>, l => tailOf(l), a <> x, b <> y, e)

law derives_along:
  for +grammar: +List<C.Production>
  for +items: +List<C.Sym>
  for -a: +List<Nat>
  for -b: +List<Nat>
  for eq: {a == b : +List<Nat>}
  for d: Derives(grammar, items, a)
  Derives(grammar, items, b)

def derives_along(grammar, items, a, b, eq, d):
  %eq : Derives(grammar, items, _)
  d

law ahead_along:
  for +grammar: +List<C.Production>
  for +x: Nat
  for -a: +List<Nat>
  for -b: +List<Nat>
  for eq: {a == b : +List<Nat>}
  for d: DerivesAhead(grammar, x, a)
  DerivesAhead(grammar, x, b)

def ahead_along(grammar, x, a, b, eq, d):
  %eq : DerivesAhead(grammar, x, _)
  d

def ahead_pick(+grammar: +List<C.Production>, +x: Nat, +ahead: +List<Nat>, -A: Type, -B: Type,
               cases: Either<A, B>, here: A -> DerivesAhead(grammar, x, ahead), later: B -> DerivesAhead(grammar, x, ahead)) -> DerivesAhead(grammar, x, ahead):
  match cases:
    case Inl{a}:
      here(a)
    case Inr{b}:
      later(b)

# A Yes from the search is a split of the tokens whose first part x derives.
def ahead_yes(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
              ~decYes: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == Yes{} : Tri} -> Derives(g, items, w),
              +grammar: +List<C.Production>, +x: Nat, post: +List<Nat>, +pre: +List<Nat>, e: {aheadOn(~dec, grammar, x, post, pre) == Yes{} : Tri}) -> DerivesAhead(grammar, x, List.append(&2, Nat, pre, post)):
  match post:
    case Nil{}:
      (pre, ([], ({==}, decYes(grammar, [C.Nonterminal{x}], pre, e))))
    case Con{+t, +rest}:
      +ahead = List.append(&2, Nat, pre, t <> rest)
      ahead_pick(grammar, x, ahead, {dec(grammar, [C.Nonterminal{x}], pre) == Yes{} : Tri}, {aheadOn(~dec, grammar, x, rest, List.append(&2, Nat, pre, [t])) == Yes{} : Tri},
        or_yes(dec(grammar, [C.Nonterminal{x}], pre), aheadOn(~dec, grammar, x, rest, List.append(&2, Nat, pre, [t])), e),
        here => (pre, (t <> rest, ({==}, decYes(grammar, [C.Nonterminal{x}], pre, here)))),
        later => ahead_along(grammar, x, List.append(&2, Nat, List.append(&2, Nat, pre, [t]), rest), ahead, app_snoc(pre, t, rest),
          ahead_yes(~dec, ~decYes, grammar, x, rest, List.append(&2, Nat, pre, [t]), later)))

# A No from the search: no split m ++ s of the rest, after pre, gives x the tokens pre ++ m.
def ahead_no(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
             ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
             +grammar: +List<C.Production>, +x: Nat, post: +List<Nat>, +pre: +List<Nat>, e: {aheadOn(~dec, grammar, x, post, pre) == No{} : Tri},
             m: +List<Nat>, -s: +List<Nat>, sp: {List.append(&2, Nat, m, s) == post : +List<Nat>}, d: Derives(grammar, [C.Nonterminal{x}], List.append(&2, Nat, pre, m))) -> Empty:
  match post m:
    case Nil{} _:
      +mNil = app_nil_left(m, s, sp)
      decNo(grammar, [C.Nonterminal{x}], pre, e,
        derives_along(grammar, [C.Nonterminal{x}], List.append(&2, Nat, pre, m), pre,
          Equal.trans(+List<Nat>, List.append(&2, Nat, pre, m), List.append(&2, Nat, pre, []), pre,
            Lemma.append_congr(pre, m, pre, [], {==}, mNil), Lemma.append_nil_right(pre)), d))
    case Con{+t, +rest} Nil{}:
      decNo(grammar, [C.Nonterminal{x}], pre, or_no_left(dec(grammar, [C.Nonterminal{x}], pre), aheadOn(~dec, grammar, x, rest, List.append(&2, Nat, pre, [t])), e),
        derives_along(grammar, [C.Nonterminal{x}], List.append(&2, Nat, pre, []), pre, Lemma.append_nil_right(pre), d))
    case Con{+t, +rest} Con{+h, +m2}:
      +eLater = or_no_right(dec(grammar, [C.Nonterminal{x}], pre), aheadOn(~dec, grammar, x, rest, List.append(&2, Nat, pre, [t])), e)
      +spl = sp
      +ht = cons_head(h, List.append(&2, Nat, m2, s), t, rest, spl)
      +tl = cons_tail(h, List.append(&2, Nat, m2, s), t, rest, spl)
      +moved = Equal.trans(+List<Nat>, List.append(&2, Nat, pre, h <> m2), List.append(&2, Nat, pre, t <> m2), List.append(&2, Nat, List.append(&2, Nat, pre, [t]), m2),
        Lemma.append_congr(pre, h <> m2, pre, t <> m2, {==}, Equal.cong(Nat, +List<Nat>, v => v <> m2, h, t, ht)),
        Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, pre, [t]), m2), List.append(&2, Nat, pre, t <> m2), app_snoc(pre, t, m2)))
      ahead_no(~dec, ~decNo, grammar, x, rest, List.append(&2, Nat, pre, [t]), eLater, m2, s, tl,
        derives_along(grammar, [C.Nonterminal{x}], List.append(&2, Nat, pre, h <> m2), List.append(&2, Nat, List.append(&2, Nat, pre, [t]), m2), moved, d))

def ahead_no_at(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
                ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
                +grammar: +List<C.Production>, +x: Nat, +ahead: +List<Nat>, e: {aheadOn(~dec, grammar, x, ahead, []) == No{} : Tri}, hx: DerivesAhead(grammar, x, ahead)) -> Empty:
  match hx:
    case (pre, (post, (sp, d))):
      ahead_no(~dec, ~decNo, grammar, x, ahead, [], e, pre, post, sp, d)

def all_ahead_yes(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
                  ~decYes: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == Yes{} : Tri} -> Derives(g, items, w),
                  xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>, e: {allAhead(~dec, xs, grammar, ahead) == Yes{} : Tri}) -> AllAhead(grammar, xs, ahead):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +both = e
      +a = aheadOn(~dec, grammar, x, ahead, [])
      +b = allAhead(~dec, rest, grammar, ahead)
      (ahead_yes(~dec, ~decYes, grammar, x, ahead, [], and_yes_left(a, b, both)),
       all_ahead_yes(~dec, ~decYes, rest, grammar, ahead, and_yes_right(a, b, both)))

def all_ahead_no(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
                 ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
                 xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>, e: {allAhead(~dec, xs, grammar, ahead) == No{} : Tri}, h: AllAhead(grammar, xs, ahead)) -> Empty:
  match xs:
    case Nil{}:
      yes_not_no(e)
    case Con{+x, +rest}:
      match h:
        case (hx, hr):
          and_not_no(aheadOn(~dec, grammar, x, ahead, []), allAhead(~dec, rest, grammar, ahead),
            n => ahead_no_at(~dec, ~decNo, grammar, x, ahead, n, hx),
            n => all_ahead_no(~dec, ~decNo, rest, grammar, ahead, n, hr),
            e)

def none_ahead_yes(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
                   ~decNo: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == No{} : Tri} -> Derives(g, items, w) -> Empty,
                   xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>, e: {noneAhead(~dec, xs, grammar, ahead) == Yes{} : Tri}) -> NoneAhead(grammar, xs, ahead):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      +both = e
      +a = notTri(aheadOn(~dec, grammar, x, ahead, []))
      +b = noneAhead(~dec, rest, grammar, ahead)
      (hx => ahead_no_at(~dec, ~decNo, grammar, x, ahead, not_yes(aheadOn(~dec, grammar, x, ahead, []), and_yes_left(a, b, both)), hx),
       none_ahead_yes(~dec, ~decNo, rest, grammar, ahead, and_yes_right(a, b, both)))

def none_ahead_no(~dec: +List<C.Production> -> +List<C.Sym> -> +List<Nat> -> Tri,
                  ~decYes: @g:+List<C.Production> -> @items:+List<C.Sym> -> @w:+List<Nat> -> {dec(g, items, w) == Yes{} : Tri} -> Derives(g, items, w),
                  xs: +List<Nat>, +grammar: +List<C.Production>, +ahead: +List<Nat>, e: {noneAhead(~dec, xs, grammar, ahead) == No{} : Tri}, h: NoneAhead(grammar, xs, ahead)) -> Empty:
  match xs:
    case Nil{}:
      yes_not_no(e)
    case Con{+x, +rest}:
      match h:
        case (hx, hr):
          and_not_no(notTri(aheadOn(~dec, grammar, x, ahead, [])), noneAhead(~dec, rest, grammar, ahead),
            n => hx(ahead_yes(~dec, ~decYes, grammar, x, ahead, [], not_no(aheadOn(~dec, grammar, x, ahead, []), n))),
            n => none_ahead_no(~dec, ~decYes, rest, grammar, ahead, n, hr),
            e)

law inst_all_ahead_yes:
  for xs: +List<Nat>
  for +grammar: +List<C.Production>
  for +ahead: +List<Nat>
  for e: {allAhead(~decUnknown, xs, grammar, ahead) == Yes{} : Tri}
  AllAhead(grammar, xs, ahead)

def inst_all_ahead_yes(xs, grammar, ahead, e):
  all_ahead_yes(~decUnknown, ~decUnknownYes, xs, grammar, ahead, e)

law inst_all_ahead_no:
  for xs: +List<Nat>
  for +grammar: +List<C.Production>
  for +ahead: +List<Nat>
  for e: {allAhead(~decUnknown, xs, grammar, ahead) == No{} : Tri}
  for h: AllAhead(grammar, xs, ahead)
  Empty

def inst_all_ahead_no(xs, grammar, ahead, e, h):
  all_ahead_no(~decUnknown, ~decUnknownNo, xs, grammar, ahead, e, h)

law inst_none_ahead_yes:
  for xs: +List<Nat>
  for +grammar: +List<C.Production>
  for +ahead: +List<Nat>
  for e: {noneAhead(~decUnknown, xs, grammar, ahead) == Yes{} : Tri}
  NoneAhead(grammar, xs, ahead)

def inst_none_ahead_yes(xs, grammar, ahead, e):
  none_ahead_yes(~decUnknown, ~decUnknownNo, xs, grammar, ahead, e)

law inst_none_ahead_no:
  for xs: +List<Nat>
  for +grammar: +List<C.Production>
  for +ahead: +List<Nat>
  for e: {noneAhead(~decUnknown, xs, grammar, ahead) == No{} : Tri}
  for h: NoneAhead(grammar, xs, ahead)
  Empty

def inst_none_ahead_no(xs, grammar, ahead, e, h):
  none_ahead_no(~decUnknown, ~decUnknownYes, xs, grammar, ahead, e, h)
