
# ---- Nonterminals ----

law lt_succ_self:
  for x: Nat
  {Nat.is_lt(x, 1n+x) == True{} : Bool}

def lt_succ_self(x):
  match x:
    case 0n:
      {==}
    case 1n+y:
      lt_succ_self(y)

law lt_max_left:
  for x: Nat
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(x, a) == True{} : Bool}
  {Nat.is_lt(x, Nat.max(a, b)) == True{} : Bool}

def lt_max_left(x, a, b, h):
  match x a b:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(x, Nat.max(0n, b)) == True{} : Bool}, Lemma.lt_zero_false(x, h))
    case 0n 1n+c 0n:
      {==}
    case 0n 1n+c 1n+d:
      {==}
    case 1n+y 1n+c 0n:
      h
    case 1n+y 1n+c 1n+d:
      lt_max_left(y, c, d, h)

law lt_max_right:
  for x: Nat
  for a: Nat
  for b: Nat
  for h: {Nat.is_lt(x, b) == True{} : Bool}
  {Nat.is_lt(x, Nat.max(a, b)) == True{} : Bool}

def lt_max_right(x, a, b, h):
  match x a b:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(x, Nat.max(a, 0n)) == True{} : Bool}, Lemma.lt_zero_false(x, h))
    case 0n 0n 1n+d:
      {==}
    case 0n 1n+c 1n+d:
      {==}
    case 1n+y 0n 1n+d:
      h
    case 1n+y 1n+c 1n+d:
      lt_max_right(y, c, d, h)

# A nonterminal with an alternate is counted by ntCount.
law lhs_below:
  for grammar: +List<Spec.Production>
  for q: Nat
  for +x: Nat
  for e: {Spec.lhsIs(grammar, q, x) == True{} : Bool}
  {Nat.is_lt(x, First.ntCount(grammar)) == True{} : Bool}

def lhs_below(grammar, q, x, e):
  match grammar q:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(x, 0n) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{Spec.Production{+lhs, rhs}, +rest} 0n:
      +same = Lemma.nat_eq_sound(lhs, x, e)
      lt_max_left(x, 1n+lhs, First.ntCount(rest),
        Equal.trans(Bool, Nat.is_lt(x, 1n+lhs), Nat.is_lt(x, 1n+x), True{}, Equal.cong(Nat, Bool, v => Nat.is_lt(x, 1n+v), lhs, x, same), lt_succ_self(x)))
    case Con{Spec.Production{+lhs, rhs}, +rest} 1n+(+p):
      lt_max_right(x, 1n+lhs, First.ntCount(rest), lhs_below(rest, p, x, e))

# An alternate of a nonterminal that predicts the token: it is the nonterminal's, and the
# token is in the tables' predict set of its first slot.
law nt_alternate:
  for isOwn: Bool
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +q: Nat
  for +next: Maybe<&2, Nat>
  for cp: Spec.ChoicePredicts(grammar, start, Spec.nonterminalAlternate(isOwn, grammar, q), next)
  {isOwn == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, q, [], 0n)) == True{} : Bool}

def nt_alternate(isOwn, grammar, start, t, po, q, next, cp):
  match isOwn:
    case True{}:
      ({==}, predicts_sound(grammar, start, t, po, Spec.rhsOf(grammar, q), q, [], [], {==}, next, cp))
    case False{}:
      Empty.absurd(({False{} == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, q, [], 0n)) == True{} : Bool}), cp)

law pick_head:
  for own: Bool
  for +c: Nat
  for +i0: Nat
  for +s: Gll.LSet
  for +rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for e: {own == True{} : Bool}
  for +same: {c == i0 : Nat}
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  HasAt(c, next, LL1.alternatePick(own, LL1.Predicted{i0, s}, rest))

def pick_head(own, c, i0, s, rest, next, e, same, hs):
  match own:
    case True{}:
      Inl{(same, hs)}
    case False{}:
      Empty.absurd(HasAt(c, next, rest), Lemma.false_is_not_true(e))

law pick_tail:
  for own: Bool
  for +c: Nat
  for +choice: LL1.Predicted
  for +rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for h: HasAt(c, next, rest)
  HasAt(c, next, LL1.alternatePick(own, choice, rest))

def pick_tail(own, c, choice, rest, next, h):
  match own choice:
    case True{} LL1.Predicted{c2, s2}:
      Inr{h}
    case False{} _:
      h

# The alternate numbered c (production q of the list, counted from i0) is in the list.
law alternate_in:
  for prods: +List<Spec.Production>
  for q: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x: Nat
  for +i0: Nat
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for +e: {c == Nat.add(q, i0) : Nat}
  for own: {Spec.lhsIs(prods, q, x) == True{} : Bool}
  for +hs: {Gll.lsHas(next, Gll.predictAt(grammar, t, c, [], 0n)) == True{} : Bool}
  HasAt(c, next, LL1.alternatesOf(prods, grammar, t, x, i0))

def alternate_in(prods, q, grammar, t, x, i0, c, next, e, own, hs):
  match prods q:
    case Nil{} _:
      Empty.absurd(HasAt(c, next, []), Lemma.false_is_not_true(own))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      pick_head(Nat.is_eq(lhs, x), c, i0, Gll.predictAt(grammar, t, i0, [], 0n), LL1.alternatesOf(rest, grammar, t, x, 1n+i0), next, own, e,
        Equal.trans(Bool, Gll.lsHas(next, Gll.predictAt(grammar, t, i0, [], 0n)), Gll.lsHas(next, Gll.predictAt(grammar, t, c, [], 0n)), True{},
          Equal.cong(Nat, Bool, v => Gll.lsHas(next, Gll.predictAt(grammar, t, v, [], 0n)), i0, c, Equal.sym(Nat, c, i0, e)), hs))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+p):
      pick_tail(Nat.is_eq(lhs, x), c, LL1.Predicted{i0, Gll.predictAt(grammar, t, i0, [], 0n)}, LL1.alternatesOf(rest, grammar, t, x, 1n+i0), next,
        alternate_in(rest, p, grammar, t, x, 1n+i0, c, next, Equal.trans(Nat, c, 1n+Nat.add(p, i0), Nat.add(p, 1n+i0), e, Equal.sym(Nat, Nat.add(p, 1n+i0), 1n+Nat.add(p, i0), Lemma.add_succ_right(p, i0))), own, hs))

# The nonterminals x0 .. x0+n-1 are all checked.
law nt_cover:
  for n: Nat
  for d: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x0: Nat
  for +x: Nat
  for +e: {x == Nat.add(d, x0) : Nat}
  for lt: {Nat.is_lt(d, n) == True{} : Bool}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n))) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.nonterminalConflicts(n, grammar, t, x0)) == False{} : Bool}

def nt_cover(n, d, grammar, t, x0, x, e, lt, ne):
  match n d:
    case 0n _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.nonterminalConflicts(0n, grammar, t, x0)) == False{} : Bool}, Lemma.lt_zero_false(d, lt))
    case 1n+m 0n:
      +here = LL1.conflictsAmong(Spec.NonterminalAt{x0}, LL1.alternatesOf(grammar, grammar, t, x0, 0n))
      nonempty_left(here, LL1.nonterminalConflicts(m, grammar, t, 1n+x0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n))), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(Spec.NonterminalAt{v}, LL1.alternatesOf(grammar, grammar, t, v, 0n))), x0, x, Equal.sym(Nat, x, x0, e)), ne))
    case 1n+(+m) 1n+(+d2):
      nonempty_right(LL1.conflictsAmong(Spec.NonterminalAt{x0}, LL1.alternatesOf(grammar, grammar, t, x0, 0n)), LL1.nonterminalConflicts(m, grammar, t, 1n+x0),
        nt_cover(m, d2, grammar, t, 1n+x0, x, Equal.trans(Nat, x, 1n+Nat.add(d2, x0), Nat.add(d2, 1n+x0), e, Equal.sym(Nat, Nat.add(d2, 1n+x0), 1n+Nat.add(d2, x0), Lemma.add_succ_right(d2, x0))), lt, ne))

law nonterminal_hits:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +x: Nat
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for p1: {Spec.lhsIs(grammar, first, x) == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, first, [], 0n)) == True{} : Bool}
  for p2: {Spec.lhsIs(grammar, second, x) == True{} : Bool} & {Gll.lsHas(next, Gll.predictAt(grammar, t, second, [], 0n)) == True{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def nonterminal_hits(grammar, t, x, first, second, next, neq, p1, p2):
  match p1:
    case (own0, hs1):
      match p2:
        case (own2, hs2):
          +own1 = {own0 : {Spec.lhsIs(grammar, first, x) == True{} : Bool}}
          h1 = alternate_in(grammar, first, grammar, t, x, 0n, first, next, Equal.sym(Nat, Nat.add(first, 0n), first, Lemma.add_zero_right(first)), own1, hs1)
          h2 = alternate_in(grammar, second, grammar, t, x, 0n, second, next, Equal.sym(Nat, Nat.add(second, 0n), second, Lemma.add_zero_right(second)), own2, hs2)
          nonempty_left(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
            nt_cover(First.ntCount(grammar), x, grammar, t, 0n, x, Equal.sym(Nat, Nat.add(x, 0n), x, Lemma.add_zero_right(x)), lhs_below(grammar, first, x, own1),
              among_hit(Spec.NonterminalAt{x}, LL1.alternatesOf(grammar, grammar, t, x, 0n), first, second, next, neq, h1, h2)))

# Two alternates of a nonterminal that predict the same token: the check reports it.
law nonterminal_point:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +x: Nat
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.NonterminalAt{x}, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, Spec.NonterminalAt{x}, second), next)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def nonterminal_point(grammar, start, t, po, x, first, second, next, neq, cp1, cp2):
  nonterminal_hits(grammar, t, x, first, second, next, neq,
    nt_alternate(Spec.lhsIs(grammar, first, x), grammar, start, t, po, first, next, cp1),
    nt_alternate(Spec.lhsIs(grammar, second, x), grammar, start, t, po, second, next, cp2))
