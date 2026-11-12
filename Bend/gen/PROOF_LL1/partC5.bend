
# ---- Brackets: the check visits every bracket ----

law nonempty_mid:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for +zs: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, List.append(&2, LL1.Conflict, ys, zs))) == False{} : Bool}

def nonempty_mid(xs, ys, zs, h):
  match xs:
    case Nil{}:
      nonempty_left(ys, zs, h)
    case Con{x, rest}:
      {==}

def altsOfItem(item: Maybe<&2, Spec.Item>) -> +List<+List<Spec.Item>>:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      alts
    case _:
      []

def isBrackItem(item: Maybe<&2, Spec.Item>) -> Bool:
  match item:
    case Some{Spec.Brack{kind, alts}}:
      True{}
    case _:
      False{}

# The local checks at item j of a sequence are among the sequence's checks.
law local_reach:
  for items: +List<Spec.Item>
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +f: Nat
  for +d0: Nat
  for +D: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +eD: {D == Nat.add(j, d0) : Nat}
  for +ne: {List.is_empty(&2, LL1.Conflict, localConflicts(Gll.nthItem(items, j), grammar, t, index, R0, D)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, items, alts, grammar, t, index, R0, d0)) == False{} : Bool}

def local_reach(items, j, alts, f, d0, D, grammar, t, index, R0, eD, ne):
  match items j:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, [], alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Brack{+k, +inn}, +rest} 0n:
      +here = {Some{Spec.Brack{k, inn}} : Maybe<&2, Spec.Item>}
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, d0)), List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, D)), False{},
        Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(here, grammar, t, index, R0, v)), d0, D, Equal.sym(Nat, D, d0, eD)), ne)
      nonempty_mid(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k, grammar, t, index, R0, d0, inn)), LL1.afterRoundConflicts(k, grammar, t, index, R0, d0, inn),
        List.append(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n), LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)), ne2)
    case Con{Spec.Sym{s}, rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Sym{s} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Eps{}, rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Brack{+k, +inn}, +rest} 1n+(+j2):
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)
      +afterC = LL1.afterRoundConflicts(k, grammar, t, index, R0, d0, inn)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k, grammar, t, index, R0, d0, inn)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_right(innerC, later,
          local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne))))
    case Con{Spec.Sym{+s}, +rest} 1n+(+j2):
      local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne)
    case Con{Spec.Eps{}, +rest} 1n+(+j2):
      local_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), ne)

# The checks inside the bracket at item j of a sequence are among the sequence's checks.
law inner_reach:
  for items: +List<Spec.Item>
  for j: Nat
  for +alts: +List<+List<Spec.Item>>
  for +f: Nat
  for +d0: Nat
  for +D: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +k: Spec.Bracket
  for +inn: +List<+List<Spec.Item>>
  for +eD: {D == Nat.add(j, d0) : Nat}
  for +itEq: {Gll.nthItem(items, j) == Some{Spec.Brack{k, inn}} : Maybe<&2, Spec.Item>}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, D <> R0, 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, items, alts, grammar, t, index, R0, d0)) == False{} : Bool}

def inner_reach(items, j, alts, f, d0, D, grammar, t, index, R0, k, inn, eD, itEq, ne):
  match items j:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, [], alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Brack{+k2, +inn2}, +rest} 0n:
      +innEq = Equal.cong(Maybe<&2, Spec.Item>, +List<+List<Spec.Item>>, v => altsOfItem(v), Some{Spec.Brack{k2, inn2}}, Some{Spec.Brack{k, inn}}, itEq)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn2, grammar, t, index, d0 <> R0, 0n)
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, innerC), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)), False{},
        Equal.cong(+List<+List<Spec.Item>>, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], v, grammar, t, index, d0 <> R0, 0n)), inn2, inn, innEq),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, d0 <> R0, 0n)), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, D <> R0, 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MAlts{}, [], inn, grammar, t, index, v <> R0, 0n)), d0, D, Equal.sym(Nat, D, d0, eD)), ne))
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +afterC = LL1.afterRoundConflicts(k2, grammar, t, index, R0, d0, inn2)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k2, grammar, t, index, R0, d0, inn2)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_left(innerC, later, ne2)))
    case Con{Spec.Sym{+s}, +rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Sym{s} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackItem(v), Some{Spec.Sym{s}}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Eps{}, +rest} 0n:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Spec.Eps{} <> rest, alts, grammar, t, index, R0, d0)) == False{} : Bool},
        Lemma.false_is_not_true(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => isBrackItem(v), Some{Spec.Eps{}}, Some{Spec.Brack{k, inn}}, itEq)))
    case Con{Spec.Brack{+k2, +inn2}, +rest} 1n+(+j2):
      +later = LL1.bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, R0, 1n+d0)
      +innerC = LL1.bracketConflicts(f, Gll.MAlts{}, [], inn2, grammar, t, index, d0 <> R0, 0n)
      +afterC = LL1.afterRoundConflicts(k2, grammar, t, index, R0, d0, inn2)
      nonempty_right(LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R0, []), d0}, LL1.enterChoices(k2, grammar, t, index, R0, d0, inn2)), List.append(&2, LL1.Conflict, afterC, List.append(&2, LL1.Conflict, innerC, later)),
        nonempty_right(afterC, List.append(&2, LL1.Conflict, innerC, later), nonempty_right(innerC, later,
          inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne))))
    case Con{Spec.Sym{+s}, +rest} 1n+(+j2):
      inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne)
    case Con{Spec.Eps{}, +rest} 1n+(+j2):
      inner_reach(rest, j2, alts, f, 1n+d0, D, grammar, t, index, R0, k, inn, Equal.trans(Nat, D, 1n+Nat.add(j2, d0), Nat.add(j2, 1n+d0), eD, Equal.sym(Nat, Nat.add(j2, 1n+d0), 1n+Nat.add(j2, d0), Lemma.add_succ_right(j2, d0))), itEq, ne)

# The checks in alternative c of a bracket are among the bracket's checks.
law alt_reach:
  for alts: +List<+List<Spec.Item>>
  for c: Nat
  for +f: Nat
  for +a0: Nat
  for +A: Nat
  for +items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +eA: {A == Nat.add(c, a0) : Nat}
  for isA: {Nat.is_lt(c, List.length(&2, +List<Spec.Item>, alts)) == True{} : Bool}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, Spec.altOf(alts, c), [], grammar, t, index, A <> R0, 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, alts, grammar, t, index, R0, a0)) == False{} : Bool}

def alt_reach(alts, c, f, a0, A, items, grammar, t, index, R0, eA, isA, ne):
  match alts c:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, [], grammar, t, index, R0, a0)) == False{} : Bool}, Lemma.lt_zero_false(c, isA))
    case Con{+alt, +rest} 0n:
      +here = LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, a0 <> R0, 0n)
      nonempty_left(here, LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, R0, 1n+a0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, A <> R0, 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, v <> R0, 0n)), a0, A, Equal.sym(Nat, A, a0, eA)), ne))
    case Con{+alt, +rest} 1n+(+c2):
      nonempty_right(LL1.bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, a0 <> R0, 0n), LL1.bracketConflicts(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, R0, 1n+a0),
        alt_reach(rest, c2, f, 1n+a0, A, items, grammar, t, index, R0, Equal.trans(Nat, A, 1n+Nat.add(c2, a0), Nat.add(c2, 1n+a0), eA, Equal.sym(Nat, Nat.add(c2, 1n+a0), 1n+Nat.add(c2, a0), Lemma.add_succ_right(c2, a0))), isA, ne))

law seq_in_nil:
  for p: +List<Nat>
  {Spec.sequenceIn(p, []) == [] : +List<Spec.Item>}

def seq_in_nil(p):
  match p:
    case Nil{}:
      {==}
    case Con{m, Nil{}}:
      {==}
    case Con{m, Con{a, rest}}:
      seq_in_nil(rest)

law alt_out:
  for alts: +List<+List<Spec.Item>>
  for a: Nat
  for e: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, alts)) == False{} : Bool}
  {Spec.altOf(alts, a) == [] : +List<Spec.Item>}

def alt_out(alts, a, e):
  match alts a:
    case Nil{} _:
      {==}
    case Con{alt, rest} 0n:
      Empty.absurd({alt == [] : +List<Spec.Item>}, Lemma.true_is_not_false(e))
    case Con{alt, rest} 1n+b:
      alt_out(rest, b, e)

def LocalAt(+rest: +List<Nat>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +R1: +List<Nat>, +dot: Nat) -> Data:
  {List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)) == False{} : Bool}

def LocateIH(+rest: +List<Nat>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +R1: +List<Nat>, +dot: Nat) -> Type:
  @fuel: Nat -> LocalAt(rest, grammar, t, index, R1, dot) -> {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(fuel, Gll.MItems{}, Gll.seqAt(grammar, index, R1), [], grammar, t, index, R1, 0n)) == False{} : Bool}

# A sequence named by no bracket's alternative has no checks to find.
law nowhere:
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R1: +List<Nat>
  for +dot: Nat
  for +goal: Bool
  for +nil: {Gll.seqAt(grammar, index, R1) == [] : +List<Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, R1, dot)
  {goal == False{} : Bool}

def nowhere(rest, grammar, t, index, R1, dot, goal, nil, ne):
  +nilIn = Equal.trans(+List<Spec.Item>, Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), Spec.sequenceIn(rest, []), [],
    Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Spec.sequenceIn(rest, v), Gll.seqAt(grammar, index, R1), [], nil), seq_in_nil(rest))
  Empty.absurd({goal == False{} : Bool}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), False{},
    Equal.sym(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), True{},
      Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(v, dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), [], nilIn)), ne)))

# One level down: the bracket at item m, alternative a, when a is an alternative of it.
law locate_alt:
  for b: Bool
  for f: Nat
  for +m: Nat
  for +a: Nat
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +k2: Spec.Bracket
  for +inn2: +List<+List<Spec.Item>>
  for +bEq: {Nat.is_lt(a, List.length(&2, +List<Spec.Item>, inn2)) == b : Bool}
  for +it2Eq: {Gll.nthItem(Gll.seqAt(grammar, index, R0), m) == Some{Spec.Brack{k2, inn2}} : Maybe<&2, Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, a <> (m <> R0), dot)
  for ih: LocateIH(rest, grammar, t, index, a <> (m <> R0), dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate_alt(b, f, m, a, rest, grammar, t, index, R0, dot, k2, inn2, bEq, it2Eq, ne, ih):
  match b f:
    case False{} _:
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, S, [], grammar, t, index, R0, 0n)),
        Equal.trans(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(S, m), a), Spec.altOf(inn2, a), [], altEq, alt_out(inn2, a, bEq)), ne)
    case True{} 0n:
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      inner_reach(S, m, [], 0n, 0n, m, grammar, t, index, R0, k2, inn2, Equal.sym(Nat, Nat.add(m, 0n), m, Lemma.add_zero_right(m)), it2Eq, {==})
    case True{} 1n+(+f2):
      +S = Gll.seqAt(grammar, index, R0)
      +altEq = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(S, m), Some{Spec.Brack{k2, inn2}}, it2Eq)
      +got = ih(f2, ne)
      +got2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, Spec.altOf(inn2, a), [], grammar, t, index, a <> (m <> R0), 0n)), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, Gll.bracketAlt(Gll.nthItem(S, m), a), [], grammar, t, index, a <> (m <> R0), 0n)), False{},
        Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(f2, Gll.MItems{}, v, [], grammar, t, index, a <> (m <> R0), 0n)), Spec.altOf(inn2, a), Gll.bracketAlt(Gll.nthItem(S, m), a), Equal.sym(+List<Spec.Item>, Gll.bracketAlt(Gll.nthItem(S, m), a), Spec.altOf(inn2, a), altEq)), got)
      inner_reach(S, m, [], 1n+f2, 0n, m, grammar, t, index, R0, k2, inn2, Equal.sym(Nat, Nat.add(m, 0n), m, Lemma.add_zero_right(m)), it2Eq,
        alt_reach(inn2, a, f2, 0n, a, [], grammar, t, index, m <> R0, Equal.sym(Nat, Nat.add(a, 0n), a, Lemma.add_zero_right(a)), bEq, got2))

# One level down: what item m of the sequence is.
law locate_step:
  for it2: Maybe<&2, Spec.Item>
  for f: Nat
  for +m: Nat
  for +a: Nat
  for +rest: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +it2Eq: {Gll.nthItem(Gll.seqAt(grammar, index, R0), m) == it2 : Maybe<&2, Spec.Item>}
  for +ne: LocalAt(rest, grammar, t, index, a <> (m <> R0), dot)
  for ih: LocateIH(rest, grammar, t, index, a <> (m <> R0), dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate_step(it2, f, m, a, rest, grammar, t, index, R0, dot, it2Eq, ne, ih):
  match it2:
    case Some{Spec.Brack{+k2, +inn2}}:
      locate_alt(Nat.is_lt(a, List.length(&2, +List<Spec.Item>, inn2)), f, m, a, rest, grammar, t, index, R0, dot, k2, inn2, {==}, it2Eq, ne, ih)
    case Some{Spec.Sym{+s}}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), Some{Spec.Sym{s}}, it2Eq), ne)
    case Some{Spec.Eps{}}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), Some{Spec.Eps{}}, it2Eq), ne)
    case None{}:
      nowhere(rest, grammar, t, index, a <> (m <> R0), dot, List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)),
        Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, R0), m), None{}, it2Eq), ne)

# The check visits the bracket named by the prefix, or runs out of nesting fuel on the way
# (which it reports as a conflict too).
law locate:
  for prem: +List<Nat>
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +index: Nat
  for +R0: +List<Nat>
  for +dot: Nat
  for +ne: LocalAt(prem, grammar, t, index, R0, dot)
  {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(fuel, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}

def locate(prem, fuel, grammar, t, index, R0, dot, ne):
  match prem fuel:
    case _ 0n:
      {==}
    case Nil{} 1n+(+f):
      +S = Gll.seqAt(grammar, index, R0)
      local_reach(S, dot, [], f, 0n, dot, grammar, t, index, R0, Equal.sym(Nat, Nat.add(dot, 0n), dot, Lemma.add_zero_right(dot)),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Gll.nthItem(S, dot), grammar, t, index, R0, dot)), List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(S, dot), grammar, t, index, R0, dot)), False{},
          Equal.cong(Maybe<&2, Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(v, grammar, t, index, R0, dot)), Gll.nthItem(S, dot), Spec.itemAt(S, dot), Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(S, dot), Gll.nthItem(S, dot), item_at_eq(S, dot))), ne))
    case Con{m, Nil{}} 1n+(+f):
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(1n+f, Gll.MItems{}, Gll.seqAt(grammar, index, R0), [], grammar, t, index, R0, 0n)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{+m, Con{+a, +rest}} 1n+(+f):
      +S = Gll.seqAt(grammar, index, R0)
      +R1 = {a <> (m <> R0) : +List<Nat>}
      +alt = Equal.trans(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.bracketAlt(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, R1),
        alternative_eq(Spec.itemAt(S, m), a), Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Spec.itemAt(S, m), Gll.nthItem(S, m), item_at_eq(S, m)))
      +ne2 = Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Gll.seqAt(grammar, index, R1)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)),
        List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, Spec.bracketAlternative(Spec.itemAt(S, m), a)), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), False{},
        Equal.cong(+List<Spec.Item>, Bool, v => List.is_empty(&2, LL1.Conflict, localConflicts(Spec.itemAt(Spec.sequenceIn(rest, v), dot), grammar, t, index, Gll.reverseOnto(rest, R1), dot)), Gll.seqAt(grammar, index, R1), Spec.bracketAlternative(Spec.itemAt(S, m), a),
          Equal.sym(+List<Spec.Item>, Spec.bracketAlternative(Spec.itemAt(S, m), a), Gll.seqAt(grammar, index, R1), alt)), ne)
      locate_step(Gll.nthItem(S, m), f, m, a, rest, grammar, t, index, R0, dot, {==}, ne2, (fx => nx => locate(rest, fx, grammar, t, index, a <> (m <> R0), dot, nx)))

# Every production is checked.
law prod_reach:
  for prods: +List<Spec.Production>
  for q: Nat
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +i0: Nat
  for +n: Nat
  for +e: {n == Nat.add(q, i0) : Nat}
  for +ne: {List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, Spec.rhsOf(prods, q), [], grammar, t, n, [], 0n)) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.productionConflicts(prods, grammar, t, i0)) == False{} : Bool}

def prod_reach(prods, q, grammar, t, i0, n, e, ne):
  match prods q:
    case Nil{} _:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.productionConflicts([], grammar, t, i0)) == False{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 0n:
      +here = LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, i0, [], 0n)
      nonempty_left(here, LL1.productionConflicts(rest, grammar, t, 1n+i0),
        Equal.trans(Bool, List.is_empty(&2, LL1.Conflict, here), List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, n, [], 0n)), False{},
          Equal.cong(Nat, Bool, v => List.is_empty(&2, LL1.Conflict, LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, v, [], 0n)), i0, n, Equal.sym(Nat, n, i0, e)), ne))
    case Con{Spec.Production{+lhs, +rhs}, +rest} 1n+(+q2):
      nonempty_right(LL1.bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, i0, [], 0n), LL1.productionConflicts(rest, grammar, t, 1n+i0),
        prod_reach(rest, q2, grammar, t, 1n+i0, n, Equal.trans(Nat, n, 1n+Nat.add(q2, i0), Nat.add(q2, 1n+i0), e, Equal.sym(Nat, Nat.add(q2, 1n+i0), 1n+Nat.add(q2, i0), Lemma.add_succ_right(q2, i0))), ne))

# ======== THE THEOREM ========

law ll1_point:
  for point: Spec.ChoicePoint
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
  for cp1: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, first), next)
  for cp2: Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, second), next)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)) == False{} : Bool}

def ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2):
  match point:
    case Spec.NonterminalAt{+x}:
      nonterminal_point(grammar, start, t, po, x, first, second, next, neq, cp1, cp2)
    case Spec.BracketAt{+index, +p, +dot}:
      +seq = Spec.sequenceAt(grammar, index, p)
      +local = enter_local(Spec.itemAt(seq, dot), grammar, start, t, po, index, p, dot, Spec.itemsFrom(1n+dot, seq), first, second, next, neq, {==}, {==}, cp1, cp2)
      nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
        prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), locate(p, Gll.nestFuel(), grammar, t, index, [], dot, local)))
    case Spec.AfterRoundAt{+index, +p, +dot}:
      +seq = Spec.sequenceAt(grammar, index, p)
      +local = after_local(Spec.itemAt(seq, dot), grammar, start, t, po, index, p, dot, Spec.itemsFrom(1n+dot, seq), first, second, next, neq, {==}, {==}, cp1, cp2)
      nonempty_right(LL1.nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), LL1.productionConflicts(grammar, grammar, t, 0n),
        prod_reach(grammar, index, grammar, t, 0n, index, Equal.sym(Nat, Nat.add(index, 0n), index, Lemma.add_zero_right(index)), locate(p, Gll.nestFuel(), grammar, t, index, [], dot, local)))

# LL(1) BY THE TABLES IS LL(1).
law tables_ll1_sound:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ok: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  Spec.LL1(grammar, start)

def tables_ll1_sound(grammar, start, t, ok):
  +closed = First.tablesClosed(grammar, start, t)
  +none = List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t))
  +po = Lemma.and_true_left(closed, none, ok)
  +noConflict = Lemma.and_true_right_side(closed, none, ok)
  point => first => second => next => neq => cp1 => cp2 =>
    Lemma.false_is_not_true(Equal.trans(Bool, False{}, none, True{}, Equal.sym(Bool, none, False{}, ll1_point(point, grammar, start, t, po, first, second, next, neq, cp1, cp2)), noConflict))
