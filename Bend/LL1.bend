import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./FIRST.bend as First

# LL(1) BY THE TABLES (not trusted: computed here; its law is `tables_ll1_sound`).
#
# At every choice point of the grammar (SPEC.bend, `ChoicePoint`), the predict sets of the
# choices, read from the tables of FIRST.bend, must not share a token (or both admit the end
# of the input). The tables contain the exact sets, so a grammar without conflicts here is
# LL(1) in SPEC.bend's sense; a conflict here may be one the exact sets do not have (from a
# place no sentence uses). The engine predicts with these tables, so this is also the
# engine's own view.

# Two choices at a choice point that the tables cannot tell apart.
type Conflict is Data:
  Conflict{point: Spec.ChoicePoint, first: Nat, second: Nat}

# Do two lookahead sets share a token, or both admit the end of the input? A set of
# everything shares with any set that is not empty.
def lsNonEmpty(s: Gll.LSet) -> Bool:
  match s:
    case Gll.LSet{any, tokens, end}:
      Bool.or(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))))

def tokensMeet(xs: +List<Nat>, +ys: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, rest}:
      Bool.or(Gll.natIn(x, ys), tokensMeet(rest, ys))

def lsMeet(+a: Gll.LSet, +b: Gll.LSet) -> Bool:
  match a b:
    case Gll.LSet{a1, t1, e1} Gll.LSet{a2, +t2, e2}:
      Bool.or(Bool.and(a1, lsNonEmpty(Gll.LSet{a2, t2, e2})), Bool.or(Bool.and(a2, lsNonEmpty(Gll.LSet{a1, t1, e1})), Bool.or(Bool.and(e1, e2), tokensMeet(t1, t2))))

# A choice: its number and its predict set.
type Predicted is Data:
  Predicted{choice: Nat, set: Gll.LSet}

def meetPick(meet: Bool, +point: Spec.ChoicePoint, +first: Nat, +second: Nat, +rest: +List<Conflict>) -> +List<Conflict>:
  match meet:
    case True{}:
      Conflict{point, first, second} <> rest
    case False{}:
      rest

# The conflicts of one choice with the choices after it.
def conflictsWith(+point: Spec.ChoicePoint, +choice: Predicted, others: +List<Predicted>) -> +List<Conflict>:
  match choice others:
    case _ Nil{}:
      []
    case Predicted{+c1, +s1} Con{Predicted{+c2, +s2}, rest}:
      meetPick(lsMeet(s1, s2), point, c1, c2, conflictsWith(point, Predicted{c1, s1}, rest))

def conflictsAmong(+point: Spec.ChoicePoint, choices: +List<Predicted>) -> +List<Conflict>:
  match choices:
    case Nil{}:
      []
    case Con{+choice, +rest}:
      List.append(&2, Conflict, conflictsWith(point, choice, rest), conflictsAmong(point, rest))

# ---- The choices at a nonterminal: its alternates, by production number ----

def alternatePick(own: Bool, +choice: Predicted, rest: +List<Predicted>) -> +List<Predicted>:
  match own:
    case True{}:
      choice <> rest
    case False{}:
      rest

def alternatesOf(prods: +List<Spec.Production>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat, +index: Nat) -> +List<Predicted>:
  match prods:
    case Nil{}:
      []
    case Con{Spec.Production{+lhs, rhs}, rest}:
      +later = alternatesOf(rest, grammar, t, x, 1n+index)
      alternatePick(Nat.is_eq(lhs, x), Predicted{index, Gll.predictAt(grammar, t, index, [], 0n)}, later)

def nonterminalConflicts(n: Nat, +grammar: +List<Spec.Production>, +t: Gll.Tables, +x: Nat) -> +List<Conflict>:
  match n:
    case 0n:
      []
    case 1n+m:
      List.append(&2, Conflict, conflictsAmong(Spec.NonterminalAt{x}, alternatesOf(grammar, grammar, t, x, 0n)), nonterminalConflicts(m, grammar, t, 1n+x))

# ---- The choices at a bracket: its alternates from 0, then leaving it ----

# An alternate's predict set: FIRST of the alternate, and, when its round may be empty, what
# may follow the round (Gll.predictAt of its first slot); otherwise FIRST alone.
def alternateSet(mayBeEmpty: Bool, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +alt: +List<Spec.Item>) -> Gll.LSet:
  match mayBeEmpty:
    case True{}:
      Gll.predictAt(grammar, t, index, rpath, 0n)
    case False{}:
      Gll.firstOf(Gll.infoItems(alt, t))

def bracketAlternates(alts: +List<+List<Spec.Item>>, +mayBeEmpty: Bool, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +a: Nat) -> +List<Predicted>:
  match alts:
    case Nil{}:
      []
    case Con{+alt, rest}:
      Predicted{a, alternateSet(mayBeEmpty, grammar, t, index, a <> rpath, alt)} <> bracketAlternates(rest, mayBeEmpty, grammar, t, index, rpath, 1n+a)

def leavePick(leave: Bool, +choice: Predicted) -> +List<Predicted>:
  match leave:
    case True{}:
      [choice]
    case False{}:
      []

def choicesWith(+mayBeEmpty: Bool, +leave: Bool, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>) -> +List<Predicted>:
  List.append(&2, Predicted, bracketAlternates(alts, mayBeEmpty, grammar, t, index, dot <> rpath, 0n),
    leavePick(leave, Predicted{List.length(&2, +List<Spec.Item>, alts), Gll.predictAt(grammar, t, index, rpath, 1n+dot)}))

# Entering a bracket (as in SPEC.bend's enterChoice).
def enterChoices(kind: Spec.Bracket, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>) -> +List<Predicted>:
  match kind:
    case Spec.Group{}:
      choicesWith(True{}, False{}, grammar, t, index, rpath, dot, alts)
    case Spec.Optional{}:
      choicesWith(False{}, True{}, grammar, t, index, rpath, dot, alts)
    case Spec.Closure{}:
      choicesWith(False{}, True{}, grammar, t, index, rpath, dot, alts)
    case Spec.Positive{}:
      choicesWith(True{}, False{}, grammar, t, index, rpath, dot, alts)

# After a round of < > (as in SPEC.bend's afterRoundChoice).
def afterRoundConflicts(kind: Spec.Bracket, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +alts: +List<+List<Spec.Item>>) -> +List<Conflict>:
  match kind:
    case Spec.Positive{}:
      conflictsAmong(Spec.AfterRoundAt{index, Gll.reverseOnto(rpath, []), dot}, choicesWith(False{}, True{}, grammar, t, index, rpath, dot, alts))
    case _:
      []

# Every bracket of the items, at any depth: its conflicts. The same two modes as
# `Gll.infoOf` (Bend has no mutual recursion); in MAlts, `dot` counts the alternatives.
# Running out of nesting fuel is reported as a conflict (choices 0 and 0): the check could
# not look further, so it must not say the grammar is LL(1).
def bracketConflicts(fuel: Nat, mode: Gll.Mode, items: +List<Spec.Item>, alts: +List<+List<Spec.Item>>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat) -> +List<Conflict>:
  match fuel mode items alts:
    case 0n _ _ _:
      [Conflict{Spec.BracketAt{index, Gll.reverseOnto(rpath, []), dot}, 0n, 0n}]
    case 1n+(+f) Gll.MItems{} Nil{} _:
      []
    case 1n+(+f) Gll.MItems{} Con{Spec.Brack{+kind, +inner}, rest} _:
      +point = {Spec.BracketAt{index, Gll.reverseOnto(rpath, []), dot} : Spec.ChoicePoint}
      List.append(&2, Conflict, conflictsAmong(point, enterChoices(kind, grammar, t, index, rpath, dot, inner)),
        List.append(&2, Conflict, afterRoundConflicts(kind, grammar, t, index, rpath, dot, inner),
        List.append(&2, Conflict, bracketConflicts(f, Gll.MAlts{}, [], inner, grammar, t, index, dot <> rpath, 0n),
          bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, rpath, 1n+dot))))
    case 1n+(+f) Gll.MItems{} Con{it, rest} _:
      bracketConflicts(1n+f, Gll.MItems{}, rest, alts, grammar, t, index, rpath, 1n+dot)
    case 1n+(+f) Gll.MAlts{} _ Nil{}:
      []
    case 1n+(+f) Gll.MAlts{} _ Con{alt, rest}:
      List.append(&2, Conflict, bracketConflicts(f, Gll.MItems{}, alt, [], grammar, t, index, dot <> rpath, 0n), bracketConflicts(1n+f, Gll.MAlts{}, items, rest, grammar, t, index, rpath, 1n+dot))

def productionConflicts(prods: +List<Spec.Production>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat) -> +List<Conflict>:
  match prods:
    case Nil{}:
      []
    case Con{Spec.Production{lhs, +rhs}, rest}:
      List.append(&2, Conflict, bracketConflicts(Gll.nestFuel(), Gll.MItems{}, rhs, [], grammar, t, index, [], 0n), productionConflicts(rest, grammar, t, 1n+index))

# All conflicts of the grammar by the tables: at every nonterminal, then at every bracket.
def conflictsOf(+grammar: +List<Spec.Production>, +t: Gll.Tables) -> +List<Conflict>:
  List.append(&2, Conflict, nonterminalConflicts(First.ntCount(grammar), grammar, t, 0n), productionConflicts(grammar, grammar, t, 0n))

# LL(1) by the tables: closed tables and no conflict.
def ll1ByTables(+grammar: +List<Spec.Production>, +start: Nat, +t: Gll.Tables) -> Bool:
  Bool.and(First.tablesClosed(grammar, start, t), List.is_empty(&2, Conflict, conflictsOf(grammar, t)))
