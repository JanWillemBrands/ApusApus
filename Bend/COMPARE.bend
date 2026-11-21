import Base
import ./SYNTAX.bend as Spec
import ./CORE.bend as Core
import ./EBNF.bend as E
import ./GLL.bend as Gll
import ./RUN.bend as Run
import ./EXACT.bend as Exact
import ./GUARD.bend as Guard
import ./PREFER.bend as Prefer
import ./EXTENT.bend as Ext

# COMPARING SWIFT APUS WITH THE CORE. The files in ../swift/ are written by
# ApusApusTests/BendExport.swift: a grammar as written, its marks, an input, and the BSR
# elements Swift Apus computed for it, all in SYNTAX.bend's syntax. `report` translates the
# grammar and the marks to the core (towards Swift, EBNF.bend), runs the core's parser or
# oracle, maps its steps back to Swift's slots and puts them next to Swift's.
#
#   Agree{n}                  Swift has exactly the n steps of the core's set
#   Differ{e, s, miss, extra} the core's set has e steps, Swift s; `miss` are steps of a
#                             tree the core keeps that Swift lacks, `extra` are Swift's
#                             steps that are on no such tree (dead wood)
#   NoAnswer{}                the core gave no answer
#
# Each set is exactly the steps of its trees: the parse trees (`gll_bsr_exact`), the
# admissible ones (phase 1) and the chosen ones (phases 1 and 2): the oracle's set without
# dead wood (`chosenSteps`, `extent_exact`), and the selected ones (phase 3). The selecting
# oracle's set embeds exactly the selected trees (`extent_exact`) but keeps the other steps
# of a reading that is out, so its dead wood is dropped the same way (`liveFrom`, checked by
# `coverFrom`): each step kept lies on a parse tree inside the set, that is a selected one.
# Every answer is right whatever the fuel, so the report
# tries a small fuel first and doubles it while there is no answer, ending with the fuel
# with which each is proven to answer (`exact_parser_answers`, `chosen_answers`,
# `extent_answers`): NoAnswer does not happen. (The loops stop when they are done, but
# a smaller fuel still runs faster on large grammars.)
type Report is Data:
  Agree{count: Nat}
  Differ{exact: Nat, swift: Nat, missing: +List<Spec.Bsr>, extra: +List<Spec.Bsr>}
  NoAnswer{}

def keepOut(inside: Bool, +x: Spec.Bsr, xs: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match inside:
    case True{}:
      xs
    case False{}:
      x <> xs

# The elements of xs that are not in ys.
def notIn(xs: +List<Spec.Bsr>, +ys: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      keepOut(Spec.bsrMember(x, ys), x, notIn(rest, ys))

# Each element once: two core steps may map to the same slot.
def distinct(xs: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      keepOut(Spec.bsrMember(x, rest), x, distinct(rest))

def pickIf(same: Bool, +exact: +List<Spec.Bsr>, +swift: +List<Spec.Bsr>, +missing: +List<Spec.Bsr>, +extra: +List<Spec.Bsr>) -> Report:
  match same:
    case True{}:
      Agree{List.length(&2, Spec.Bsr, exact)}
    case False{}:
      Differ{List.length(&2, Spec.Bsr, exact), List.length(&2, Spec.Bsr, swift), missing, extra}

def pick(+exact: +List<Spec.Bsr>, +swift: +List<Spec.Bsr>, +missing: +List<Spec.Bsr>, +extra: +List<Spec.Bsr>) -> Report:
  pickIf(Bool.and(List.is_empty(&2, Spec.Bsr, missing), List.is_empty(&2, Spec.Bsr, extra)), exact, swift, missing, extra)

def compareTo(+exact: +List<Spec.Bsr>, +swift: +List<Spec.Bsr>) -> Report:
  pick(exact, swift, notIn(exact, swift), notIn(swift, exact))

# The core's set mapped to Swift's slots, next to Swift's.
def reportOf(found: Maybe<&2, +List<Core.Bsr>>, +origins: +List<E.Origin>, +swift: +List<Spec.Bsr>) -> Report:
  match found:
    case Some{+set}:
      compareTo(distinct(E.stepsToSwift(origins, set)), swift)
    case None{}:
      NoAnswer{}

# 1 + twice the size of the descriptor universe.
def fuel(+grammar: +List<Core.Production>, +input: +List<Nat>) -> Nat:
  1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input)))

# Which set of the core a report compares with.
type Target is Data:
  Exact{}
  Chosen{gmarks: +List<Guard.GuardMark>, rmarks: +List<Prefer.RankMark>}
  Selected{gmarks: +List<Guard.GuardMark>, rmarks: +List<Prefer.RankMark>, emarks: +List<Ext.ExtentMark>}

def runWith(target: Target, +f: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match target:
    case Exact{}:
      Exact.exactSteps(f, grammar, start, input)
    case Chosen{+gm, +rm}:
      Ext.chosenSteps(f, grammar, gm, rm, start, input)
    case Selected{+gm, +rm, +em}:
      Ext.coverFrom(Ext.liveFrom(Ext.selectedSteps(f, grammar, gm, rm, em, start, input), f, grammar, start, input), f, grammar, start, input)

def cappedIf(below: Bool, +f: Nat, +cap: Nat) -> Nat:
  match below:
    case True{}:
      f
    case False{}:
      cap

def capped(+f: Nat, +cap: Nat) -> Nat:
  cappedIf(Nat.is_le(f, cap), f, cap)

def orMore(found: Maybe<&2, +List<Core.Bsr>>, +retry: Maybe<&2, +List<Core.Bsr>>) -> Maybe<&2, +List<Core.Bsr>>:
  match found:
    case Some{+set}:
      Some{set}
    case None{}:
      retry

# Fuel f (at most cap); with no answer, fuel 2f, at most `tries` more times, and the cap last.
def doubling(tries: Nat, +f: Nat, +cap: Nat, +target: Target, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  match tries:
    case 0n:
      runWith(target, cap, grammar, start, input)
    case 1n+t:
      orMore(runWith(target, capped(f, cap), grammar, start, input), doubling(t, Nat.add(f, f), cap, target, grammar, start, input))

def stepsOf(+target: Target, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  doubling(16n, 8n, fuel(grammar, input), target, grammar, start, input)

def reportWith(+tr: E.Translation, +target: Target, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportOf(stepsOf(target, E.coreOf(tr), start, input), E.originsIn(tr), swift)

# THE EXACT SET.
def report(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportWith(E.towardsSwift(grammar), Exact{}, start, input, swift)

# AFTER @prefer AND @avoid, on top of lookahead, @left and @right (phases 1 and 2): the
# chosen set. Without preference marks it is phase 1 alone.
def oracleWith(+tr: E.Translation, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportWith(tr, Chosen{Guard.marksOf(gm, E.originsIn(tr)), Prefer.rankMarksOf(marks, E.originsIn(tr))}, start, input, swift)

def preferReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  oracleWith(E.towardsSwift(grammar), gm, marks, start, input, swift)

# AFTER LOOKAHEAD, @left AND @right (phase 1).
def guardReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  oracleWith(E.towardsSwift(grammar), gm, [], start, input, swift)

# AFTER @longest AND @shortest (phase 3, on top of phases 1 and 2): the selecting oracle's set.
def extentWith(+tr: E.Translation, +gm: +List<Spec.GuardMark>, +pm: +List<Spec.Mark>, +em: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportWith(tr, Selected{Guard.marksOf(gm, E.originsIn(tr)), Prefer.rankMarksOf(pm, E.originsIn(tr)), Ext.extentMarksOf(em, E.originsIn(tr))}, start, input, swift)

def extentReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +pm: +List<Spec.Mark>, +em: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  extentWith(E.towardsSwift(grammar), gm, pm, em, start, input, swift)
