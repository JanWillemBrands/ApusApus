import Base
import ./SPEC.bend as Spec
import ./EXACT.bend as Exact
import ./PREFER.bend as Prefer
import ./GUARD.bend as Guard
import ./EXTENT.bend as Ext
import ./UNBEATEN.bend as Unb
import ./WITNESS.bend as Witness

# COMPARING SWIFT APUS WITH THE EXACT SET. The files in swift/ are written by
# ApusApusTests/BendExport.swift: a grammar, an input, and the BSR elements Swift Apus
# computed for it. `report` puts them next to the exact set of the same grammar and
# input, which `gll_bsr_exact` guarantees to be exactly the steps of the parse trees.
#
#   Agree{n}                  Swift has exactly the n steps of the exact set
#   Differ{e, s, miss, extra} the exact set has e steps, Swift s; `miss` are steps of a
#                             parse tree that Swift lacks, `extra` are Swift's steps that
#                             are in no parse tree (dead wood)
#   NoAnswer{}                the exact parser gave no answer (out of fuel, or a check failed)
#
# `preferReport` does the same after @prefer and @avoid, on top of the rules (below).

type Report is Data:
  Agree{count: Nat}
  Differ{exact: Nat, swift: Nat, missing: +List<Spec.Bsr>, extra: +List<Spec.Bsr>}
  NoAnswer{}

def fuel() -> Nat:
  20000n

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

def pickIf(same: Bool, +exact: +List<Spec.Bsr>, +swift: +List<Spec.Bsr>, +missing: +List<Spec.Bsr>, +extra: +List<Spec.Bsr>) -> Report:
  match same:
    case True{}:
      Agree{List.length(&2, Spec.Bsr, exact)}
    case False{}:
      Differ{List.length(&2, Spec.Bsr, exact), List.length(&2, Spec.Bsr, swift), missing, extra}

def pick(+exact: +List<Spec.Bsr>, +swift: +List<Spec.Bsr>, +missing: +List<Spec.Bsr>, +extra: +List<Spec.Bsr>) -> Report:
  pickIf(Bool.and(List.is_empty(&2, Spec.Bsr, missing), List.is_empty(&2, Spec.Bsr, extra)), exact, swift, missing, extra)

def reportOf(found: Maybe<&2, +List<Spec.Bsr>>, +swift: +List<Spec.Bsr>) -> Report:
  match found:
    case Some{+exact}:
      pick(exact, swift, notIn(exact, swift), notIn(swift, exact))
    case None{}:
      NoAnswer{}

def report(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportOf(Exact.exactSteps(fuel(), grammar, start, input), swift)

# AFTER @prefer AND @avoid. The preference oracle's set embeds exactly the unbeaten trees
# (`prefer_avoid_exact`), but it also keeps the steps inside a removed choice, which make
# no tree. To compare with Swift Apus after its Oracle, the report takes the steps of the
# unbeaten trees only: the witness trees of the oracle's set that use only its steps.

def keepSteps(ok: Bool, +xs: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match ok:
    case True{}:
      xs
    case False{}:
      []

def embeddedIn(ws: +List<Spec.Tree>, +set: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match ws:
    case Nil{}:
      []
    case Con{+t, rest}:
      List.append(&2, Spec.Bsr, keepSteps(Spec.allIn(Spec.steps(t, 0n), set), Spec.steps(t, 0n)), embeddedIn(rest, set))

# Each element once: trees share steps.
def distinct(xs: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      keepOut(Spec.bsrMember(x, rest), x, distinct(rest))

def unbeatenFrom(found: Maybe<&2, +List<Spec.Bsr>>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  match found:
    case Some{+set}:
      Some{distinct(embeddedIn(Witness.witnesses(fuel(), grammar, start, input, set), set))}
    case None{}:
      None{}

# The steps of the unbeaten trees, or nothing when the oracle refuses.
def unbeatenSteps(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  unbeatenFrom(Unb.unbeatenSteps(fuel(), grammar, gm, marks, start, input), grammar, start, input)

def preferReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +marks: +List<Spec.Mark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportOf(unbeatenSteps(grammar, gm, marks, start, input), swift)

# AFTER LOOKAHEAD, @left AND @right (phase 1). The same, with the guard oracle: the steps
# of the admissible trees (`guards_exact`), or nothing when the oracle refuses.
def admittedSteps(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  unbeatenFrom(Guard.guardSteps(fuel(), grammar, gm, start, input), grammar, start, input)

def guardReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportOf(admittedSteps(grammar, gm, start, input), swift)

# AFTER @longest AND @shortest (phase 3, on top of phases 1 and 2). The same, with the
# extent oracle: the steps of the selected trees (`extent_exact`), or nothing when the
# oracle refuses.
def extentBestSteps(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +pm: +List<Spec.Mark>, +em: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Spec.Bsr>>:
  unbeatenFrom(Ext.extentSteps(fuel(), grammar, gm, pm, em, start, input), grammar, start, input)

def extentReport(+grammar: +List<Spec.Production>, +gm: +List<Spec.GuardMark>, +pm: +List<Spec.Mark>, +em: +List<Spec.ExtentMark>, +start: Nat, +input: +List<Nat>, +swift: +List<Spec.Bsr>) -> Report:
  reportOf(extentBestSteps(grammar, gm, pm, em, start, input), swift)
