import Base
import ./SPEC.bend as Spec
import ./EXACT.bend as Exact

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
