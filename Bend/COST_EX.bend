import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./EXACT.bend as Exact
import ./COST.bend as Cost
import ./FIRST.bend as First
import ./PREDICT_EX.bend as Ex
import ./swift/brackets.bend as S_brackets
import ./swift/choice.bend as S_choice
import ./swift/left.bend as S_left
import ./swift/loop.bend as S_loop
import ./swift/loop_empty.bend as S_loop_empty
import ./swift/nullable_loop.bend as S_nullable_loop
import ./swift/optional.bend as S_optional
import ./swift/positive.bend as S_positive
import ./swift/split.bend as S_split

# The cost of the plain and the predicting parser on the examples, with the counts the cost
# leaves out, the input length and the exact set's size.

type Row is Data:
  Row{tokens: Nat, exactSteps: Nat, plain: Cost.Cost, plainOthers: Cost.Others, predicting: Cost.Cost, predictingOthers: Cost.Others}

def stateOf(r: Gll.GRun) -> Gll.GState:
  match r:
    case Gll.GDone{s}:
      s
    case Gll.OutOfFuel{s}:
      s

def rowFrom(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Row:
  +pr = {Gll.Predict{Ex.tablesOr(First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start))} : Gll.Pred}
  +plainState = stateOf(Gll.parse(Ex.fuel(), grammar, start, input))
  +predictingState = stateOf(Gll.parseWith(Ex.fuel(), pr, grammar, start, input))
  Row{List.length(&2, Nat, input), List.length(&2, Spec.Bsr, Ex.setOr(Exact.exactSteps(Ex.fuel(), grammar, start, input))),
    Cost.costOf(Gll.NoPred{}, grammar, input, plainState), Cost.othersOf(grammar, input, plainState),
    Cost.costOf(pr, grammar, input, predictingState), Cost.othersOf(grammar, input, predictingState)}

def row(+grammar: +List<Spec.Production>, +input: +List<Nat>) -> Row:
  rowFrom(grammar, 0n, input)

def main() -> +List<Row>:
  [ row(Ex.loopGrammar(), [1n, 2n, 2n, 2n, 3n]),
    row(Ex.choiceGrammar(), [1n, 1n, 2n, 3n]),
    row(Ex.nullGrammar(), [2n, 2n, 1n]),
    row(Ex.optGrammar(), [2n]),
    row(Ex.splitGrammar(), [1n, 1n, 1n]),
    row(Ex.leftGrammar(), [1n, 5n, 1n, 5n, 1n]),
    row(Ex.exprGrammar(), Ex.exprInput()),
    rowFrom(S_brackets.grammar(), S_brackets.start(), S_brackets.input()),
    rowFrom(S_choice.grammar(), S_choice.start(), S_choice.input()),
    rowFrom(S_left.grammar(), S_left.start(), S_left.input()),
    rowFrom(S_loop.grammar(), S_loop.start(), S_loop.input()),
    rowFrom(S_loop_empty.grammar(), S_loop_empty.start(), S_loop_empty.input()),
    rowFrom(S_nullable_loop.grammar(), S_nullable_loop.start(), S_nullable_loop.input()),
    rowFrom(S_optional.grammar(), S_optional.start(), S_optional.input()),
    rowFrom(S_positive.grammar(), S_positive.start(), S_positive.input()),
    rowFrom(S_split.grammar(), S_split.start(), S_split.input()) ]
