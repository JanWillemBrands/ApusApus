import Base
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PREFER.bend as Prefer
import ./TABLES.bend as T

# THE PREDICTING PARSER: the GLL engine with Scott's predict sets. A cluster of x at i
# starts a production of x only when the token at i is in the production's predict set, by
# the tables of TABLES.bend. The parser hands out its steps only when the tables are closed
# and its final state is closed for the descriptors prediction admits
# (`predict_every_parse_step`: it misses no step of a parse tree).

# The predict set of every production, in grammar order.
def predictSets(prods: +List<Core.Production>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>, +nulls: +List<Nat>) -> +List<+List<Maybe<&2, Nat>>>:
  match prods:
    case Nil{}:
      []
    case Con{Core.Production{+lhs, +rhs}, rest}:
      T.predictOf(lhs, rhs, firsts, follows, nulls) <> predictSets(rest, firsts, follows, nulls)

# The tables are closed and the start symbol is followed by the end.
def tablesClosed(+grammar: +List<Core.Production>, +start: Nat, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>) -> Bool:
  Bool.and(Prefer.nullsClosed(grammar, nulls),
    Bool.and(T.firstsClosed(grammar, firsts, nulls),
      Bool.and(T.followsClosed(grammar, firsts, follows, nulls),
        Bool.and(T.followHas(start, None{}, follows), T.suffixOk([Core.Nonterminal{start, Core.Anything{}}], start, firsts, follows, nulls)))))

def predictPick(ok: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +sets: +List<+List<Maybe<&2, Nat>>>) -> Maybe<&2, +List<Core.Bsr>>:
  match ok:
    case True{}:
      Check.runCheckedWith(Gll.Allowed{sets}, Gll.parseWith(fuel, Gll.Allowed{sets}, grammar, start, input), grammar, start, input)
    case False{}:
      None{}

def predictWith(+fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>, +nulls: +List<Nat>, +firsts: +List<T.FirstFact>, +follows: +List<T.FollowFact>) -> Maybe<&2, +List<Core.Bsr>>:
  predictPick(tablesClosed(grammar, start, nulls, firsts, follows), fuel, grammar, start, input, predictSets(grammar, firsts, follows, nulls))

# THE PREDICTING PARSER: tables grown with `fuel` rounds each, the engine run with `fuel` steps.
def predictedSteps(fuel: Nat, +grammar: +List<Core.Production>, +start: Nat, +input: +List<Nat>) -> Maybe<&2, +List<Core.Bsr>>:
  +f = fuel
  +nulls = Prefer.growNulls(f, grammar, [])
  +firsts = T.growFirsts(f, grammar, nulls, [])
  predictWith(f, grammar, start, input, nulls, firsts, T.growFollows(f, grammar, firsts, nulls, [T.FollowFact{start, None{}}]))
