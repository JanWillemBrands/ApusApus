import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# WHAT A PARSE COSTS (a measure, not a claim). Three counts of distinct facts of the
# engine's final state, each one unit, none depending on the order the engine worked in:
#
#   descriptors        the work: one execution of the engine's outer loop each (Scott and
#                      Johnstone's |U|)
#   steps              the memory: the output BSR set (their |ϒ|); at least the exact set,
#                      the rest is dead wood
#   lexer questions    the lexer's work, for a lexer that answers on demand and remembers
#                      its answers: the distinct pairs (position, terminal) it is asked
#                      about. A descriptor before a terminal asks about that terminal; with
#                      prediction, every candidate descriptor also asks about each terminal
#                      of its predict set. A lexer that answers once per position needs at
#                      least one question per position visited.
#
# The candidates are the descriptors the rules of the closedness check (CHECK.bend) would
# add to the state, whether prediction admits them or not.

type Question is Data:
  Question{position: Nat, terminal: Nat}

type Cost is Data:
  Cost{descriptors: Nat, steps: Nat, lexerQuestions: Nat}

def questionEqual(a: Question, b: Question) -> Bool:
  match a b:
    case Question{p1, t1} Question{p2, t2}:
      Bool.and(Nat.is_eq(p1, p2), Nat.is_eq(t1, t2))

def questionIn(+question: Question, questions: +List<Question>) -> Bool:
  match questions:
    case Nil{}:
      False{}
    case Con{other, rest}:
      Bool.or(questionEqual(question, other), questionIn(question, rest))

def addQuestionPick(known: Bool, +question: Question, questions: +List<Question>) -> +List<Question>:
  match known:
    case True{}:
      questions
    case False{}:
      question <> questions

def addQuestion(+question: Question, +questions: +List<Question>) -> +List<Question>:
  addQuestionPick(questionIn(question, questions), question, questions)

def addQuestions(new: +List<Question>, +questions: +List<Question>) -> +List<Question>:
  match new:
    case Nil{}:
      questions
    case Con{+question, rest}:
      addQuestions(rest, addQuestion(question, questions))

# ---- The candidates: what each fact's rule would add ----

def whenTrue(condition: Bool, +descriptors: +List<Gll.Desc>) -> +List<Gll.Desc>:
  match condition:
    case True{}:
      descriptors
    case False{}:
      []

# The descriptor after the item at the dot, for a seen descriptor.
def nextOfItem(item: Maybe<&2, Spec.Item>, +input: +List<Nat>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +start: Nat, +position: Nat) -> +List<Gll.Desc>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+terminal}}}:
      whenTrue(Gll.tokenIs(List.get(&2, Nat, input, position), terminal), [Gll.Desc{index, rpath, 1n+dot, start, 1n+position}])
    case Some{Spec.Brack{+kind, alts}}:
      whenTrue(Gll.isSkippable(kind), [Gll.Desc{index, rpath, 1n+dot, start, position}])
    case Some{Spec.Eps{}}:
      [Gll.Desc{index, rpath, 1n+dot, start, position}]
    case _:
      []

def nextOf(descriptor: Gll.Desc, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> +List<Gll.Desc>:
  match descriptor:
    case Gll.Desc{+index, +rpath, +dot, +start, +position}:
      nextOfItem(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), input, index, rpath, dot, start, position)

def nextOfAll(seen: +List<Gll.Desc>, +grammar: +List<Spec.Production>, +input: +List<Nat>) -> +List<Gll.Desc>:
  match seen:
    case Nil{}:
      []
    case Con{descriptor, rest}:
      List.append(&2, Gll.Desc, nextOf(descriptor, grammar, input), nextOfAll(rest, grammar, input))

def seedsOfAll(clusters: +List<Gll.CKey>, +grammar: +List<Spec.Production>) -> +List<Gll.Desc>:
  match clusters:
    case Nil{}:
      []
    case Con{+key, rest}:
      List.append(&2, Gll.Desc, Check.seedsOf(grammar, key), seedsOfAll(rest, grammar))

def resumedOf(edge: Gll.Edge, +end: Nat) -> Gll.Desc:
  match edge:
    case Gll.Edge{index, rpath, dot, start}:
      Gll.Desc{index, rpath, 1n+dot, start, end}

def resumesOfEdge(pops: +List<Gll.Pop>, +key: Gll.CKey, +edge: Gll.Edge) -> +List<Gll.Desc>:
  match pops:
    case Nil{}:
      []
    case Con{Gll.Pop{+popKey, +end}, rest}:
      List.append(&2, Gll.Desc, whenTrue(Gll.keyEq(key, popKey), [resumedOf(edge, end)]), resumesOfEdge(rest, key, edge))

def resumesOfAll(returns: +List<Gll.Ret>, +pops: +List<Gll.Pop>) -> +List<Gll.Desc>:
  match returns:
    case Nil{}:
      []
    case Con{Gll.Ret{+key, +edge}, rest}:
      List.append(&2, Gll.Desc, resumesOfEdge(pops, key, edge), resumesOfAll(rest, pops))

def againOfAll(pops: +List<Gll.Pop>, +grammar: +List<Spec.Production>) -> +List<Gll.Desc>:
  match pops:
    case Nil{}:
      []
    case Con{Gll.Pop{+key, +end}, rest}:
      List.append(&2, Gll.Desc, Check.againOfKey(grammar, key, end), againOfAll(rest, grammar))

def candidates(+grammar: +List<Spec.Production>, +input: +List<Nat>, s: Gll.GState) -> +List<Gll.Desc>:
  match s:
    case Gll.GState{+seen, todo, +clusters, +returns, +pops, steps}:
      List.append(&2, Gll.Desc, nextOfAll(seen, grammar, input), List.append(&2, Gll.Desc, seedsOfAll(clusters, grammar), List.append(&2, Gll.Desc, resumesOfAll(returns, pops), againOfAll(pops, grammar))))

# ---- The lexer's questions ----

def terminalQuestion(item: Maybe<&2, Spec.Item>, +position: Nat) -> +List<Question>:
  match item:
    case Some{Spec.Sym{Spec.Terminal{+terminal}}}:
      [Question{position, terminal}]
    case _:
      []

# A seen descriptor before a terminal asks about that terminal.
def matchQuestions(seen: +List<Gll.Desc>, +grammar: +List<Spec.Production>) -> +List<Question>:
  match seen:
    case Nil{}:
      []
    case Con{Gll.Desc{+index, +rpath, +dot, start, +position}, rest}:
      List.append(&2, Question, terminalQuestion(Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), position), matchQuestions(rest, grammar))

def questionsAt(terminals: +List<Nat>, +position: Nat) -> +List<Question>:
  match terminals:
    case Nil{}:
      []
    case Con{+terminal, rest}:
      Question{position, terminal} <> questionsAt(rest, position)

def predictTerminals(set: Gll.LSet) -> +List<Nat>:
  match set:
    case Gll.LSet{any, terminals, end}:
      terminals

# With prediction, a candidate asks about every terminal of its predict set.
def predictQuestions(pr: Gll.Pred, +grammar: +List<Spec.Production>, descriptors: +List<Gll.Desc>) -> +List<Question>:
  match pr descriptors:
    case Gll.NoPred{} _:
      []
    case Gll.Predict{+tables} Nil{}:
      []
    case Gll.Predict{+tables} Con{Gll.Desc{+index, +rpath, +dot, start, +position}, rest}:
      List.append(&2, Question, questionsAt(predictTerminals(Gll.predictAt(grammar, tables, index, rpath, dot)), position), predictQuestions(Gll.Predict{tables}, grammar, rest))

def lexerQuestions(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> +List<Question>:
  addQuestions(List.append(&2, Question, matchQuestions(Check.seenOf(s), grammar), predictQuestions(pr, grammar, candidates(grammar, input, s))), [])

# ---- The cost of a run ----

def costOf(+pr: Gll.Pred, +grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> Cost:
  Cost{List.length(&2, Gll.Desc, Check.seenOf(s)), List.length(&2, Spec.Bsr, Check.stepsOf(s)), List.length(&2, Question, lexerQuestions(pr, grammar, input, s))}

# The counts the cost leaves out, for checking that they follow the descriptors.
type Others is Data:
  Others{clusters: Nat, returns: Nat, pops: Nat, candidates: Nat}

def othersOf(+grammar: +List<Spec.Production>, +input: +List<Nat>, +s: Gll.GState) -> Others:
  Others{List.length(&2, Gll.CKey, Check.clustersOf(s)), List.length(&2, Gll.Ret, Check.returnsOf(s)), List.length(&2, Gll.Pop, Check.popsOf(s)), List.length(&2, Gll.Desc, candidates(grammar, input, s))}
