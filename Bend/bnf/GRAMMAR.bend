import Base
import ./TYPES.bend as Types

# The parser: a CYK table, then the binary subtree (BSR) set built from it.

def natMember(+x: Nat, xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(x, y), natMember(x, rest))

def keepNat(keep: Bool, x: Nat, xs: +List<Nat>) -> +List<Nat>:
  match keep:
    case False{}:
      xs
    case True{}:
      x <> xs

# The nonterminals A with a production A = kind.
def terminalNonterminals(+grammar: +List<Types.Production>, +kind: Nat) -> +List<Nat>:
  match grammar:
    case Nil{}:
      Nil{}
    case Con{Types.Production{lhs, [Types.Terminal{k}]}, rest}:
      keepNat(Nat.is_eq(k, kind), lhs, terminalNonterminals(rest, kind))
    case Con{other, rest}:
      terminalNonterminals(rest, kind)

# The nonterminals A with a production A = B C, B in `lefts` and C in `rights`.
def binaryNonterminals(+grammar: +List<Types.Production>, +lefts: +List<Nat>, +rights: +List<Nat>) -> +List<Nat>:
  match grammar:
    case Nil{}:
      Nil{}
    case Con{Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, rest}:
      keepNat(Bool.and(natMember(b, lefts), natMember(c, rights)), lhs, binaryNonterminals(rest, lefts, rights))
    case Con{other, rest}:
      binaryNonterminals(rest, lefts, rights)

# CYK: a table cell holds the nonterminals that derive the `length` tokens from `start`.
type Cell is Data:
  Cell{start: Nat, length: Nat, nonterminals: +List<Nat>}

def pickCell(found: Bool, here: +List<Nat>, later: +List<Nat>) -> +List<Nat>:
  match found:
    case False{}:
      later
    case True{}:
      here

def lookup(table: +List<Cell>, +start: Nat, +length: Nat) -> +List<Nat>:
  match table:
    case Nil{}:
      Nil{}
    case Con{Cell{s, l, nonterminals}, rest}:
      pickCell(Bool.and(Nat.is_eq(l, length), Nat.is_eq(s, start)), nonterminals, lookup(rest, start, length))

# All ways to split a span from `start` into a left part of length 1 .. `left` and the
# rest; the total length left + right stays the same as the split moves.
def splitNonterminals(+grammar: +List<Types.Production>, +table: +List<Cell>, +start: Nat, left: Nat, +right: Nat) -> +List<Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+(+smaller):
      List.append(
        &2, Nat,
        binaryNonterminals(grammar, lookup(table, start, 1n+smaller), lookup(table, Nat.add(start, 1n+smaller), right)),
        splitNonterminals(grammar, table, start, smaller, 1n+right))

def tokenNonterminals(+grammar: +List<Types.Production>, token: Maybe<&2, Nat>) -> +List<Nat>:
  match token:
    case None{}:
      Nil{}
    case Some{kind}:
      terminalNonterminals(grammar, kind)

# The nonterminals for the span (start, length): a single token uses the
# terminal productions, a longer span combines two shorter spans.
def cellNonterminals(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Cell>, +start: Nat, length: Nat) -> +List<Nat>:
  match length:
    case 0n:
      Nil{}
    case 1n+0n:
      tokenNonterminals(grammar, List.get(&2, Nat, inputTokens, start))
    case 1n+1n+(+shorter):
      splitNonterminals(grammar, table, start, 1n+shorter, 1n)

# One row of the table: the cells of one length, for the starts 0 .. remaining-1.
def row(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Cell>, +length: Nat, remaining: Nat) -> +List<Cell>:
  match remaining:
    case 0n:
      Nil{}
    case 1n+(+start):
      Cell{start, length, cellNonterminals(grammar, inputTokens, table, start, length)} <> row(grammar, inputTokens, table, length, start)

# The table for all lengths 1 .. fuel, longest first. Each row only reads cells
# of shorter spans, which the table already holds.
def buildTable(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +count: Nat, fuel: Nat) -> +List<Cell>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+shorter):
      +shorterTable = buildTable(grammar, inputTokens, count, shorter)
      List.append(&2, Cell, row(grammar, inputTokens, shorterTable, 1n+shorter, count), shorterTable)

# BINARY SUBTREE SETS: every derivation step of every parse tree, as BSR elements.
#
# A step for A = "t" at position s is Bsr{Slot{p, 1}, s, s, s + 1}, when the token at s is t.
# A step for A = B C over the span (s, l), split after k tokens, is
# Bsr{Slot{p, 2}, s, s + k, s + l}, when B is in the cell for (s, k) and C in the cell for
# (s + k, l - k).

def keepBsr(keep: Bool, element: Types.Bsr, others: +List<Types.Bsr>) -> +List<Types.Bsr>:
  match keep:
    case False{}:
      others
    case True{}:
      element <> others

# The steps A = "kind" at position s, for the productions from `index` on.
def terminalSteps(grammar: +List<Types.Production>, +kind: Nat, +s: Nat, +index: Nat) -> +List<Types.Bsr>:
  match grammar:
    case Nil{}:
      Nil{}
    case Con{Types.Production{lhs, [Types.Terminal{k}]}, rest}:
      keepBsr(Nat.is_eq(k, kind), Types.Bsr{Types.Slot{index, 1n}, s, s, 1n+s}, terminalSteps(rest, kind, s, 1n+index))
    case Con{other, rest}:
      terminalSteps(rest, kind, s, 1n+index)

# The steps A = B C over i .. j with pivot k, B in `lefts` and C in `rights`.
def binarySteps(grammar: +List<Types.Production>, +lefts: +List<Nat>, +rights: +List<Nat>, +i: Nat, +k: Nat, +j: Nat, +index: Nat) -> +List<Types.Bsr>:
  match grammar:
    case Nil{}:
      Nil{}
    case Con{Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, rest}:
      keepBsr(Bool.and(natMember(b, lefts), natMember(c, rights)), Types.Bsr{Types.Slot{index, 2n}, i, k, j}, binarySteps(rest, lefts, rights, i, k, j, 1n+index))
    case Con{other, rest}:
      binarySteps(rest, lefts, rights, i, k, j, 1n+index)

def tokenSteps(+grammar: +List<Types.Production>, token: Maybe<&2, Nat>, +s: Nat) -> +List<Types.Bsr>:
  match token:
    case None{}:
      Nil{}
    case Some{kind}:
      terminalSteps(grammar, kind, s, 0n)

# The steps for all splits of the span from `start`; the left part has length
# 1 .. `left`, and left + right stays the same.
def splitSteps(+grammar: +List<Types.Production>, +table: +List<Cell>, +start: Nat, left: Nat, +right: Nat) -> +List<Types.Bsr>:
  match left:
    case 0n:
      Nil{}
    case 1n+(+smaller):
      List.append(
        &2, Types.Bsr,
        binarySteps(grammar, lookup(table, start, 1n+smaller), lookup(table, Nat.add(start, 1n+smaller), right), start, Nat.add(start, 1n+smaller), Nat.add(start, Nat.add(1n+smaller, right)), 0n),
        splitSteps(grammar, table, start, smaller, 1n+right))

def spanSteps(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Cell>, +start: Nat, length: Nat) -> +List<Types.Bsr>:
  match length:
    case 0n:
      Nil{}
    case 1n+0n:
      tokenSteps(grammar, List.get(&2, Nat, inputTokens, start), start)
    case 1n+1n+(+shorter):
      splitSteps(grammar, table, start, 1n+shorter, 1n)

def rowSteps(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Cell>, +length: Nat, remaining: Nat) -> +List<Types.Bsr>:
  match remaining:
    case 0n:
      Nil{}
    case 1n+(+start):
      List.append(&2, Types.Bsr, spanSteps(grammar, inputTokens, table, start, length), rowSteps(grammar, inputTokens, table, length, start))

def allSteps(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Cell>, +count: Nat, fuel: Nat) -> +List<Types.Bsr>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+shorter):
      List.append(&2, Types.Bsr, rowSteps(grammar, inputTokens, table, 1n+shorter, count), allSteps(grammar, inputTokens, table, count, shorter))

# Every derivation step the CYK table supports, connected to the root or not.
def cykSteps(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>) -> +List<Types.Bsr>:
  +count = List.length(&2, Nat, inputTokens)
  allSteps(grammar, inputTokens, buildTable(grammar, inputTokens, count, count), count, count)

# PRUNING: keep only the steps that contribute to a parse tree of the whole input.
# A need asks for the steps of nonterminal a over i .. j. The first need is the
# start symbol over the whole input; a kept step A = B C over i .. j with pivot k
# needs B over i .. k and C over k .. j.

type Need is Data:
  Need{a: Nat, i: Nat, j: Nat}

def needMember(+need: Need, needs: +List<Need>) -> Bool:
  match need needs:
    case _ Nil{}:
      False{}
    case Need{+a, +i, +j} Con{Need{a2, i2, j2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))), needMember(Need{a, i, j}, rest))

# The nonterminal of production `index` (0 when there is no such production).
def lhsOf(+grammar: +List<Types.Production>, index: Nat) -> Nat:
  match grammar index:
    case Nil{} _:
      0n
    case Con{Types.Production{lhs, rhs}, rest} 0n:
      lhs
    case Con{p, rest} 1n+i:
      lhsOf(rest, i)

def isNeeded(+grammar: +List<Types.Production>, +needs: +List<Need>, element: Types.Bsr) -> Bool:
  match element:
    case Types.Bsr{Types.Slot{+p, d}, +i, k, +j}:
      needMember(Need{lhsOf(grammar, p), i, j}, needs)

def keepNeeded(keep: Bool, element: Types.Bsr, others: +List<Types.Bsr>) -> +List<Types.Bsr>:
  match keep:
    case False{}:
      others
    case True{}:
      element <> others

def filterNeeded(+grammar: +List<Types.Production>, +needs: +List<Need>, steps: +List<Types.Bsr>) -> +List<Types.Bsr>:
  match steps:
    case Nil{}:
      Nil{}
    case Con{+element, rest}:
      keepNeeded(isNeeded(grammar, needs, element), element, filterNeeded(grammar, needs, rest))

# What a complete step A = B C over i .. j with pivot k needs; other steps need nothing.
def pairNeeds(rhs: +List<Types.Symbol>, +i: Nat, +k: Nat, +j: Nat) -> +List<Need>:
  match rhs:
    case Nil{}:
      Nil{}
    case Con{Types.Terminal{t}, more}:
      Nil{}
    case Con{Types.Nonterminal{b}, Nil{}}:
      Nil{}
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{t}, more}}:
      Nil{}
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      [Need{b, i, k}, Need{c, k, j}]
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      Nil{}

def childNeeds(+grammar: +List<Types.Production>, element: Types.Bsr) -> +List<Need>:
  match element:
    case Types.Bsr{Types.Slot{p, 0n}, i, k, j}:
      Nil{}
    case Types.Bsr{Types.Slot{p, 1n+0n}, i, k, j}:
      Nil{}
    case Types.Bsr{Types.Slot{p, 1n+1n+0n}, +i, +k, +j}:
      pairNeeds(Types.rhsOf(grammar, p), i, k, j)
    case Types.Bsr{Types.Slot{p, 1n+1n+1n+more}, i, k, j}:
      Nil{}

def allChildNeeds(+grammar: +List<Types.Production>, kept: +List<Types.Bsr>) -> +List<Need>:
  match kept:
    case Nil{}:
      Nil{}
    case Con{element, rest}:
      List.append(&2, Need, childNeeds(grammar, element), allChildNeeds(grammar, rest))

# The needs after n rounds: each round adds what the steps needed so far need.
def needsAt(+grammar: +List<Types.Production>, +start: Nat, +count: Nat, +steps: +List<Types.Bsr>, n: Nat) -> +List<Need>:
  match n:
    case 0n:
      [Need{start, 0n, count}]
    case 1n+(+m):
      +before = needsAt(grammar, start, count, steps, m)
      List.append(&2, Need, before, allChildNeeds(grammar, filterNeeded(grammar, before, steps)))

# The BSR set of the input: the CYK steps that a parse tree of the whole input needs.
# A need is for a shorter span than the step that needs it, so `count` rounds reach
# every node of every parse tree.
def bsrSet(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>) -> +List<Types.Bsr>:
  +count = List.length(&2, Nat, inputTokens)
  +steps = cykSteps(grammar, inputTokens)
  filterNeeded(grammar, needsAt(grammar, start, count, steps, count), steps)

# The recognizer: the input is accepted when the BSR set is not empty.
def recognize(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>) -> Bool:
  Bool.not(List.is_empty(&2, Types.Bsr, bsrSet(grammar, start, inputTokens)))
