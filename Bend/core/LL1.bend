import Base
import ../SPEC.bend as Spec
import ./CORE.bend as Core
import ./EBNF.bend as E

# LL(1) ON THE CORE.
#
# On the core every choice point is a nonterminal and every choice a production, so LL(1)
# is the textbook strong LL(1) of a BNF grammar. FOLLOW of a production is read from parse
# trees: in some parse tree, the production's last step ends at j and the token at j is
# `next`. LL(1) of a grammar as written is LL(1) of its translation towards LL(1), the one
# whose loops are right-recursive (EBNF.bend).

# The items can read nothing.
def Nullable(+grammar: +List<Core.Production>, +items: +List<Core.Sym>) -> Type:
  &f: +List<Core.Tree> -> {Core.fits(f, grammar, items) == True{} : Bool} & {Core.leaves(f) == [] : +List<Nat>}

# The items can begin with `next`.
def FirstIs(+grammar: +List<Core.Production>, +items: +List<Core.Sym>, +next: Maybe<&2, Nat>) -> Type:
  &f: +List<Core.Tree> -> &t: Nat -> &r: +List<Nat> ->
    {Core.fits(f, grammar, items) == True{} : Bool} & {Core.leaves(f) == t <> r : +List<Nat>} & {next == Some{t} : Maybe<&2, Nat>}

# In some parse tree, production q's last step ends at j, and the token at j is `next`
# (None at the end of the input).
def FollowIs(+grammar: +List<Core.Production>, +start: Nat, +q: Nat, +next: Maybe<&2, Nat>) -> Type:
  &input: +List<Nat> -> &tree: Core.Tree -> &i: Nat -> &k: Nat -> &j: Nat ->
    Core.ParseTree(grammar, start, input, tree) &
    {Core.member(Core.Bsr{q, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), i, k, j}, Core.steps([tree], 0n)) == True{} : Bool} &
    {Core.tokAt(input, j) == next : Maybe<&2, Nat>}

# Production q can begin with `next`: through FIRST, or it reads nothing and FOLLOW has it.
def Predicts(+grammar: +List<Core.Production>, +start: Nat, +q: Nat, +next: Maybe<&2, Nat>) -> Type:
  Either<FirstIs(grammar, Core.rhsOf(grammar, q), next), Nullable(grammar, Core.rhsOf(grammar, q)) & FollowIs(grammar, start, q, next)>

# LL(1) at nonterminal x: no two productions of x can begin with the same next token.
def LL1At(+grammar: +List<Core.Production>, +start: Nat, +x: Nat) -> Type:
  @q1: Nat -> @q2: Nat -> @next: Maybe<&2, Nat> ->
    {Nat.is_eq(q1, q2) == False{} : Bool} -> {Core.lhsIs(grammar, q1, x) == True{} : Bool} -> {Core.lhsIs(grammar, q2, x) == True{} : Bool} ->
    Predicts(grammar, start, q1, next) -> Predicts(grammar, start, q2, next) -> Empty

# LL(1): LL(1) at every nonterminal.
def LL1(+grammar: +List<Core.Production>, +start: Nat) -> Type:
  @x: Nat -> LL1At(grammar, start, x)

# LL(1) of a grammar as written: of its translation towards LL(1).
def LL1Written(+grammar: +List<Spec.Production>, +start: Nat) -> Type:
  LL1(E.coreOf(E.towardsLL1(grammar)), start)

# A node of production q at position k in the tree: children that read the input from k,
# whose own steps are steps of the tree.
def NodeAt(+grammar: +List<Core.Production>, +input: +List<Nat>, +tree: Core.Tree, +q: Nat, +k: Nat) -> Type:
  &ch: +List<Core.Tree> -> {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k) == True{} : Bool} & {Core.allIn(Core.own(q, ch, 0n, k, k), Core.steps([tree], 0n)) == True{} : Bool}
