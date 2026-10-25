import Base
import ./TYPES.bend as Types
import ./GRAMMAR.bend as Grammar
import ./LAWS.bend as GrammarLaws
import ./LEMMAS.bend as Lemma

# Proofs of the laws in LAWS.bend.
#
# The CYK part (first half) is about cykSteps, every step the CYK table supports:
# - the table is complete: a parse tree's nonterminal is in the cell for the slice
#   it spells (cell_complete);
# - every CYK step is a leaf step for its token or a step A = B C with B and C in the
#   cells of its two parts (set_from);
# - every parse tree of the input is embedded in the CYK steps (cyk_embedded_every),
#   and every cell entry has an embedded tree (cell_support, supported_dot).
#
# The BSR set keeps the CYK steps that pruning needs (Grammar.bsrSet):
# - nothing missing: down a parse tree each node is needed one round after its
#   parent, so every step survives (tree_kept, cyk_every_parse_step);
# - no dead wood: every need has a context, a way to extend any tree for its span to
#   a parse tree of the whole input (all_ok); a kept step's own tree, extended,
#   is the parse tree the law asks for (cyk_only_parse_steps).
# The recognizer's laws follow from these two.

# ======== EMBEDDED TREES ========
#
# The old form of the BSR laws, still used inside the CYK proofs: is every step of
# a tree in a set? `embedded(tree, set, i)` checks exactly the elements of steps(tree, i).

# Does the set have the step for slot dot + 1 of production `index` (node from i),
# when the child that completes the slot covers at .. end? A slot with one symbol
# and more to come has no element, so that step is not required.
def slotStep(+set: +List<Types.Bsr>, +index: Nat, +dot: Nat, +i: Nat, +at: Nat, +end: Nat, last: Bool) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(dot, 0n), Bool.not(last)), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n+dot}, i, at, end}, set))

# Does a node without children (an empty right side) have its step?
def emptyStep(+set: +List<Types.Bsr>, +index: Nat, +at: Nat, +children: +List<Types.Tree>) -> Bool:
  Bool.or(Bool.not(List.is_empty(&2, Types.Tree, children)), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 0n}, at, at, at}, set))

# Are all derivation steps of a node's children in the set? The node uses
# production `index` and starts at i; `forest` holds its children from number
# dot + 1 on, and the first of them starts at `at`. Each child completes a slot,
# and a child node also needs its own steps.
def embeddedChildren(forest: +List<Types.Tree>, +set: +List<Types.Bsr>, +index: Nat, +dot: Nat, +i: Nat, +at: Nat) -> Bool:
  match forest:
    case Nil{}:
      True{}
    case Con{Types.Leaf{+kind}, +rest}:
      Bool.and(slotStep(set, index, dot, i, at, 1n+at, List.is_empty(&2, Types.Tree, rest)), embeddedChildren(rest, set, index, 1n+dot, i, 1n+at))
    case Con{Types.Node{+q, +children}, +rest}:
      +end = Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(children)))
      Bool.and(
        slotStep(set, index, dot, i, at, end, List.is_empty(&2, Types.Tree, rest)),
        Bool.and(
          Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at)),
          embeddedChildren(rest, set, index, 1n+dot, i, end)))

# Is every derivation step of the tree in the set, when the tree starts at position i?
# The positions come from the tree itself: each child starts where the leaves of the
# children before it end.
def embedded(tree: Types.Tree, +set: +List<Types.Bsr>, +i: Nat) -> Bool:
  match tree:
    case Types.Leaf{kind}:
      False{}
    case Types.Node{+index, +children}:
      Bool.and(emptyStep(set, index, i, children), embeddedChildren(children, set, index, 0n, i, i))

# Where the last child starts, when the first starts at `at`.
def lastStart(forest: +List<Types.Tree>, +at: Nat) -> Nat:
  match forest:
    case Nil{}:
      at
    case Con{tree, Nil{}}:
      at
    case Con{+tree, Con{+next, +more}}:
      lastStart(next <> more, Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves([tree]))))

# The step for the whole node: all its children recognized.
def rootStep(tree: Types.Tree, +i: Nat) -> Types.Bsr:
  match tree:
    case Types.Leaf{kind}:
      Types.Bsr{Types.Slot{0n, 0n}, i, i, i}
    case Types.Node{+index, +children}:
      Types.Bsr{Types.Slot{index, List.length(&2, Types.Tree, children)}, i, lastStart(children, i), Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(children)))}


# ---- Positions in the grammar ----
#
# The scans over the grammar walk its tail, but a parse tree names a production by
# its index in the whole grammar. `dropP(o, grammar) == rest` keeps track of that.

def dropP(n: Nat, productions: +List<Types.Production>) -> +List<Types.Production>:
  match n:
    case 0n:
      productions
    case 1n+p:
      match productions:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          dropP(p, t)


law productions_nil_is_not_cons:
  for -p: Types.Production
  for -r: +List<Types.Production>
  for e: {[] == p <> r : +List<Types.Production>}
  Empty

def productions_nil_is_not_cons(p, r, e):
  Lemma.false_is_not_true(Equal.sym(Bool, True{}, False{}, Equal.cong(+List<Types.Production>, Bool, l => List.is_empty(&2, Types.Production, l), [], p <> r, e)))


# After the production at index o, the tail starts at index o + 1.
law drop_next:
  for +grammar: +List<Types.Production>
  for o: Nat
  for +p: Types.Production
  for +r: +List<Types.Production>
  for e: {dropP(o, grammar) == p <> r : +List<Types.Production>}
  {dropP(1n+o, grammar) == r : +List<Types.Production>}

def drop_next(grammar, o, p, r, e):
  match grammar o:
    case Nil{} 0n:
      Empty.absurd({dropP(1n, []) == r : +List<Types.Production>}, productions_nil_is_not_cons(p, r, e))
    case Nil{} 1n+q:
      Empty.absurd({dropP(1n+1n+q, []) == r : +List<Types.Production>}, productions_nil_is_not_cons(p, r, e))
    case Con{h, t} 0n:
      %Equal.sym(+List<Types.Production>, h <> t, p <> r, e) : {dropP(1n, _) == r : +List<Types.Production>}
      {==}
    case Con{h, t} 1n+q:
      drop_next(t, q, p, r, e)


# ---- Sanity laws about the specification ----

def GrammarLaws.only_empty_fits_nothing(forest, grammar, fitting):
  match forest:
    case Nil{}:
      {==}
    case Con{Types.Leaf{kind}, trees}:
      Empty.absurd({Types.Leaf{kind} <> trees == [] : +List<Types.Tree>}, Lemma.false_is_not_true(fitting))
    case Con{Types.Node{index, children}, trees}:
      Empty.absurd({Types.Node{index, children} <> trees == [] : +List<Types.Tree>}, Lemma.false_is_not_true(fitting))


def GrammarLaws.terminal_spells_itself(forest, grammar, kind, fitting):
  match forest:
    case Nil{}:
      Empty.absurd({GrammarLaws.leaves([]) == [kind] : +List<Nat>}, Lemma.false_is_not_true(fitting))
    case Con{Types.Leaf{+k}, +trees}:
      +both = fitting
      kIsKind = Lemma.nat_eq_sound(k, kind, Lemma.and_true_left(Nat.is_eq(k, kind), GrammarLaws.fits(trees, grammar, []), both))
      treesEmpty = GrammarLaws.only_empty_fits_nothing(trees, grammar, Lemma.and_true_right_side(Nat.is_eq(k, kind), GrammarLaws.fits(trees, grammar, []), both))
      %Equal.sym(+List<Types.Tree>, trees, [], treesEmpty) : {k <> GrammarLaws.leaves(_) == [kind] : +List<Nat>}
      %Equal.sym(Nat, k, kind, kIsKind) : {[_] == [kind] : +List<Nat>}
      {==}
    case Con{Types.Node{index, children}, trees}:
      Empty.absurd({GrammarLaws.leaves(Types.Node{index, children} <> trees) == [kind] : +List<Nat>}, Lemma.false_is_not_true(fitting))


def GrammarLaws.empty_grammar_derives_nothing(forest, id, fitting):
  match forest:
    case Nil{}:
      Lemma.false_is_not_true(fitting)
    case Con{Types.Leaf{kind}, trees}:
      Lemma.false_is_not_true(fitting)
    case Con{Types.Node{index, children}, trees}:
      Lemma.false_is_not_true(fitting)


# ---- Building parse trees ----

# What the production at index o (where the tail of the grammar starts) says.
law lhs_at:
  for +grammar: +List<Types.Production>
  for o: Nat
  for +lhs: Nat
  for +rhs: +List<Types.Symbol>
  for +r: +List<Types.Production>
  for e: {dropP(o, grammar) == Types.Production{lhs, rhs} <> r : +List<Types.Production>}
  {Types.lhsIs(grammar, o, lhs) == True{} : Bool}

def lhs_at(grammar, o, lhs, rhs, r, e):
  match grammar o:
    case Nil{} 0n:
      Empty.absurd({Types.lhsIs([], 0n, lhs) == True{} : Bool}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Nil{} 1n+q:
      Empty.absurd({Types.lhsIs([], 1n+q, lhs) == True{} : Bool}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Con{h, t} 0n:
      %Equal.sym(+List<Types.Production>, h <> t, Types.Production{lhs, rhs} <> r, e) : {Types.lhsIs(_, 0n, lhs) == True{} : Bool}
      Lemma.nat_eq_refl(lhs)
    case Con{Types.Production{hl, hr}, t} 1n+q:
      lhs_at(t, q, lhs, rhs, r, e)


law rhs_at:
  for +grammar: +List<Types.Production>
  for o: Nat
  for -lhs: Nat
  for +rhs: +List<Types.Symbol>
  for -r: +List<Types.Production>
  for e: {dropP(o, grammar) == Types.Production{lhs, rhs} <> r : +List<Types.Production>}
  {Types.rhsOf(grammar, o) == rhs : +List<Types.Symbol>}

def rhs_at(grammar, o, lhs, rhs, r, e):
  match grammar o:
    case Nil{} 0n:
      Empty.absurd({Types.rhsOf([], 0n) == rhs : +List<Types.Symbol>}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Nil{} 1n+q:
      Empty.absurd({Types.rhsOf([], 1n+q) == rhs : +List<Types.Symbol>}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Con{h, t} 0n:
      %Equal.sym(+List<Types.Production>, h <> t, Types.Production{lhs, rhs} <> r, e) : {Types.rhsOf(_, 0n) == rhs : +List<Types.Symbol>}
      {==}
    case Con{Types.Production{hl, hr}, t} 1n+q:
      rhs_at(t, q, lhs, rhs, r, e)


# A forest fits a sequence when its first tree fits the first symbol and the rest fits the rest.
law fits_cons_intro:
  for t: Types.Tree
  for -ts: +List<Types.Tree>
  for s: Types.Symbol
  for -ss: +List<Types.Symbol>
  for +grammar: +List<Types.Production>
  for +first: {GrammarLaws.fits([t], grammar, [s]) == True{} : Bool}
  for rest: {GrammarLaws.fits(ts, grammar, ss) == True{} : Bool}
  {GrammarLaws.fits(t <> ts, grammar, s <> ss) == True{} : Bool}

def fits_cons_intro(t, ts, s, ss, grammar, first, rest):
  match t s:
    case Types.Leaf{+kind} Types.Terminal{+k}:
      Lemma.and_true_intro(Nat.is_eq(kind, k), GrammarLaws.fits(ts, grammar, ss), Lemma.and_true_left(Nat.is_eq(kind, k), True{}, first), rest)
    case Types.Leaf{kind} Types.Nonterminal{id}:
      Empty.absurd({GrammarLaws.fits(Types.Leaf{kind} <> ts, grammar, Types.Nonterminal{id} <> ss) == True{} : Bool}, Lemma.false_is_not_true(first))
    case Types.Node{index, children} Types.Terminal{k}:
      Empty.absurd({GrammarLaws.fits(Types.Node{index, children} <> ts, grammar, Types.Terminal{k} <> ss) == True{} : Bool}, Lemma.false_is_not_true(first))
    case Types.Node{+index, +children} Types.Nonterminal{+id}:
      inner = Lemma.and_true_right_side(Types.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}), first)
      Lemma.and_true_intro(
        Types.lhsIs(grammar, index, id),
        Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)),
        Lemma.and_true_left(Types.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}), first),
        Lemma.and_true_intro(
          GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)),
          GrammarLaws.fits(ts, grammar, ss),
          Lemma.and_true_left(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}, inner),
          rest))


# The leaves of a forest are the leaves of its first tree, then of the rest.
law leaves_cons:
  for t: Types.Tree
  for +ts: +List<Types.Tree>
  {GrammarLaws.leaves(t <> ts) == List.append(&2, Nat, GrammarLaws.leaves([t]), GrammarLaws.leaves(ts)) : +List<Nat>}

def leaves_cons(t, ts):
  match t:
    case Types.Leaf{kind}:
      {==}
    case Types.Node{index, +children}:
      %Equal.sym(+List<Nat>, List.append(&2, Nat, GrammarLaws.leaves(children), []), GrammarLaws.leaves(children), Lemma.append_nil_right(GrammarLaws.leaves(children))) : {List.append(&2, Nat, GrammarLaws.leaves(children), GrammarLaws.leaves(ts)) == List.append(&2, Nat, _, GrammarLaws.leaves(ts)) : +List<Nat>}
      {==}


law node_leaves:
  for -o: Nat
  for +children: +List<Types.Tree>
  for -w: +List<Nat>
  for e: {GrammarLaws.leaves(children) == w : +List<Nat>}
  {GrammarLaws.leaves([Types.Node{o, children}]) == w : +List<Nat>}

def node_leaves(o, children, w, e):
  Equal.trans(+List<Nat>, List.append(&2, Nat, GrammarLaws.leaves(children), []), GrammarLaws.leaves(children), w, Lemma.append_nil_right(GrammarLaws.leaves(children)), e)


law pair_leaves:
  for +tb: Types.Tree
  for +tc: Types.Tree
  for -wl: +List<Nat>
  for -wr: +List<Nat>
  for eb: {GrammarLaws.leaves([tb]) == wl : +List<Nat>}
  for ec: {GrammarLaws.leaves([tc]) == wr : +List<Nat>}
  {GrammarLaws.leaves([tb, tc]) == List.append(&2, Nat, wl, wr) : +List<Nat>}

def pair_leaves(tb, tc, wl, wr, eb, ec):
  Equal.trans(
    +List<Nat>,
    GrammarLaws.leaves([tb, tc]),
    List.append(&2, Nat, GrammarLaws.leaves([tb]), GrammarLaws.leaves([tc])),
    List.append(&2, Nat, wl, wr),
    leaves_cons(tb, [tc]),
    Lemma.append_congr(GrammarLaws.leaves([tb]), GrammarLaws.leaves([tc]), wl, wr, eb, ec))


# ======== CYK: COMPLETENESS ========

# ---- Membership ----

law nat_member_pick:
  for +x: Nat
  for +y: Nat
  for +rest: +List<Nat>
  for +ys: +List<Nat>
  for cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Grammar.natMember(x, rest) == True{} : Bool}>
  for searchRest: {Grammar.natMember(x, rest) == True{} : Bool} -> {Grammar.natMember(x, List.append(&2, Nat, rest, ys)) == True{} : Bool}
  {Bool.or(Nat.is_eq(x, y), Grammar.natMember(x, List.append(&2, Nat, rest, ys))) == True{} : Bool}

def nat_member_pick(x, y, rest, ys, cases, searchRest):
  match cases:
    case Inl{isY}:
      Lemma.or_true_left_intro(Nat.is_eq(x, y), Grammar.natMember(x, List.append(&2, Nat, rest, ys)), isY)
    case Inr{inRest}:
      Lemma.or_true_right_intro(Nat.is_eq(x, y), Grammar.natMember(x, List.append(&2, Nat, rest, ys)), searchRest(inRest))


law nat_member_append_left:
  for +x: Nat
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for e: {Grammar.natMember(x, xs) == True{} : Bool}
  {Grammar.natMember(x, List.append(&2, Nat, xs, ys)) == True{} : Bool}

def nat_member_append_left(x, xs, ys, e):
  match xs:
    case Nil{}:
      Empty.absurd({Grammar.natMember(x, ys) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Con{+y, +rest}:
      nat_member_pick(x, y, rest, ys, Lemma.or_true_cases(Nat.is_eq(x, y), Grammar.natMember(x, rest), e), inRest => nat_member_append_left(x, rest, ys, inRest))


law nat_member_append_right:
  for +x: Nat
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for e: {Grammar.natMember(x, ys) == True{} : Bool}
  {Grammar.natMember(x, List.append(&2, Nat, xs, ys)) == True{} : Bool}

def nat_member_append_right(x, xs, ys, e):
  match xs:
    case Nil{}:
      e
    case Con{+y, rest}:
      Lemma.or_true_right_intro(Nat.is_eq(x, y), Grammar.natMember(x, List.append(&2, Nat, rest, ys)), nat_member_append_right(x, rest, ys, e))


law keep_nat_keeps:
  for keep: Bool
  for +lhs: Nat
  for -others: +List<Nat>
  for +a: Nat
  for e: {Grammar.natMember(a, others) == True{} : Bool}
  {Grammar.natMember(a, Grammar.keepNat(keep, lhs, others)) == True{} : Bool}

def keep_nat_keeps(keep, lhs, others, a, e):
  match keep:
    case False{}:
      e
    case True{}:
      Lemma.or_true_right_intro(Nat.is_eq(a, lhs), Grammar.natMember(a, others), e)


# ---- Lookups find the computed cell ----

# A lookup skips a row of another length.
law lookup_skip_row:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +len: Nat
  for +s: Nat
  for +l: Nat
  for +rest: +List<Grammar.Cell>
  for +ne: {Nat.is_eq(len, l) == False{} : Bool}
  for remaining: Nat
  {Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, remaining), rest), s, l) == Grammar.lookup(rest, s, l) : +List<Nat>}

def lookup_skip_row(grammar, inputTokens, table, len, s, l, rest, ne, remaining):
  match remaining:
    case 0n:
      {==}
    case 1n+(+st):
      %Equal.sym(Bool, Nat.is_eq(len, l), False{}, ne) : {Grammar.pickCell(Bool.and(_, Nat.is_eq(st, s)), Grammar.cellNonterminals(grammar, inputTokens, table, st, len), Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, st), rest), s, l)) == Grammar.lookup(rest, s, l) : +List<Nat>}
      lookup_skip_row(grammar, inputTokens, table, len, s, l, rest, ne, st)


law row_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +len: Nat
  for +s: Nat
  for -rest: +List<Grammar.Cell>
  for +st: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(st, s) == found : Bool}
  for lt: {Nat.is_lt(s, 1n+st) == True{} : Bool}
  for searchRow: {Nat.is_lt(s, st) == True{} : Bool} -> {Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, st), rest), s, len) == Grammar.cellNonterminals(grammar, inputTokens, table, s, len) : +List<Nat>}
  {Grammar.pickCell(Bool.and(True{}, found), Grammar.cellNonterminals(grammar, inputTokens, table, st, len), Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, st), rest), s, len)) == Grammar.cellNonterminals(grammar, inputTokens, table, s, len) : +List<Nat>}

def row_pick(grammar, inputTokens, table, len, s, rest, st, found, foundEq, lt, searchRow):
  match found:
    case True{}:
      %Lemma.nat_eq_sound(st, s, foundEq) : {Grammar.cellNonterminals(grammar, inputTokens, table, st, len) == Grammar.cellNonterminals(grammar, inputTokens, table, _, len) : +List<Nat>}
      {==}
    case False{}:
      searchRow(Lemma.lt_succ_ne(s, st, lt, foundEq))


# A lookup of a start inside the row finds the cell computed for it.
law lookup_in_row:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +len: Nat
  for +s: Nat
  for +rest: +List<Grammar.Cell>
  for remaining: Nat
  for lt: {Nat.is_lt(s, remaining) == True{} : Bool}
  {Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, remaining), rest), s, len) == Grammar.cellNonterminals(grammar, inputTokens, table, s, len) : +List<Nat>}

def lookup_in_row(grammar, inputTokens, table, len, s, rest, remaining, lt):
  match remaining:
    case 0n:
      Empty.absurd({Grammar.lookup(rest, s, len) == Grammar.cellNonterminals(grammar, inputTokens, table, s, len) : +List<Nat>}, Lemma.lt_zero_false(s, lt))
    case 1n+(+st):
      %Equal.sym(Bool, Nat.is_eq(len, len), True{}, Lemma.nat_eq_refl(len)) : {Grammar.pickCell(Bool.and(_, Nat.is_eq(st, s)), Grammar.cellNonterminals(grammar, inputTokens, table, st, len), Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, table, len, st), rest), s, len)) == Grammar.cellNonterminals(grammar, inputTokens, table, s, len) : +List<Nat>}
      row_pick(grammar, inputTokens, table, len, s, rest, st, Nat.is_eq(st, s), {==}, lt, ltSt => lookup_in_row(grammar, inputTokens, table, len, s, rest, st, ltSt))


law built_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +p: Nat
  for +f: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(f, p) == found : Bool}
  for le: {Nat.is_le(p, f) == True{} : Bool}
  for lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for searchShorter: {Nat.is_le(1n+p, f) == True{} : Bool} -> {Grammar.lookup(Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f), s, 1n+p) == Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), p), s, 1n+p) : +List<Nat>}
  {Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f), 1n+f, List.length(&2, Nat, inputTokens)), Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f)), s, 1n+p) == Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), p), s, 1n+p) : +List<Nat>}

def built_pick(grammar, inputTokens, s, p, f, found, foundEq, le, lt, searchShorter):
  match found:
    case True{}:
      %Lemma.nat_eq_sound(f, p, foundEq) : {Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f), 1n+f, List.length(&2, Nat, inputTokens)), Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f)), s, 1n+_) == Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), _), s, 1n+_) : +List<Nat>}
      lookup_in_row(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f), 1n+f, s, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f), List.length(&2, Nat, inputTokens), lt)
    case False{}:
      +shorter = Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), f)
      Equal.trans(
        +List<Nat>,
        Grammar.lookup(List.append(&2, Grammar.Cell, Grammar.row(grammar, inputTokens, shorter, 1n+f, List.length(&2, Nat, inputTokens)), shorter), s, 1n+p),
        Grammar.lookup(shorter, s, 1n+p),
        Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), p), s, 1n+p),
        lookup_skip_row(grammar, inputTokens, shorter, 1n+f, s, 1n+p, shorter, foundEq, List.length(&2, Nat, inputTokens)),
        searchShorter(Lemma.le_succ_ne(p, f, le, foundEq)))


# For a span of length p + 1 <= fuel that starts inside the input, the lookup
# returns the cell computed from the table of the shorter spans.
law lookup_built:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +p: Nat
  for fuel: Nat
  for le: {Nat.is_le(1n+p, fuel) == True{} : Bool}
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  {Grammar.lookup(Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), fuel), s, 1n+p) == Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), p), s, 1n+p) : +List<Nat>}

def lookup_built(grammar, inputTokens, s, p, fuel, le, lt):
  match fuel:
    case 0n:
      Empty.absurd({Grammar.lookup([], s, 1n+p) == Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), p), s, 1n+p) : +List<Nat>}, Lemma.false_is_not_true(le))
    case 1n+(+f):
      built_pick(grammar, inputTokens, s, p, f, Nat.is_eq(f, p), {==}, le, lt, shorterLe => lookup_built(grammar, inputTokens, s, p, f, shorterLe, lt))


# ---- The grammar scans find every matching production ----

# Tests on right sides, used to refute impossible shapes and to read off symbols.
def isSingleTerminal(l: +List<Types.Symbol>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{Types.Terminal{k}, Nil{}}:
      True{}
    case Con{Types.Terminal{k}, Con{x, more}}:
      False{}
    case Con{Types.Nonterminal{b}, more}:
      False{}


def terminalOf(l: +List<Types.Symbol>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{Types.Terminal{k}, more}:
      k
    case Con{Types.Nonterminal{b}, more}:
      0n


def isNonterminalPair(l: +List<Types.Symbol>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{Types.Terminal{k}, more}:
      False{}
    case Con{Types.Nonterminal{b}, Nil{}}:
      False{}
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{k}, more}}:
      False{}
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      True{}
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      False{}


def firstNonterminalOf(l: +List<Types.Symbol>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{Types.Terminal{k}, more}:
      0n
    case Con{Types.Nonterminal{b}, more}:
      b


def secondNonterminalOf(l: +List<Types.Symbol>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{x, Nil{}}:
      0n
    case Con{x, Con{Types.Terminal{k}, more}}:
      0n
    case Con{x, Con{Types.Nonterminal{c}, more}}:
      c


law terminal_head:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +rest: +List<Types.Production>
  for +a: Nat
  for +kind: Nat
  for lhsOk: {Nat.is_eq(lhs, a) == True{} : Bool}
  for rhsOk: {rhs == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {Grammar.natMember(a, Grammar.terminalNonterminals(Types.Production{lhs, rhs} <> rest, kind)) == True{} : Bool}

def terminal_head(lhs, rhs, rest, a, kind, lhsOk, rhsOk):
  match rhs:
    case Nil{}:
      Empty.absurd({Grammar.natMember(a, Grammar.terminalNonterminals(Types.Production{lhs, []} <> rest, kind)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), [], [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Terminal{+k}, Nil{}}:
      kIsKind = Equal.cong(+List<Types.Symbol>, Nat, l => terminalOf(l), [Types.Terminal{k}], [Types.Terminal{kind}], rhsOk)
      %Equal.sym(Nat, k, kind, kIsKind) : {Grammar.natMember(a, Grammar.keepNat(Nat.is_eq(_, kind), lhs, Grammar.terminalNonterminals(rest, kind))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(kind, kind), True{}, Lemma.nat_eq_refl(kind)) : {Grammar.natMember(a, Grammar.keepNat(_, lhs, Grammar.terminalNonterminals(rest, kind))) == True{} : Bool}
      Lemma.or_true_left_intro(Nat.is_eq(a, lhs), Grammar.natMember(a, Grammar.terminalNonterminals(rest, kind)), Equal.trans(Bool, Nat.is_eq(a, lhs), Nat.is_eq(lhs, a), True{}, Lemma.nat_eq_symm(a, lhs), lhsOk))
    case Con{Types.Terminal{k}, Con{x, more}}:
      Empty.absurd({Grammar.natMember(a, Grammar.terminalNonterminals(Types.Production{lhs, Types.Terminal{k} <> x <> more} <> rest, kind)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Terminal{k} <> x <> more, [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Nonterminal{b}, more}:
      Empty.absurd({Grammar.natMember(a, Grammar.terminalNonterminals(Types.Production{lhs, Types.Nonterminal{b} <> more} <> rest, kind)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Nonterminal{b} <> more, [Types.Terminal{kind}], rhsOk)))


law terminal_skip:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +rest: +List<Types.Production>
  for +kind: Nat
  for +a: Nat
  for e: {Grammar.natMember(a, Grammar.terminalNonterminals(rest, kind)) == True{} : Bool}
  {Grammar.natMember(a, Grammar.terminalNonterminals(Types.Production{lhs, rhs} <> rest, kind)) == True{} : Bool}

def terminal_skip(lhs, rhs, rest, kind, a, e):
  match rhs:
    case Nil{}:
      e
    case Con{Types.Terminal{+k}, Nil{}}:
      keep_nat_keeps(Nat.is_eq(k, kind), lhs, Grammar.terminalNonterminals(rest, kind), a, e)
    case Con{Types.Terminal{k}, Con{x, more}}:
      e
    case Con{Types.Nonterminal{b}, more}:
      e


# If production `index` is a = "kind", then terminalNonterminals finds a.
law terminal_nts_complete:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +kind: Nat
  for index: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {Grammar.natMember(a, Grammar.terminalNonterminals(grammar, kind)) == True{} : Bool}

def terminal_nts_complete(grammar, a, kind, index, lhsOk, rhsOk):
  match grammar index:
    case Nil{} _:
      Empty.absurd({Grammar.natMember(a, Grammar.terminalNonterminals([], kind)) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Con{Types.Production{+lhs, +rhs}, +rest} 0n:
      terminal_head(lhs, rhs, rest, a, kind, lhsOk, rhsOk)
    case Con{Types.Production{+lhs, +rhs}, +rest} 1n+i:
      terminal_skip(lhs, rhs, rest, kind, a, terminal_nts_complete(rest, a, kind, i, lhsOk, rhsOk))


law binary_head:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +rest: +List<Types.Production>
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for lhsOk: {Nat.is_eq(lhs, a) == True{} : Bool}
  for rhsOk: {rhs == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for inLefts: {Grammar.natMember(b, lefts) == True{} : Bool}
  for inRights: {Grammar.natMember(c, rights) == True{} : Bool}
  {Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, rhs} <> rest, lefts, rights)) == True{} : Bool}

def binary_head(lhs, rhs, rest, a, b, c, lefts, rights, lhsOk, rhsOk, inLefts, inRights):
  match rhs:
    case Con{Types.Nonterminal{+b2}, Con{Types.Nonterminal{+c2}, Nil{}}}:
      +sameRhs = rhsOk
      bEq = Equal.cong(+List<Types.Symbol>, Nat, l => firstNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      cEq = Equal.cong(+List<Types.Symbol>, Nat, l => secondNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      %Equal.sym(Nat, b2, b, bEq) : {Grammar.natMember(a, Grammar.keepNat(Bool.and(Grammar.natMember(_, lefts), Grammar.natMember(c2, rights)), lhs, Grammar.binaryNonterminals(rest, lefts, rights))) == True{} : Bool}
      %Equal.sym(Nat, c2, c, cEq) : {Grammar.natMember(a, Grammar.keepNat(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(_, rights)), lhs, Grammar.binaryNonterminals(rest, lefts, rights))) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), True{}, Lemma.and_true_intro(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), inLefts, inRights)) : {Grammar.natMember(a, Grammar.keepNat(_, lhs, Grammar.binaryNonterminals(rest, lefts, rights))) == True{} : Bool}
      Lemma.or_true_left_intro(Nat.is_eq(a, lhs), Grammar.natMember(a, Grammar.binaryNonterminals(rest, lefts, rights)), Equal.trans(Bool, Nat.is_eq(a, lhs), Nat.is_eq(lhs, a), True{}, Lemma.nat_eq_symm(a, lhs), lhsOk))
    case Nil{}:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, []} <> rest, lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Terminal{k}, more}:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, Types.Terminal{k} <> more} <> rest, lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Terminal{k} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Nil{}}:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, [Types.Nonterminal{b2}]} <> rest, lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [Types.Nonterminal{b2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Terminal{k}, more}}:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Terminal{k} <> more} <> rest, lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Terminal{k} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Nonterminal{c2}, Con{x, more}}}:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more} <> rest, lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))


law binary_skip:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +rest: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +a: Nat
  for e: {Grammar.natMember(a, Grammar.binaryNonterminals(rest, lefts, rights)) == True{} : Bool}
  {Grammar.natMember(a, Grammar.binaryNonterminals(Types.Production{lhs, rhs} <> rest, lefts, rights)) == True{} : Bool}

def binary_skip(lhs, rhs, rest, lefts, rights, a, e):
  match rhs:
    case Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Nil{}}}:
      keep_nat_keeps(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), lhs, Grammar.binaryNonterminals(rest, lefts, rights), a, e)
    case Nil{}:
      e
    case Con{Types.Terminal{k}, more}:
      e
    case Con{Types.Nonterminal{b}, Nil{}}:
      e
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{k}, more}}:
      e
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      e


# If production `index` is a = b c, with b in lefts and c in rights, then binaryNonterminals finds a.
law binary_nts_complete:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for index: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +inLefts: {Grammar.natMember(b, lefts) == True{} : Bool}
  for +inRights: {Grammar.natMember(c, rights) == True{} : Bool}
  {Grammar.natMember(a, Grammar.binaryNonterminals(grammar, lefts, rights)) == True{} : Bool}

def binary_nts_complete(grammar, a, b, c, lefts, rights, index, lhsOk, rhsOk, inLefts, inRights):
  match grammar index:
    case Nil{} _:
      Empty.absurd({Grammar.natMember(a, Grammar.binaryNonterminals([], lefts, rights)) == True{} : Bool}, Lemma.false_is_not_true(lhsOk))
    case Con{Types.Production{+lhs, +rhs}, +rest} 0n:
      binary_head(lhs, rhs, rest, a, b, c, lefts, rights, lhsOk, rhsOk, inLefts, inRights)
    case Con{Types.Production{+lhs, +rhs}, +rest} 1n+i:
      binary_skip(lhs, rhs, rest, lefts, rights, a, binary_nts_complete(rest, a, b, c, lefts, rights, i, lhsOk, rhsOk, inLefts, inRights))


# ---- The split loop tries every split ----

law split_pick:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +a: Nat
  for +kp: Nat
  for +m: Nat
  for +smaller: Nat
  for +right: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(kp, smaller) == found : Bool}
  for kle: {Nat.is_le(kp, smaller) == True{} : Bool}
  for sum: {Nat.add(1n+kp, m) == Nat.add(1n+smaller, right) : Nat}
  for hit: {Grammar.natMember(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m))) == True{} : Bool}
  for searchLater: {Nat.is_le(1n+kp, smaller) == True{} : Bool} -> {Nat.add(1n+kp, m) == Nat.add(smaller, 1n+right) : Nat} -> {Grammar.natMember(a, Grammar.splitNonterminals(grammar, table, s, smaller, 1n+right)) == True{} : Bool}
  {Grammar.natMember(a, List.append(&2, Nat, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right)), Grammar.splitNonterminals(grammar, table, s, smaller, 1n+right))) == True{} : Bool}

def split_pick(grammar, table, s, a, kp, m, smaller, right, found, foundEq, kle, sum, hit, searchLater):
  match found:
    case True{}:
      +kpIsSmaller = Lemma.nat_eq_sound(kp, smaller, foundEq)
      sameSum = Equal.trans(Nat, Nat.add(1n+kp, m), Nat.add(1n+smaller, right), Nat.add(1n+kp, right), sum, Equal.cong(Nat, Nat, n => Nat.add(1n+n, right), smaller, kp, Equal.sym(Nat, kp, smaller, kpIsSmaller)))
      mIsRight = Lemma.add_cancel_left(1n+kp, m, right, sameSum)
      %kpIsSmaller : {Grammar.natMember(a, List.append(&2, Nat, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+_), Grammar.lookup(table, Nat.add(s, 1n+_), right)), Grammar.splitNonterminals(grammar, table, s, _, 1n+right))) == True{} : Bool}
      %mIsRight : {Grammar.natMember(a, List.append(&2, Nat, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), _)), Grammar.splitNonterminals(grammar, table, s, kp, 1n+_))) == True{} : Bool}
      nat_member_append_left(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m)), Grammar.splitNonterminals(grammar, table, s, kp, 1n+m), hit)
    case False{}:
      kle2 = Lemma.le_succ_ne(kp, smaller, kle, Equal.trans(Bool, Nat.is_eq(smaller, kp), Nat.is_eq(kp, smaller), False{}, Lemma.nat_eq_symm(smaller, kp), foundEq))
      sum2 = Equal.trans(Nat, Nat.add(1n+kp, m), 1n+Nat.add(smaller, right), Nat.add(smaller, 1n+right), sum, Equal.sym(Nat, Nat.add(smaller, 1n+right), 1n+Nat.add(smaller, right), Lemma.add_succ_right(smaller, right)))
      nat_member_append_right(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right)), Grammar.splitNonterminals(grammar, table, s, smaller, 1n+right), searchLater(kle2, sum2))


# If the split with left length kp + 1 finds a, the split loop finds a.
law split_member:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +a: Nat
  for +kp: Nat
  for +m: Nat
  for left: Nat
  for +right: Nat
  for kle: {Nat.is_le(1n+kp, left) == True{} : Bool}
  for sum: {Nat.add(1n+kp, m) == Nat.add(left, right) : Nat}
  for +hit: {Grammar.natMember(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m))) == True{} : Bool}
  {Grammar.natMember(a, Grammar.splitNonterminals(grammar, table, s, left, right)) == True{} : Bool}

def split_member(grammar, table, s, a, kp, m, left, right, kle, sum, hit):
  match left:
    case 0n:
      Empty.absurd({Grammar.natMember(a, []) == True{} : Bool}, Lemma.false_is_not_true(kle))
    case 1n+(+smaller):
      split_pick(grammar, table, s, a, kp, m, smaller, right, Nat.is_eq(kp, smaller), {==}, kle, sum, hit, kle2 => sum2 => split_member(grammar, table, s, a, kp, m, smaller, 1n+right, kle2, sum2, hit))


# ---- The shape of trees in a binary-form grammar ----

# The right side of a production in binary form is "t" or B C.
def RhsShape(+grammar: +List<Types.Production>, +index: Nat) -> Type:
  Either<&k: Nat -> {Types.rhsOf(grammar, index) == [Types.Terminal{k}] : +List<Types.Symbol>}, &b: Nat -> &c: Nat -> {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}>


law binary_head_shape:
  for -lhs: Nat
  for rhs: +List<Types.Symbol>
  for -rest: +List<Types.Production>
  for binary: {GrammarLaws.IsBinaryForm(Types.Production{lhs, rhs} <> rest) == True{} : Bool}
  RhsShape(Types.Production{lhs, rhs} <> rest, 0n)

def binary_head_shape(lhs, rhs, rest, binary):
  match rhs:
    case Con{Types.Terminal{k}, Nil{}}:
      Inl{(k, {==})}
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      Inr{(b, (c, {==}))}
    case Nil{}:
      Empty.absurd(RhsShape(Types.Production{lhs, []} <> rest, 0n), Lemma.false_is_not_true(binary))
    case Con{Types.Terminal{k}, Con{x, more}}:
      Empty.absurd(RhsShape(Types.Production{lhs, Types.Terminal{k} <> x <> more} <> rest, 0n), Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Nil{}}:
      Empty.absurd(RhsShape(Types.Production{lhs, [Types.Nonterminal{b}]} <> rest, 0n), Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{k}, more}}:
      Empty.absurd(RhsShape(Types.Production{lhs, Types.Nonterminal{b} <> Types.Terminal{k} <> more} <> rest, 0n), Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      Empty.absurd(RhsShape(Types.Production{lhs, Types.Nonterminal{b} <> Types.Nonterminal{c} <> x <> more} <> rest, 0n), Lemma.false_is_not_true(binary))


law binary_rest:
  for -lhs: Nat
  for rhs: +List<Types.Symbol>
  for -rest: +List<Types.Production>
  for binary: {GrammarLaws.IsBinaryForm(Types.Production{lhs, rhs} <> rest) == True{} : Bool}
  {GrammarLaws.IsBinaryForm(rest) == True{} : Bool}

def binary_rest(lhs, rhs, rest, binary):
  match rhs:
    case Con{Types.Terminal{k}, Nil{}}:
      binary
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      binary
    case Nil{}:
      Empty.absurd({GrammarLaws.IsBinaryForm(rest) == True{} : Bool}, Lemma.false_is_not_true(binary))
    case Con{Types.Terminal{k}, Con{x, more}}:
      Empty.absurd({GrammarLaws.IsBinaryForm(rest) == True{} : Bool}, Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Nil{}}:
      Empty.absurd({GrammarLaws.IsBinaryForm(rest) == True{} : Bool}, Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{k}, more}}:
      Empty.absurd({GrammarLaws.IsBinaryForm(rest) == True{} : Bool}, Lemma.false_is_not_true(binary))
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      Empty.absurd({GrammarLaws.IsBinaryForm(rest) == True{} : Bool}, Lemma.false_is_not_true(binary))


law binary_rhs:
  for +grammar: +List<Types.Production>
  for index: Nat
  for +a: Nat
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  RhsShape(grammar, index)

def binary_rhs(grammar, index, a, binary, lhsOk):
  match grammar index:
    case Nil{} _:
      Empty.absurd(RhsShape([], index), Lemma.false_is_not_true(lhsOk))
    case Con{Types.Production{+lhs, +rhs}, +rest} 0n:
      binary_head_shape(lhs, rhs, rest, binary)
    case Con{Types.Production{+lhs, +rhs}, +rest} 1n+i:
      binary_rhs(rest, i, a, binary_rest(lhs, rhs, rest, binary), lhsOk)


law fits_at:
  for -children: +List<Types.Tree>
  for -grammar: +List<Types.Production>
  for -r1: +List<Types.Symbol>
  for -r2: +List<Types.Symbol>
  for e: {r1 == r2 : +List<Types.Symbol>}
  for f: {GrammarLaws.fits(children, grammar, r1) == True{} : Bool}
  {GrammarLaws.fits(children, grammar, r2) == True{} : Bool}

def fits_at(children, grammar, r1, r2, e, f):
  %e : {GrammarLaws.fits(children, grammar, _) == True{} : Bool}
  f


law fits_cons_left:
  for t: Types.Tree
  for -ts: +List<Types.Tree>
  for s: Types.Symbol
  for -ss: +List<Types.Symbol>
  for +grammar: +List<Types.Production>
  for e: {GrammarLaws.fits(t <> ts, grammar, s <> ss) == True{} : Bool}
  {GrammarLaws.fits([t], grammar, [s]) == True{} : Bool}

def fits_cons_left(t, ts, s, ss, grammar, e):
  match t s:
    case Types.Leaf{+kind} Types.Terminal{+k}:
      Lemma.and_true_intro(Nat.is_eq(kind, k), True{}, Lemma.and_true_left(Nat.is_eq(kind, k), GrammarLaws.fits(ts, grammar, ss), e), {==})
    case Types.Leaf{kind} Types.Nonterminal{id}:
      Empty.absurd({GrammarLaws.fits([Types.Leaf{kind}], grammar, [Types.Nonterminal{id}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Types.Node{index, children} Types.Terminal{k}:
      Empty.absurd({GrammarLaws.fits([Types.Node{index, children}], grammar, [Types.Terminal{k}]) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Types.Node{+index, +children} Types.Nonterminal{+id}:
      +both = e
      inner = Lemma.and_true_right_side(Types.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), both)
      Lemma.and_true_intro(
        Types.lhsIs(grammar, index, id),
        Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}),
        Lemma.and_true_left(Types.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), both),
        Lemma.and_true_intro(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}, Lemma.and_true_left(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss), inner), {==}))


law fits_cons_right:
  for t: Types.Tree
  for +ts: +List<Types.Tree>
  for s: Types.Symbol
  for +ss: +List<Types.Symbol>
  for +grammar: +List<Types.Production>
  for e: {GrammarLaws.fits(t <> ts, grammar, s <> ss) == True{} : Bool}
  {GrammarLaws.fits(ts, grammar, ss) == True{} : Bool}

def fits_cons_right(t, ts, s, ss, grammar, e):
  match t s:
    case Types.Leaf{+kind} Types.Terminal{+k}:
      Lemma.and_true_right_side(Nat.is_eq(kind, k), GrammarLaws.fits(ts, grammar, ss), e)
    case Types.Leaf{kind} Types.Nonterminal{id}:
      Empty.absurd({GrammarLaws.fits(ts, grammar, ss) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Types.Node{index, children} Types.Terminal{k}:
      Empty.absurd({GrammarLaws.fits(ts, grammar, ss) == True{} : Bool}, Lemma.false_is_not_true(e))
    case Types.Node{+index, +children} Types.Nonterminal{+id}:
      Lemma.and_true_right_side(
        GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)),
        GrammarLaws.fits(ts, grammar, ss),
        Lemma.and_true_right_side(Types.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), e))


law trees_cons_is_not_nil:
  for -t: Types.Tree
  for -ts: +List<Types.Tree>
  for e: {t <> ts == [] : +List<Types.Tree>}
  Empty

def trees_cons_is_not_nil(t, ts, e):
  Lemma.false_is_not_true(Equal.cong(+List<Types.Tree>, Bool, l => List.is_empty(&2, Types.Tree, l), t <> ts, [], e))


# What a node for nonterminal a says about itself: its production belongs to a,
# and its children fit the production's right side.
law node_lhs:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +children: +List<Types.Tree>
  for fitting: {GrammarLaws.fits([Types.Node{index, children}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  {Types.lhsIs(grammar, index, a) == True{} : Bool}

def node_lhs(grammar, index, a, children, fitting):
  Lemma.and_true_left(Types.lhsIs(grammar, index, a), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}), fitting)


law node_children:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +children: +List<Types.Tree>
  for fitting: {GrammarLaws.fits([Types.Node{index, children}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  {GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)) == True{} : Bool}

def node_children(grammar, index, a, children, fitting):
  Lemma.and_true_left(
    GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)),
    True{},
    Lemma.and_true_right_side(Types.lhsIs(grammar, index, a), Bool.and(GrammarLaws.fits(children, grammar, Types.rhsOf(grammar, index)), True{}), fitting))


law no_children_pick:
  for -grammar: +List<Types.Production>
  for -index: Nat
  for shape: RhsShape(grammar, index)
  for childFit: {GrammarLaws.fits([], grammar, Types.rhsOf(grammar, index)) == True{} : Bool}
  Empty

def no_children_pick(grammar, index, shape, childFit):
  match shape:
    case Inl{(k, e)}:
      Lemma.false_is_not_true(fits_at([], grammar, Types.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit))
    case Inr{(b, (c, e))}:
      Lemma.false_is_not_true(fits_at([], grammar, Types.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))


# In binary form a node has children.
law no_children:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +fitting: {GrammarLaws.fits([Types.Node{index, []}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  Empty

def no_children(grammar, index, a, binary, fitting):
  no_children_pick(grammar, index, binary_rhs(grammar, index, a, binary, node_lhs(grammar, index, a, [], fitting)), node_children(grammar, index, a, [], fitting))


# One child: it is a leaf, and the production is a = "kind".
def OneChild(+grammar: +List<Types.Production>, +index: Nat, +a: Nat, +child: Types.Tree) -> Type:
  &kind: Nat -> {child == Types.Leaf{kind} : Types.Tree} & {Types.lhsIs(grammar, index, a) == True{} : Bool} & {Types.rhsOf(grammar, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}


law one_child_pick:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for child: Types.Tree
  for shape: RhsShape(grammar, index)
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for childFit: {GrammarLaws.fits([child], grammar, Types.rhsOf(grammar, index)) == True{} : Bool}
  OneChild(grammar, index, a, child)

def one_child_pick(grammar, index, a, child, shape, lhsOk, childFit):
  match child:
    case Types.Leaf{+kind}:
      match shape:
        case Inl{(k0, e0)}:
          +k = {k0 : Nat}
          +e = {e0 : {Types.rhsOf(grammar, index) == [Types.Terminal{k}] : +List<Types.Symbol>}}
          fitsK = fits_at([Types.Leaf{kind}], grammar, Types.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)
          kindIsK = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), True{}, fitsK))
          (kind, ({==}, (lhsOk, Equal.trans(+List<Types.Symbol>, Types.rhsOf(grammar, index), [Types.Terminal{k}], [Types.Terminal{kind}], e, Equal.cong(Nat, +List<Types.Symbol>, n => [Types.Terminal{n}], k, kind, Equal.sym(Nat, kind, k, kindIsK))))))
        case Inr{(b, (c, e))}:
          Empty.absurd(OneChild(grammar, index, a, Types.Leaf{kind}), Lemma.false_is_not_true(fits_at([Types.Leaf{kind}], grammar, Types.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit)))
    case Types.Node{+i, +children}:
      match shape:
        case Inl{(k, e)}:
          Empty.absurd(OneChild(grammar, index, a, Types.Node{i, children}), Lemma.false_is_not_true(fits_at([Types.Node{i, children}], grammar, Types.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)))
        case Inr{(b0, (c0, e))}:
          +b = {b0 : Nat}
          +c = {c0 : Nat}
          Empty.absurd(OneChild(grammar, index, a, Types.Node{i, children}), Lemma.false_is_not_true(fits_cons_right(Types.Node{i, children}, [], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fits_at([Types.Node{i, children}], grammar, Types.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))))


law one_child_facts:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +child: Types.Tree
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +fitting: {GrammarLaws.fits([Types.Node{index, [child]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  OneChild(grammar, index, a, child)

def one_child_facts(grammar, index, a, child, binary, fitting):
  +lhsOk = node_lhs(grammar, index, a, [child], fitting)
  one_child_pick(grammar, index, a, child, binary_rhs(grammar, index, a, binary, lhsOk), lhsOk, node_children(grammar, index, a, [child], fitting))


# Two children: the production is a = b c, and the children fit b and c.
def TwoChildren(+grammar: +List<Types.Production>, +index: Nat, +a: Nat, +first: Types.Tree, +second: Types.Tree) -> Type:
  &b: Nat -> &c: Nat -> {Types.lhsIs(grammar, index, a) == True{} : Bool} & {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>} & {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool} & {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}


law two_children_pick:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for shape: RhsShape(grammar, index)
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for childFit: {GrammarLaws.fits([first, second], grammar, Types.rhsOf(grammar, index)) == True{} : Bool}
  TwoChildren(grammar, index, a, first, second)

def two_children_pick(grammar, index, a, first, second, shape, lhsOk, childFit):
  match shape:
    case Inl{(k0, e)}:
      +k = {k0 : Nat}
      fitsK = fits_at([first, second], grammar, Types.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)
      restFits = fits_cons_right(first, [second], Types.Terminal{k}, [], grammar, fitsK)
      Empty.absurd(TwoChildren(grammar, index, a, first, second), trees_cons_is_not_nil(second, [], GrammarLaws.only_empty_fits_nothing([second], grammar, restFits)))
    case Inr{(b0, (c0, e0))}:
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      +e = {e0 : {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}}
      +fitsBC = fits_at([first, second], grammar, Types.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit)
      (b, (c, (lhsOk, (e, (fits_cons_left(first, [second], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fitsBC), fits_cons_right(first, [second], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fitsBC))))))


law two_children_facts:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +fitting: {GrammarLaws.fits([Types.Node{index, [first, second]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  TwoChildren(grammar, index, a, first, second)

def two_children_facts(grammar, index, a, first, second, binary, fitting):
  +lhsOk = node_lhs(grammar, index, a, [first, second], fitting)
  two_children_pick(grammar, index, a, first, second, binary_rhs(grammar, index, a, binary, lhsOk), lhsOk, node_children(grammar, index, a, [first, second], fitting))


law many_children_pick:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +t1: Types.Tree
  for +t2: Types.Tree
  for +t3: Types.Tree
  for +more: +List<Types.Tree>
  for shape: RhsShape(grammar, index)
  for childFit: {GrammarLaws.fits(t1 <> t2 <> t3 <> more, grammar, Types.rhsOf(grammar, index)) == True{} : Bool}
  Empty

def many_children_pick(grammar, index, t1, t2, t3, more, shape, childFit):
  match shape:
    case Inl{(k0, e)}:
      +k = {k0 : Nat}
      restFits = fits_cons_right(t1, t2 <> t3 <> more, Types.Terminal{k}, [], grammar, fits_at(t1 <> t2 <> t3 <> more, grammar, Types.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit))
      trees_cons_is_not_nil(t2, t3 <> more, GrammarLaws.only_empty_fits_nothing(t2 <> t3 <> more, grammar, restFits))
    case Inr{(b0, (c0, e))}:
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      afterFirst = fits_cons_right(t1, t2 <> t3 <> more, Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fits_at(t1 <> t2 <> t3 <> more, grammar, Types.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))
      afterSecond = fits_cons_right(t2, t3 <> more, Types.Nonterminal{c}, [], grammar, afterFirst)
      trees_cons_is_not_nil(t3, more, GrammarLaws.only_empty_fits_nothing(t3 <> more, grammar, afterSecond))


# In binary form a node has at most two children.
law many_children:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +t1: Types.Tree
  for +t2: Types.Tree
  for +t3: Types.Tree
  for +more: +List<Types.Tree>
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +fitting: {GrammarLaws.fits([Types.Node{index, t1 <> t2 <> t3 <> more}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  Empty

def many_children(grammar, index, a, t1, t2, t3, more, binary, fitting):
  many_children_pick(grammar, index, t1, t2, t3, more, binary_rhs(grammar, index, a, binary, node_lhs(grammar, index, a, t1 <> t2 <> t3 <> more, fitting)), node_children(grammar, index, a, t1 <> t2 <> t3 <> more, fitting))


# ---- Every tree in a binary-form grammar has leaves ----

law one_nonempty:
  for -grammar: +List<Types.Production>
  for +index: Nat
  for -a: Nat
  for -child: Types.Tree
  for facts: OneChild(grammar, index, a, child)
  {List.is_empty(&2, Nat, GrammarLaws.leaves([Types.Node{index, [child]}])) == False{} : Bool}

def one_nonempty(grammar, index, a, child, facts):
  match facts:
    case (kind, (isLeaf, rest)):
      %Equal.sym(Types.Tree, child, Types.Leaf{kind}, isLeaf) : {List.is_empty(&2, Nat, GrammarLaws.leaves([Types.Node{index, [_]}])) == False{} : Bool}
      {==}


law two_nonempty:
  for -grammar: +List<Types.Production>
  for +index: Nat
  for -a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for facts: TwoChildren(grammar, index, a, first, second)
  for firstNonempty: @b: Nat -> {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool} -> {List.is_empty(&2, Nat, GrammarLaws.leaves([first])) == False{} : Bool}
  {List.is_empty(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])) == False{} : Bool}

def two_nonempty(grammar, index, a, first, second, facts, firstNonempty):
  match facts:
    case (b, (c, (lhsOk, (rhsOk, (f1, f2))))):
      joined = node_leaves(index, [first, second], List.append(&2, Nat, GrammarLaws.leaves([first]), GrammarLaws.leaves([second])), pair_leaves(first, second, GrammarLaws.leaves([first]), GrammarLaws.leaves([second]), {==}, {==}))
      %Equal.sym(+List<Nat>, GrammarLaws.leaves([Types.Node{index, [first, second]}]), List.append(&2, Nat, GrammarLaws.leaves([first]), GrammarLaws.leaves([second])), joined) : {List.is_empty(&2, Nat, _) == False{} : Bool}
      Lemma.nonempty_append(GrammarLaws.leaves([first]), GrammarLaws.leaves([second]), firstNonempty(b, f1))


law tree_nonempty:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  {List.is_empty(&2, Nat, GrammarLaws.leaves([t])) == False{} : Bool}

def tree_nonempty(t, grammar, binary, a, fitting):
  match t:
    case Types.Leaf{kind}:
      {==}
    case Types.Node{+index, children}:
      match children:
        case Nil{}:
          Empty.absurd({List.is_empty(&2, Nat, GrammarLaws.leaves([Types.Node{index, []}])) == False{} : Bool}, no_children(grammar, index, a, binary, fitting))
        case Con{+t1, Nil{}}:
          one_nonempty(grammar, index, a, t1, one_child_facts(grammar, index, a, t1, binary, fitting))
        case Con{+t1, Con{+t2, Nil{}}}:
          two_nonempty(grammar, index, a, t1, t2, two_children_facts(grammar, index, a, t1, t2, binary, fitting), b => f => tree_nonempty(t1, grammar, binary, b, f))
        case Con{+t1, Con{+t2, Con{+t3, +more}}}:
          Empty.absurd({List.is_empty(&2, Nat, GrammarLaws.leaves([Types.Node{index, t1 <> t2 <> t3 <> more}])) == False{} : Bool}, many_children(grammar, index, a, t1, t2, t3, more, binary, fitting))


# ---- Completeness: induction over the parse tree ----

# The cell type the induction talks about: nonterminal a is in the cell for (s, l).
def InCell(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +a: Nat, +s: Nat, +l: Nat, +fuel: Nat) -> Type:
  {Grammar.natMember(a, Grammar.lookup(Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), fuel), s, l)) == True{} : Bool}


# A one-leaf node a = "kind" for a span of length 1.
law leaf_cell:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +fuel: Nat
  for +index: Nat
  for +child: Types.Tree
  for facts: OneChild(grammar, index, a, child)
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{index, [child]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [child]}])) == l : Nat}
  for le: {Nat.is_le(l, fuel) == True{} : Bool}
  InCell(grammar, inputTokens, a, s, l, fuel)

def leaf_cell(grammar, inputTokens, a, s, l, fuel, index, child, facts, at, len, le):
  match facts:
    case (+kind, (+isLeaf, (lhsOk, rhsOk))):
      leafLeaves = Equal.cong(Types.Tree, +List<Nat>, t => GrammarLaws.leaves([Types.Node{index, [t]}]), child, Types.Leaf{kind}, isLeaf)
      +lIsOne = Equal.trans(Nat, l, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [child]}])), 1n, Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [child]}])), l, len), Equal.cong(Types.Tree, Nat, t => List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [t]}])), child, Types.Leaf{kind}, isLeaf))
      +at1 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, 1n), Lemma.slice(inputTokens, s, l), [kind], Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), 1n, l, Equal.sym(Nat, l, 1n, lIsOne)), Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, l), GrammarLaws.leaves([Types.Node{index, [child]}]), [kind], at, leafLeaves))
      le1 = Equal.trans(Bool, Nat.is_le(1n, fuel), Nat.is_le(l, fuel), True{}, Equal.cong(Nat, Bool, n => Nat.is_le(n, fuel), 1n, l, Equal.sym(Nat, l, 1n, lIsOne)), le)
      built = lookup_built(grammar, inputTokens, s, 0n, fuel, le1, Lemma.slice_start_lt(inputTokens, s, 1n, kind, [], at1))
      %Equal.sym(Nat, l, 1n, lIsOne) : InCell(grammar, inputTokens, a, s, _, fuel)
      %Equal.sym(+List<Nat>, Grammar.lookup(Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), fuel), s, 1n), Grammar.cellNonterminals(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), 0n), s, 1n), built) : {Grammar.natMember(a, _) == True{} : Bool}
      %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, inputTokens, s), Some{kind}, Lemma.slice_get(inputTokens, s, kind, at1)) : {Grammar.natMember(a, Grammar.tokenNonterminals(grammar, _)) == True{} : Bool}
      terminal_nts_complete(grammar, a, kind, index, lhsOk, rhsOk)


# The induction hypothesis for a child tree, passed as a function.
def ChildInCell(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +child: Types.Tree) -> Type:
  @b: Nat -> @s: Nat -> @l: Nat -> @fuel: Nat -> {GrammarLaws.fits([child], grammar, [Types.Nonterminal{b}]) == True{} : Bool} -> {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([child]) : +List<Nat>} -> {List.length(&2, Nat, GrammarLaws.leaves([child])) == l : Nat} -> {Nat.is_le(l, fuel) == True{} : Bool} -> InCell(grammar, inputTokens, b, s, l, fuel)


law pair_cell_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +fuel: Nat
  for +index: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for +b: Nat
  for +c: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +f1: {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for +f2: {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  for w1: +List<Nat>
  for w2: +List<Nat>
  for +e1: {GrammarLaws.leaves([first]) == w1 : +List<Nat>}
  for +e2: {GrammarLaws.leaves([second]) == w2 : +List<Nat>}
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{index, [first, second]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])) == l : Nat}
  for le: {Nat.is_le(l, fuel) == True{} : Bool}
  for firstInCell: ChildInCell(grammar, inputTokens, first)
  for secondInCell: ChildInCell(grammar, inputTokens, second)
  InCell(grammar, inputTokens, a, s, l, fuel)

def pair_cell_parts(grammar, inputTokens, binary, a, s, l, fuel, index, first, second, b, c, lhsOk, rhsOk, f1, f2, w1, w2, e1, e2, at, len, le, firstInCell, secondInCell):
  match w1 w2:
    case Nil{} _:
      Empty.absurd(InCell(grammar, inputTokens, a, s, l, fuel), Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, Nat, GrammarLaws.leaves([first])), False{}, Equal.sym(Bool, List.is_empty(&2, Nat, GrammarLaws.leaves([first])), True{}, Equal.cong(+List<Nat>, Bool, x => List.is_empty(&2, Nat, x), GrammarLaws.leaves([first]), [], e1)), tree_nonempty(first, grammar, binary, b, f1))))
    case Con{h1, r1} Nil{}:
      Empty.absurd(InCell(grammar, inputTokens, a, s, l, fuel), Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, Nat, GrammarLaws.leaves([second])), False{}, Equal.sym(Bool, List.is_empty(&2, Nat, GrammarLaws.leaves([second])), True{}, Equal.cong(+List<Nat>, Bool, x => List.is_empty(&2, Nat, x), GrammarLaws.leaves([second]), [], e2)), tree_nonempty(second, grammar, binary, c, f2))))
    case Con{+h1, +r1} Con{+h2, +r2}:
      +p1 = List.length(&2, Nat, r1)
      +q2 = List.length(&2, Nat, r2)
      +m = {Nat.add(p1, q2) : Nat}
      +w1 = {h1 <> r1 : +List<Nat>}
      +w2 = {h2 <> r2 : +List<Nat>}
      +joined = node_leaves(index, [first, second], List.append(&2, Nat, w1, w2), pair_leaves(first, second, w1, w2, e1, e2))
      +lSum = Equal.trans(Nat, l, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])), Nat.add(1n+p1, 1n+q2), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])), l, len), Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(1n+p1, 1n+q2), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([Types.Node{index, [first, second]}]), List.append(&2, Nat, w1, w2), joined), Lemma.length_append(w1, w2)))
      +lTwo = Equal.trans(Nat, l, Nat.add(1n+p1, 1n+q2), 1n+1n+m, lSum, Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p1, 1n+q2), 1n+m, Lemma.add_succ_right(p1, q2)))
      +atSum = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, Nat.add(1n+p1, 1n+q2)), Lemma.slice(inputTokens, s, l), List.append(&2, Nat, w1, w2), Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), Nat.add(1n+p1, 1n+q2), l, Equal.sym(Nat, l, Nat.add(1n+p1, 1n+q2), lSum)), Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, l), GrammarLaws.leaves([Types.Node{index, [first, second]}]), List.append(&2, Nat, w1, w2), at, joined))
      at1 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, 1n+p1), w1, GrammarLaws.leaves([first]), Lemma.slice_left(inputTokens, s, w1, w2, atSum), Equal.sym(+List<Nat>, GrammarLaws.leaves([first]), w1, e1))
      at2 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, Nat.add(s, 1n+p1), 1n+q2), w2, GrammarLaws.leaves([second]), Lemma.slice_right(inputTokens, s, w1, w2, atSum), Equal.sym(+List<Nat>, GrammarLaws.leaves([second]), w2, e2))
      len1 = Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([first]), w1, e1)
      len2 = Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([second]), w2, e2)
      +shorter = Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), 1n+m)
      inLefts = firstInCell(b, s, 1n+p1, 1n+m, f1, at1, len1, Lemma.le_add_right(p1, q2))
      inRights = secondInCell(c, Nat.add(s, 1n+p1), 1n+q2, 1n+m, f2, at2, len2, Lemma.le_add_left(p1, q2))
      hit = binary_nts_complete(grammar, a, b, c, Grammar.lookup(shorter, s, 1n+p1), Grammar.lookup(shorter, Nat.add(s, 1n+p1), 1n+q2), index, lhsOk, rhsOk, inLefts, inRights)
      sum = Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p1, 1n+q2), Nat.add(m, 1n), Equal.trans(Nat, Nat.add(p1, 1n+q2), 1n+m, Nat.add(m, 1n), Lemma.add_succ_right(p1, q2), Equal.sym(Nat, Nat.add(m, 1n), 1n+m, Lemma.add_one_right(m))))
      splitHit = split_member(grammar, shorter, s, a, p1, 1n+q2, 1n+m, 1n, Lemma.le_add_right(p1, q2), sum, hit)
      leFuel = Equal.trans(Bool, Nat.is_le(1n+1n+m, fuel), Nat.is_le(l, fuel), True{}, Equal.cong(Nat, Bool, n => Nat.is_le(n, fuel), 1n+1n+m, l, Equal.sym(Nat, l, 1n+1n+m, lTwo)), le)
      built = lookup_built(grammar, inputTokens, s, 1n+m, fuel, leFuel, Lemma.slice_start_lt(inputTokens, s, Nat.add(1n+p1, 1n+q2), h1, List.append(&2, Nat, r1, w2), atSum))
      %Equal.sym(Nat, l, 1n+1n+m, lTwo) : InCell(grammar, inputTokens, a, s, _, fuel)
      %Equal.sym(+List<Nat>, Grammar.lookup(Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), fuel), s, 1n+1n+m), Grammar.cellNonterminals(grammar, inputTokens, shorter, s, 1n+1n+m), built) : {Grammar.natMember(a, _) == True{} : Bool}
      splitHit


# A node a = b c over two children: both halves are in their cells (by induction),
# so the split loop of the cell for the whole span finds a.
law pair_cell:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +fuel: Nat
  for +index: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for facts: TwoChildren(grammar, index, a, first, second)
  for w1: +List<Nat>
  for w2: +List<Nat>
  for +e1: {GrammarLaws.leaves([first]) == w1 : +List<Nat>}
  for +e2: {GrammarLaws.leaves([second]) == w2 : +List<Nat>}
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{index, [first, second]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{index, [first, second]}])) == l : Nat}
  for le: {Nat.is_le(l, fuel) == True{} : Bool}
  for firstInCell: ChildInCell(grammar, inputTokens, first)
  for secondInCell: ChildInCell(grammar, inputTokens, second)
  InCell(grammar, inputTokens, a, s, l, fuel)

def pair_cell(grammar, inputTokens, binary, a, s, l, fuel, index, first, second, facts, w1, w2, e1, e2, at, len, le, firstInCell, secondInCell):
  match facts:
    case (b, (c, (lhsOk, (rhsOk, (f1, f2))))):
      pair_cell_parts(grammar, inputTokens, binary, a, s, l, fuel, index, first, second, b, c, lhsOk, rhsOk, f1, f2, w1, w2, e1, e2, at, len, le, firstInCell, secondInCell)


# The heart of completeness: if a tree for nonterminal a spells the slice (s, l),
# then a is in the cell for (s, l) of every table that has spans of length l.
law cell_complete:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +fuel: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([t]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([t])) == l : Nat}
  for le: {Nat.is_le(l, fuel) == True{} : Bool}
  InCell(grammar, inputTokens, a, s, l, fuel)

def cell_complete(t, grammar, inputTokens, binary, a, s, l, fuel, fitting, at, len, le):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd(InCell(grammar, inputTokens, a, s, l, fuel), Lemma.false_is_not_true(fitting))
    case Types.Node{+index, children}:
      match children:
        case Nil{}:
          Empty.absurd(InCell(grammar, inputTokens, a, s, l, fuel), no_children(grammar, index, a, binary, fitting))
        case Con{+t1, Nil{}}:
          leaf_cell(grammar, inputTokens, a, s, l, fuel, index, t1, one_child_facts(grammar, index, a, t1, binary, fitting), at, len, le)
        case Con{+t1, Con{+t2, Nil{}}}:
          pair_cell(
            grammar, inputTokens, binary, a, s, l, fuel, index, t1, t2,
            two_children_facts(grammar, index, a, t1, t2, binary, fitting),
            GrammarLaws.leaves([t1]), GrammarLaws.leaves([t2]), {==}, {==},
            at, len, le,
            b1 => s1 => l1 => fuel1 => f1 => at1 => len1 => le1 => cell_complete(t1, grammar, inputTokens, binary, b1, s1, l1, fuel1, f1, at1, len1, le1),
            b2 => s2 => l2 => fuel2 => f2 => at2 => len2 => le2 => cell_complete(t2, grammar, inputTokens, binary, b2, s2, l2, fuel2, f2, at2, len2, le2))
        case Con{+t1, Con{+t2, Con{+t3, +more}}}:
          Empty.absurd(InCell(grammar, inputTokens, a, s, l, fuel), many_children(grammar, index, a, t1, t2, t3, more, binary, fitting))


# ======== THE BSR SET ========

# ---- Does a right side say "t", for the token t? ----

def tokenMatches(rhs: +List<Types.Symbol>, token: Maybe<&2, Nat>) -> Bool:
  match rhs token:
    case Nil{} _:
      False{}
    case Con{Types.Terminal{k}, Nil{}} None{}:
      False{}
    case Con{Types.Terminal{k}, Nil{}} Some{kind}:
      Nat.is_eq(k, kind)
    case Con{Types.Terminal{k}, Con{x, more}} _:
      False{}
    case Con{Types.Nonterminal{b}, more} _:
      False{}


def TokenParts(+rhs: +List<Types.Symbol>, +token: Maybe<&2, Nat>) -> Type:
  &k: Nat -> {rhs == [Types.Terminal{k}] : +List<Types.Symbol>} & {token == Some{k} : Maybe<&2, Nat>}


law token_matches_parts:
  for rhs: +List<Types.Symbol>
  for token: Maybe<&2, Nat>
  for e: {tokenMatches(rhs, token) == True{} : Bool}
  TokenParts(rhs, token)

def token_matches_parts(rhs, token, e):
  match rhs token:
    case Nil{} _:
      Empty.absurd(TokenParts([], token), Lemma.false_is_not_true(e))
    case Con{Types.Terminal{k}, Nil{}} None{}:
      Empty.absurd(TokenParts([Types.Terminal{k}], None{}), Lemma.false_is_not_true(e))
    case Con{Types.Terminal{+k}, Nil{}} Some{+kind}:
      kIsKind = Lemma.nat_eq_sound(k, kind, e)
      (k, ({==}, Equal.cong(Nat, Maybe<&2, Nat>, n => {Some{n} : Maybe<&2, Nat>}, kind, k, Equal.sym(Nat, k, kind, kIsKind))))
    case Con{Types.Terminal{k}, Con{x, more}} _:
      Empty.absurd(TokenParts(Types.Terminal{k} <> x <> more, token), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, more} _:
      Empty.absurd(TokenParts(Types.Nonterminal{b} <> more, token), Lemma.false_is_not_true(e))


# ---- Membership in lists of steps ----

law bsr_eq_refl:
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Bool.and(Nat.is_eq(p, p), Bool.and(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))))) == True{} : Bool}

def bsr_eq_refl(p, d, i, k, j):
  Lemma.and_true_intro(Nat.is_eq(p, p), Bool.and(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), Lemma.nat_eq_refl(p),
    Lemma.and_true_intro(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), Lemma.nat_eq_refl(d),
      Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
        Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j)))))


law bsr_member_head:
  for element: Types.Bsr
  for +rest: +List<Types.Bsr>
  {GrammarLaws.bsrMember(element, element <> rest) == True{} : Bool}

def bsr_member_head(element, rest):
  match element:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      Lemma.or_true_left_intro(Bool.and(Nat.is_eq(p, p), Bool.and(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))))), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest), bsr_eq_refl(p, d, i, k, j))


law bsr_member_cons:
  for element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for e: {GrammarLaws.bsrMember(element, rest) == True{} : Bool}
  {GrammarLaws.bsrMember(element, x <> rest) == True{} : Bool}

def bsr_member_cons(element, x, rest, e):
  match element x:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j} Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}:
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest), e)


law bsr_member_append_right:
  for +element: Types.Bsr
  for xs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for e: {GrammarLaws.bsrMember(element, ys) == True{} : Bool}
  {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, xs, ys)) == True{} : Bool}

def bsr_member_append_right(element, xs, ys, e):
  match xs:
    case Nil{}:
      e
    case Con{+x, +rest}:
      bsr_member_cons(element, x, List.append(&2, Types.Bsr, rest, ys), bsr_member_append_right(element, rest, ys, e))


law bsr_member_append_left:
  for element: Types.Bsr
  for xs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for e: {GrammarLaws.bsrMember(element, xs) == True{} : Bool}
  {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, xs, ys)) == True{} : Bool}

def bsr_member_append_left(element, xs, ys, e):
  match element:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      match xs:
        case Nil{}:
          Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, ys) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Con{Types.Bsr{Types.Slot{+p2, +d2}, +i2, +k2, +j2}, +rest}:
          Lemma.or_mono_right(
            Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))),
            GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest),
            GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, List.append(&2, Types.Bsr, rest, ys)),
            e,
            inRest => bsr_member_append_left(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest, ys, inRest))


law bsr_member_keep:
  for keep: Bool
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for element: Types.Bsr
  for e: {GrammarLaws.bsrMember(element, rest) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.keepBsr(keep, x, rest)) == True{} : Bool}

def bsr_member_keep(keep, x, rest, element, e):
  match keep:
    case False{}:
      e
    case True{}:
      bsr_member_cons(element, x, rest, e)


# ---- The scans emit the step of every matching production ----

law terminal_head_member:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +others: +List<Types.Production>
  for +kind: Nat
  for +s: Nat
  for +o: Nat
  for rhsOk: {rhs == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}

def terminal_head_member(lhs, rhs, others, kind, s, o, rhsOk):
  match rhs:
    case Con{Types.Terminal{+k}, Nil{}}:
      kIsKind = Equal.cong(+List<Types.Symbol>, Nat, l => terminalOf(l), [Types.Terminal{k}], [Types.Terminal{kind}], rhsOk)
      %Equal.sym(Nat, k, kind, kIsKind) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.keepBsr(Nat.is_eq(_, kind), Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(kind, kind), True{}, Lemma.nat_eq_refl(kind)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.keepBsr(_, Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}
      bsr_member_head(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))
    case Nil{}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, []} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), [], [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Terminal{k}, Con{x, more}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, Types.Terminal{k} <> x <> more} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Terminal{k} <> x <> more, [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Nonterminal{b}, more}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, Types.Nonterminal{b} <> more} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Nonterminal{b} <> more, [Types.Terminal{kind}], rhsOk)))


law terminal_steps_skip:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +others: +List<Types.Production>
  for +kind: Nat
  for +s: Nat
  for +o: Nat
  for element: Types.Bsr
  for e: {GrammarLaws.bsrMember(element, Grammar.terminalSteps(others, kind, s, 1n+o)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}

def terminal_steps_skip(lhs, rhs, others, kind, s, o, element, e):
  match rhs:
    case Con{Types.Terminal{+k}, Nil{}}:
      bsr_member_keep(Nat.is_eq(k, kind), Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o), element, e)
    case Nil{}:
      e
    case Con{Types.Terminal{k}, Con{x, more}}:
      e
    case Con{Types.Nonterminal{b}, more}:
      e


# If production o + index is A = "kind", the terminal scan emits its leaf step at s.
law terminal_steps_member:
  for rest: +List<Types.Production>
  for +kind: Nat
  for +s: Nat
  for +o: Nat
  for index: Nat
  for rhsOk: {Types.rhsOf(rest, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{Nat.add(o, index), 1n}, s, s, 1n+s}, Grammar.terminalSteps(rest, kind, s, o)) == True{} : Bool}

def terminal_steps_member(rest, kind, s, o, index, rhsOk):
  match rest index:
    case Nil{} _:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{Nat.add(o, index), 1n}, s, s, 1n+s}, []) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), [], [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Production{+lhs, +rhs}, +others} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{_, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}
      terminal_head_member(lhs, rhs, others, kind, s, o, rhsOk)
    case Con{Types.Production{+lhs, +rhs}, +others} 1n+(+i):
      %Equal.sym(Nat, Nat.add(o, 1n+i), 1n+Nat.add(o, i), Lemma.add_succ_right(o, i)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{_, 1n}, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}
      terminal_steps_skip(lhs, rhs, others, kind, s, o, Types.Bsr{Types.Slot{Nat.add(1n+o, i), 1n}, s, s, 1n+s}, terminal_steps_member(others, kind, s, 1n+o, i, rhsOk))


law binary_head_member:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +others: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +o: Nat
  for +b: Nat
  for +c: Nat
  for rhsOk: {rhs == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for inLefts: {Grammar.natMember(b, lefts) == True{} : Bool}
  for inRights: {Grammar.natMember(c, rights) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}

def binary_head_member(lhs, rhs, others, lefts, rights, i, k, j, o, b, c, rhsOk, inLefts, inRights):
  match rhs:
    case Con{Types.Nonterminal{+b2}, Con{Types.Nonterminal{+c2}, Nil{}}}:
      +sameRhs = rhsOk
      bEq = Equal.cong(+List<Types.Symbol>, Nat, l => firstNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      cEq = Equal.cong(+List<Types.Symbol>, Nat, l => secondNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      +later = Grammar.binarySteps(others, lefts, rights, i, k, j, 1n+o)
      %Equal.sym(Nat, b2, b, bEq) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.keepBsr(Bool.and(Grammar.natMember(_, lefts), Grammar.natMember(c2, rights)), Types.Bsr{Types.Slot{o, 2n}, i, k, j}, later)) == True{} : Bool}
      %Equal.sym(Nat, c2, c, cEq) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.keepBsr(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(_, rights)), Types.Bsr{Types.Slot{o, 2n}, i, k, j}, later)) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), True{}, Lemma.and_true_intro(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), inLefts, inRights)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.keepBsr(_, Types.Bsr{Types.Slot{o, 2n}, i, k, j}, later)) == True{} : Bool}
      bsr_member_head(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, later)
    case Nil{}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, []} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Terminal{t}, more}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Terminal{t} <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Terminal{t} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Nil{}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, [Types.Nonterminal{b2}]} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [Types.Nonterminal{b2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Terminal{t}, more}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Terminal{t} <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Terminal{t} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Nonterminal{c2}, Con{x, more}}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))


law binary_steps_skip:
  for +lhs: Nat
  for rhs: +List<Types.Symbol>
  for +others: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +o: Nat
  for element: Types.Bsr
  for e: {GrammarLaws.bsrMember(element, Grammar.binarySteps(others, lefts, rights, i, k, j, 1n+o)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}

def binary_steps_skip(lhs, rhs, others, lefts, rights, i, k, j, o, element, e):
  match rhs:
    case Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Nil{}}}:
      bsr_member_keep(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), Types.Bsr{Types.Slot{o, 2n}, i, k, j}, Grammar.binarySteps(others, lefts, rights, i, k, j, 1n+o), element, e)
    case Nil{}:
      e
    case Con{Types.Terminal{t}, more}:
      e
    case Con{Types.Nonterminal{b}, Nil{}}:
      e
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{t}, more}}:
      e
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      e


# If production o + index is A = b c with b in lefts and c in rights, the binary scan emits its step.
law binary_steps_member:
  for rest: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +o: Nat
  for index: Nat
  for +b: Nat
  for +c: Nat
  for rhsOk: {Types.rhsOf(rest, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +inLefts: {Grammar.natMember(b, lefts) == True{} : Bool}
  for +inRights: {Grammar.natMember(c, rights) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{Nat.add(o, index), 2n}, i, k, j}, Grammar.binarySteps(rest, lefts, rights, i, k, j, o)) == True{} : Bool}

def binary_steps_member(rest, lefts, rights, i, k, j, o, index, b, c, rhsOk, inLefts, inRights):
  match rest index:
    case Nil{} _:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{Nat.add(o, index), 2n}, i, k, j}, []) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Production{+lhs, +rhs}, +others} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{_, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}
      binary_head_member(lhs, rhs, others, lefts, rights, i, k, j, o, b, c, rhsOk, inLefts, inRights)
    case Con{Types.Production{+lhs, +rhs}, +others} 1n+(+index2):
      %Equal.sym(Nat, Nat.add(o, 1n+index2), 1n+Nat.add(o, index2), Lemma.add_succ_right(o, index2)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{_, 2n}, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}
      binary_steps_skip(lhs, rhs, others, lefts, rights, i, k, j, o, Types.Bsr{Types.Slot{Nat.add(1n+o, index2), 2n}, i, k, j}, binary_steps_member(others, lefts, rights, i, k, j, 1n+o, index2, b, c, rhsOk, inLefts, inRights))


# ---- The loops include the step of every span ----

law split_steps_pick:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +element: Types.Bsr
  for +kp: Nat
  for +m: Nat
  for +smaller: Nat
  for +right: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(kp, smaller) == found : Bool}
  for kle: {Nat.is_le(kp, smaller) == True{} : Bool}
  for sum: {Nat.add(1n+kp, m) == Nat.add(1n+smaller, right) : Nat}
  for hit: {GrammarLaws.bsrMember(element, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m), s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, m)), 0n)) == True{} : Bool}
  for searchLater: {Nat.is_le(1n+kp, smaller) == True{} : Bool} -> {Nat.add(1n+kp, m) == Nat.add(smaller, 1n+right) : Nat} -> {GrammarLaws.bsrMember(element, Grammar.splitSteps(grammar, table, s, smaller, 1n+right)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right), s, Nat.add(s, 1n+smaller), Nat.add(s, Nat.add(1n+smaller, right)), 0n), Grammar.splitSteps(grammar, table, s, smaller, 1n+right))) == True{} : Bool}

def split_steps_pick(grammar, table, s, element, kp, m, smaller, right, found, foundEq, kle, sum, hit, searchLater):
  match found:
    case True{}:
      +kpIsSmaller = Lemma.nat_eq_sound(kp, smaller, foundEq)
      sameSum = Equal.trans(Nat, Nat.add(1n+kp, m), Nat.add(1n+smaller, right), Nat.add(1n+kp, right), sum, Equal.cong(Nat, Nat, n => Nat.add(1n+n, right), smaller, kp, Equal.sym(Nat, kp, smaller, kpIsSmaller)))
      mIsRight = Lemma.add_cancel_left(1n+kp, m, right, sameSum)
      %kpIsSmaller : {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+_), Grammar.lookup(table, Nat.add(s, 1n+_), right), s, Nat.add(s, 1n+_), Nat.add(s, Nat.add(1n+_, right)), 0n), Grammar.splitSteps(grammar, table, s, _, 1n+right))) == True{} : Bool}
      %mIsRight : {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), _), s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, _)), 0n), Grammar.splitSteps(grammar, table, s, kp, 1n+_))) == True{} : Bool}
      bsr_member_append_left(element, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m), s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, m)), 0n), Grammar.splitSteps(grammar, table, s, kp, 1n+m), hit)
    case False{}:
      kle2 = Lemma.le_succ_ne(kp, smaller, kle, Equal.trans(Bool, Nat.is_eq(smaller, kp), Nat.is_eq(kp, smaller), False{}, Lemma.nat_eq_symm(smaller, kp), foundEq))
      sum2 = Equal.trans(Nat, Nat.add(1n+kp, m), 1n+Nat.add(smaller, right), Nat.add(smaller, 1n+right), sum, Equal.sym(Nat, Nat.add(smaller, 1n+right), 1n+Nat.add(smaller, right), Lemma.add_succ_right(smaller, right)))
      bsr_member_append_right(element, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right), s, Nat.add(s, 1n+smaller), Nat.add(s, Nat.add(1n+smaller, right)), 0n), Grammar.splitSteps(grammar, table, s, smaller, 1n+right), searchLater(kle2, sum2))


law split_steps_member:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +element: Types.Bsr
  for +kp: Nat
  for +m: Nat
  for left: Nat
  for +right: Nat
  for kle: {Nat.is_le(1n+kp, left) == True{} : Bool}
  for sum: {Nat.add(1n+kp, m) == Nat.add(left, right) : Nat}
  for +hit: {GrammarLaws.bsrMember(element, Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), m), s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, m)), 0n)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.splitSteps(grammar, table, s, left, right)) == True{} : Bool}

def split_steps_member(grammar, table, s, element, kp, m, left, right, kle, sum, hit):
  match left:
    case 0n:
      Empty.absurd({GrammarLaws.bsrMember(element, []) == True{} : Bool}, Lemma.false_is_not_true(kle))
    case 1n+(+smaller):
      split_steps_pick(grammar, table, s, element, kp, m, smaller, right, Nat.is_eq(kp, smaller), {==}, kle, sum, hit, kle2 => sum2 => split_steps_member(grammar, table, s, element, kp, m, smaller, 1n+right, kle2, sum2, hit))


law row_member_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +length: Nat
  for +s: Nat
  for +element: Types.Bsr
  for +st: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(st, s) == found : Bool}
  for lt: {Nat.is_lt(s, 1n+st) == True{} : Bool}
  for m: {GrammarLaws.bsrMember(element, Grammar.spanSteps(grammar, inputTokens, table, s, length)) == True{} : Bool}
  for searchRow: {Nat.is_lt(s, st) == True{} : Bool} -> {GrammarLaws.bsrMember(element, Grammar.rowSteps(grammar, inputTokens, table, length, st)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.spanSteps(grammar, inputTokens, table, st, length), Grammar.rowSteps(grammar, inputTokens, table, length, st))) == True{} : Bool}

def row_member_pick(grammar, inputTokens, table, length, s, element, st, found, foundEq, lt, m, searchRow):
  match found:
    case True{}:
      %Equal.sym(Nat, st, s, Lemma.nat_eq_sound(st, s, foundEq)) : {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.spanSteps(grammar, inputTokens, table, _, length), Grammar.rowSteps(grammar, inputTokens, table, length, st))) == True{} : Bool}
      bsr_member_append_left(element, Grammar.spanSteps(grammar, inputTokens, table, s, length), Grammar.rowSteps(grammar, inputTokens, table, length, st), m)
    case False{}:
      bsr_member_append_right(element, Grammar.spanSteps(grammar, inputTokens, table, st, length), Grammar.rowSteps(grammar, inputTokens, table, length, st), searchRow(Lemma.lt_succ_ne(s, st, lt, foundEq)))


law row_member:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +length: Nat
  for +s: Nat
  for +element: Types.Bsr
  for remaining: Nat
  for lt: {Nat.is_lt(s, remaining) == True{} : Bool}
  for +m: {GrammarLaws.bsrMember(element, Grammar.spanSteps(grammar, inputTokens, table, s, length)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.rowSteps(grammar, inputTokens, table, length, remaining)) == True{} : Bool}

def row_member(grammar, inputTokens, table, length, s, element, remaining, lt, m):
  match remaining:
    case 0n:
      Empty.absurd({GrammarLaws.bsrMember(element, []) == True{} : Bool}, Lemma.lt_zero_false(s, lt))
    case 1n+(+st):
      row_member_pick(grammar, inputTokens, table, length, s, element, st, Nat.is_eq(st, s), {==}, lt, m, ltSt => row_member(grammar, inputTokens, table, length, s, element, st, ltSt, m))


law all_member_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +count: Nat
  for +p: Nat
  for +element: Types.Bsr
  for +f: Nat
  for found: Bool
  for +foundEq: {Nat.is_eq(f, p) == found : Bool}
  for le: {Nat.is_le(p, f) == True{} : Bool}
  for m: {GrammarLaws.bsrMember(element, Grammar.rowSteps(grammar, inputTokens, table, 1n+p, count)) == True{} : Bool}
  for searchShorter: {Nat.is_le(1n+p, f) == True{} : Bool} -> {GrammarLaws.bsrMember(element, Grammar.allSteps(grammar, inputTokens, table, count, f)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.rowSteps(grammar, inputTokens, table, 1n+f, count), Grammar.allSteps(grammar, inputTokens, table, count, f))) == True{} : Bool}

def all_member_pick(grammar, inputTokens, table, count, p, element, f, found, foundEq, le, m, searchShorter):
  match found:
    case True{}:
      %Equal.sym(Nat, f, p, Lemma.nat_eq_sound(f, p, foundEq)) : {GrammarLaws.bsrMember(element, List.append(&2, Types.Bsr, Grammar.rowSteps(grammar, inputTokens, table, 1n+_, count), Grammar.allSteps(grammar, inputTokens, table, count, f))) == True{} : Bool}
      bsr_member_append_left(element, Grammar.rowSteps(grammar, inputTokens, table, 1n+p, count), Grammar.allSteps(grammar, inputTokens, table, count, f), m)
    case False{}:
      bsr_member_append_right(element, Grammar.rowSteps(grammar, inputTokens, table, 1n+f, count), Grammar.allSteps(grammar, inputTokens, table, count, f), searchShorter(Lemma.le_succ_ne(p, f, le, foundEq)))


law all_member:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +count: Nat
  for +p: Nat
  for +element: Types.Bsr
  for fuel: Nat
  for le: {Nat.is_le(1n+p, fuel) == True{} : Bool}
  for +m: {GrammarLaws.bsrMember(element, Grammar.rowSteps(grammar, inputTokens, table, 1n+p, count)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.allSteps(grammar, inputTokens, table, count, fuel)) == True{} : Bool}

def all_member(grammar, inputTokens, table, count, p, element, fuel, le, m):
  match fuel:
    case 0n:
      Empty.absurd({GrammarLaws.bsrMember(element, []) == True{} : Bool}, Lemma.false_is_not_true(le))
    case 1n+(+f):
      all_member_pick(grammar, inputTokens, table, count, p, element, f, Nat.is_eq(f, p), {==}, le, m, leF => all_member(grammar, inputTokens, table, count, p, element, f, leF, m))


# ---- What the BSR set contains ----
#
# Every element of the set is either a leaf step Bsr{Slot{p, 1}, s, s, s + 1} whose
# production is p = "t" with t the token at s, or a step Bsr{Slot{p, 2}, i, k, j}
# whose production is p = B C, with B in the table cell for i .. k and C in the
# cell for k .. j. All three BSR laws start from this fact.

def pairInCells(rhs: +List<Types.Symbol>, +table: +List<Grammar.Cell>, +i: Nat, +k: Nat, +j: Nat) -> Bool:
  match rhs:
    case Nil{}:
      False{}
    case Con{Types.Terminal{t}, more}:
      False{}
    case Con{Types.Nonterminal{b}, Nil{}}:
      False{}
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{t}, more}}:
      False{}
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      Bool.and(Nat.is_lt(i, k), Bool.and(Nat.is_lt(k, j), Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, Nat.sub(k, i))), Grammar.natMember(c, Grammar.lookup(table, k, Nat.sub(j, k))))))
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      False{}


def stepFrom(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Grammar.Cell>, element: Types.Bsr) -> Bool:
  match element:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      Bool.or(
        Bool.and(Nat.is_eq(d, 1n), Bool.and(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tokenMatches(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))))),
        Bool.and(Nat.is_eq(d, 2n), pairInCells(Types.rhsOf(grammar, p), table, i, k, j)))


def allFrom(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +table: +List<Grammar.Cell>, set: +List<Types.Bsr>) -> Bool:
  match set:
    case Nil{}:
      True{}
    case Con{element, rest}:
      Bool.and(stepFrom(grammar, inputTokens, table, element), allFrom(grammar, inputTokens, table, rest))


law from_append:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for xs: +List<Types.Bsr>
  for -ys: +List<Types.Bsr>
  for first: {allFrom(grammar, inputTokens, table, xs) == True{} : Bool}
  for second: {allFrom(grammar, inputTokens, table, ys) == True{} : Bool}
  {allFrom(grammar, inputTokens, table, List.append(&2, Types.Bsr, xs, ys)) == True{} : Bool}

def from_append(grammar, inputTokens, table, xs, ys, first, second):
  match xs:
    case Nil{}:
      second
    case Con{+element, +rest}:
      +both = first
      Lemma.and_true_intro(
        stepFrom(grammar, inputTokens, table, element),
        allFrom(grammar, inputTokens, table, List.append(&2, Types.Bsr, rest, ys)),
        Lemma.and_true_left(stepFrom(grammar, inputTokens, table, element), allFrom(grammar, inputTokens, table, rest), both),
        from_append(grammar, inputTokens, table, rest, ys, Lemma.and_true_right_side(stepFrom(grammar, inputTokens, table, element), allFrom(grammar, inputTokens, table, rest), both), second))


# A leaf step whose production's terminal is the token at s.
law leaf_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +o: Nat
  for +s: Nat
  for matches: {tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s)) == True{} : Bool}
  {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}) == True{} : Bool}

def leaf_from(grammar, inputTokens, table, o, s, matches):
  Lemma.or_true_left_intro(
    Bool.and(Nat.is_eq(1n, 1n), Bool.and(Nat.is_eq(s, s), Bool.and(Nat.is_eq(1n+s, 1n+s), tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s))))),
    Bool.and(Nat.is_eq(1n, 2n), pairInCells(Types.rhsOf(grammar, o), table, s, s, 1n+s)),
    Lemma.and_true_intro(Nat.is_eq(s, s), Bool.and(Nat.is_eq(1n+s, 1n+s), tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s))), Lemma.nat_eq_refl(s),
      Lemma.and_true_intro(Nat.is_eq(1n+s, 1n+s), tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s)), Lemma.nat_eq_refl(1n+s), matches)))


# A binary step whose parts are in the cells for i .. i + 1 + n and the rest.
law binary_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +o: Nat
  for +i: Nat
  for +n: Nat
  for +r: Nat
  for +b: Nat
  for +c: Nat
  for rhsEq: {Types.rhsOf(grammar, o) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for inLefts: {Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)) == True{} : Bool}
  for inRights: {Grammar.natMember(c, Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r)) == True{} : Bool}
  {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{o, 2n}, i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r))}) == True{} : Bool}

def binary_from(grammar, inputTokens, table, o, i, n, r, b, c, rhsEq, inLefts, inRights):
  +k = Nat.add(i, 1n+n)
  +j = Nat.add(i, Nat.add(1n+n, 1n+r))
  %Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, o), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsEq) : {Bool.or(Bool.and(Nat.is_eq(2n, 1n), Bool.and(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, i))))), Bool.and(Nat.is_eq(2n, 2n), pairInCells(_, table, i, k, j))) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(k, i), 1n+n, Lemma.sub_add_left(i, 1n+n)) : {Bool.and(Nat.is_lt(i, k), Bool.and(Nat.is_lt(k, j), Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, _)), Grammar.natMember(c, Grammar.lookup(table, k, Nat.sub(j, k)))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(j, k), 1n+r, Lemma.sub_add_add(i, 1n+n, 1n+r)) : {Bool.and(Nat.is_lt(i, k), Bool.and(Nat.is_lt(k, j), Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, k, _))))) == True{} : Bool}
  Lemma.and_true_intro(Nat.is_lt(i, k), Bool.and(Nat.is_lt(k, j), Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, k, 1n+r)))), Lemma.lt_self_add(i, n),
    Lemma.and_true_intro(Nat.is_lt(k, j), Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, k, 1n+r))), Lemma.lt_offset(i, 1n+n, r),
      Lemma.and_true_intro(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, k, 1n+r)), inLefts, inRights)))


law leaf_matches:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +kind: Nat
  for +s: Nat
  for -lhs: Nat
  for +k: Nat
  for -others: +List<Types.Production>
  for +o: Nat
  for keptEq: {Nat.is_eq(k, kind) == True{} : Bool}
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> others : +List<Types.Production>}
  {tokenMatches(Types.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s)) == True{} : Bool}

def leaf_matches(grammar, inputTokens, kind, s, lhs, k, others, o, keptEq, tokenEq, tail):
  %Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, o), [Types.Terminal{k}], rhs_at(grammar, o, lhs, [Types.Terminal{k}], others, tail)) : {tokenMatches(_, List.get(&2, Nat, inputTokens, s)) == True{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, inputTokens, s), Some{kind}, tokenEq) : {tokenMatches([Types.Terminal{k}], _) == True{} : Bool}
  keptEq


law keep_leaf_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +kind: Nat
  for +s: Nat
  for +lhs: Nat
  for +k: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for keep: Bool
  for keptEq: {Nat.is_eq(k, kind) == keep : Bool}
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> others : +List<Types.Production>}
  for later: {allFrom(grammar, inputTokens, table, Grammar.terminalSteps(others, kind, s, 1n+o)) == True{} : Bool}
  {allFrom(grammar, inputTokens, table, Grammar.keepBsr(keep, Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}

def keep_leaf_from(grammar, inputTokens, table, kind, s, lhs, k, others, o, keep, keptEq, tokenEq, tail, later):
  match keep:
    case False{}:
      later
    case True{}:
      matches = leaf_matches(grammar, inputTokens, kind, s, lhs, k, others, o, keptEq, tokenEq, tail)
      Lemma.and_true_intro(stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{o, 1n}, s, s, 1n+s}), allFrom(grammar, inputTokens, table, Grammar.terminalSteps(others, kind, s, 1n+o)), leaf_from(grammar, inputTokens, table, o, s, matches), later)


law terminal_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +kind: Nat
  for +s: Nat
  for +tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  {allFrom(grammar, inputTokens, table, Grammar.terminalSteps(rest, kind, s, o)) == True{} : Bool}

def terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, rest, o, tail):
  match rest:
    case Nil{}:
      {==}
    case Con{Types.Production{+lhs, [Types.Terminal{+k}]}, +others}:
      keep_leaf_from(
        grammar, inputTokens, table, kind, s, lhs, k, others, o,
        Nat.is_eq(k, kind), {==}, tokenEq, tail,
        terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Terminal{k}]}, others, tail)))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Terminal{+k}, Con{+second, +more}}}, +others}:
      terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{k} <> second <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+first}, +more}}, +others}:
      terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{first} <> more}, others, tail))


law keep_binary_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +i: Nat
  for +n: Nat
  for +r: Nat
  for +lhs: Nat
  for +b: Nat
  for +c: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for keep: Bool
  for +keptEq: {Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r))) == keep : Bool}
  for tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]} <> others : +List<Types.Production>}
  for later: {allFrom(grammar, inputTokens, table, Grammar.binarySteps(others, Grammar.lookup(table, i, 1n+n), Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r), i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r)), 1n+o)) == True{} : Bool}
  {allFrom(grammar, inputTokens, table, Grammar.keepBsr(keep, Types.Bsr{Types.Slot{o, 2n}, i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r))}, Grammar.binarySteps(others, Grammar.lookup(table, i, 1n+n), Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r), i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r)), 1n+o))) == True{} : Bool}

def keep_binary_from(grammar, inputTokens, table, i, n, r, lhs, b, c, others, o, keep, keptEq, tail, later):
  match keep:
    case False{}:
      later
    case True{}:
      +lefts = Grammar.lookup(table, i, 1n+n)
      +rights = Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r)
      Lemma.and_true_intro(
        stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{o, 2n}, i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r))}),
        allFrom(grammar, inputTokens, table, Grammar.binarySteps(others, lefts, rights, i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r)), 1n+o)),
        binary_from(grammar, inputTokens, table, o, i, n, r, b, c, rhs_at(grammar, o, lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}], others, tail), Lemma.and_true_left(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), keptEq), Lemma.and_true_right_side(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), keptEq)),
        later)


law binary_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +i: Nat
  for +n: Nat
  for +r: Nat
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  {allFrom(grammar, inputTokens, table, Grammar.binarySteps(rest, Grammar.lookup(table, i, 1n+n), Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r), i, Nat.add(i, 1n+n), Nat.add(i, Nat.add(1n+n, 1n+r)), o)) == True{} : Bool}

def binary_steps_from(grammar, inputTokens, table, i, n, r, rest, o, tail):
  match rest:
    case Nil{}:
      {==}
    case Con{Types.Production{+lhs, [Types.Nonterminal{+b}, Types.Nonterminal{+c}]}, +others}:
      keep_binary_from(
        grammar, inputTokens, table, i, n, r, lhs, b, c, others, o,
        Bool.and(Grammar.natMember(b, Grammar.lookup(table, i, 1n+n)), Grammar.natMember(c, Grammar.lookup(table, Nat.add(i, 1n+n), 1n+r))), {==}, tail,
        binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, others, tail)))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Terminal{+t}, +more}}, +others}:
      binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{t} <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Nil{}}}, +others}:
      binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}]}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Terminal{+t}, +more}}}, +others}:
      binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Terminal{t} <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Con{+x, +more}}}}, +others}:
      binary_steps_from(grammar, inputTokens, table, i, n, r, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Nonterminal{c} <> x <> more}, others, tail))


law token_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for token: Maybe<&2, Nat>
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == token : Maybe<&2, Nat>}
  {allFrom(grammar, inputTokens, table, Grammar.tokenSteps(grammar, token, s)) == True{} : Bool}

def token_steps_from(grammar, inputTokens, table, s, token, tokenEq):
  match token:
    case None{}:
      {==}
    case Some{+kind}:
      terminal_steps_from(grammar, inputTokens, table, kind, s, tokenEq, grammar, 0n, {==})


law split_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for left: Nat
  for +r: Nat
  {allFrom(grammar, inputTokens, table, Grammar.splitSteps(grammar, table, s, left, 1n+r)) == True{} : Bool}

def split_steps_from(grammar, inputTokens, table, s, left, r):
  match left:
    case 0n:
      {==}
    case 1n+(+smaller):
      from_append(
        grammar, inputTokens, table,
        Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), 1n+r), s, Nat.add(s, 1n+smaller), Nat.add(s, Nat.add(1n+smaller, 1n+r)), 0n),
        Grammar.splitSteps(grammar, table, s, smaller, 1n+1n+r),
        binary_steps_from(grammar, inputTokens, table, s, smaller, r, grammar, 0n, {==}),
        split_steps_from(grammar, inputTokens, table, s, smaller, 1n+r))


law span_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for length: Nat
  {allFrom(grammar, inputTokens, table, Grammar.spanSteps(grammar, inputTokens, table, s, length)) == True{} : Bool}

def span_steps_from(grammar, inputTokens, table, s, length):
  match length:
    case 0n:
      {==}
    case 1n+0n:
      token_steps_from(grammar, inputTokens, table, s, List.get(&2, Nat, inputTokens, s), {==})
    case 1n+1n+(+shorter):
      split_steps_from(grammar, inputTokens, table, s, 1n+shorter, 0n)


law row_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +length: Nat
  for remaining: Nat
  {allFrom(grammar, inputTokens, table, Grammar.rowSteps(grammar, inputTokens, table, length, remaining)) == True{} : Bool}

def row_steps_from(grammar, inputTokens, table, length, remaining):
  match remaining:
    case 0n:
      {==}
    case 1n+(+start):
      from_append(grammar, inputTokens, table, Grammar.spanSteps(grammar, inputTokens, table, start, length), Grammar.rowSteps(grammar, inputTokens, table, length, start), span_steps_from(grammar, inputTokens, table, start, length), row_steps_from(grammar, inputTokens, table, length, start))


law all_steps_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +count: Nat
  for fuel: Nat
  {allFrom(grammar, inputTokens, table, Grammar.allSteps(grammar, inputTokens, table, count, fuel)) == True{} : Bool}

def all_steps_from(grammar, inputTokens, table, count, fuel):
  match fuel:
    case 0n:
      {==}
    case 1n+(+shorter):
      from_append(grammar, inputTokens, table, Grammar.rowSteps(grammar, inputTokens, table, 1n+shorter, count), Grammar.allSteps(grammar, inputTokens, table, count, shorter), row_steps_from(grammar, inputTokens, table, 1n+shorter, count), all_steps_from(grammar, inputTokens, table, count, shorter))


# The table the BSR set is built from.
def Table(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>) -> +List<Grammar.Cell>:
  +count = List.length(&2, Nat, inputTokens)
  Grammar.buildTable(grammar, inputTokens, count, count)


law set_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  {allFrom(grammar, inputTokens, Table(grammar, inputTokens), Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}

def set_from(grammar, inputTokens):
  +count = List.length(&2, Nat, inputTokens)
  all_steps_from(grammar, inputTokens, Table(grammar, inputTokens), count, count)


law member_from_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +d2: Nat
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for -rest: +List<Types.Bsr>
  for cases: Either<{Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}, {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool}>
  for headFrom: {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool} -> {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p, d}, i, k, j}) == True{} : Bool}
  {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p, d}, i, k, j}) == True{} : Bool}

def member_from_pick(grammar, inputTokens, table, p, d, i, k, j, p2, d2, i2, k2, j2, rest, cases, headFrom, searchRest):
  match cases:
    case Inl{same}:
      +all = same
      +dikj = Lemma.and_true_right_side(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), all)
      +ikj = Lemma.and_true_right_side(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), dikj)
      +kj = Lemma.and_true_right_side(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), ikj)
      sameP = Lemma.nat_eq_sound(p, p2, Lemma.and_true_left(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), all))
      sameD = Lemma.nat_eq_sound(d, d2, Lemma.and_true_left(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), dikj))
      sameI = Lemma.nat_eq_sound(i, i2, Lemma.and_true_left(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), ikj))
      sameK = Lemma.nat_eq_sound(k, k2, Lemma.and_true_left(Nat.is_eq(k, k2), Nat.is_eq(j, j2), kj))
      sameJ = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Nat.is_eq(k, k2), Nat.is_eq(j, j2), kj))
      %Equal.sym(Nat, p, p2, sameP) : {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{_, d}, i, k, j}) == True{} : Bool}
      %Equal.sym(Nat, d, d2, sameD) : {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, _}, i, k, j}) == True{} : Bool}
      %Equal.sym(Nat, i, i2, sameI) : {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, _, k, j}) == True{} : Bool}
      %Equal.sym(Nat, k, k2, sameK) : {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, i2, _, j}) == True{} : Bool}
      %Equal.sym(Nat, j, j2, sameJ) : {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, i2, k2, _}) == True{} : Bool}
      headFrom
    case Inr{inRest}:
      searchRest(inRest)


# Anything in a set whose elements all satisfy the characterization satisfies it.
law member_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for element: Types.Bsr
  for set: +List<Types.Bsr>
  for m: {GrammarLaws.bsrMember(element, set) == True{} : Bool}
  for +ok: {allFrom(grammar, inputTokens, table, set) == True{} : Bool}
  {stepFrom(grammar, inputTokens, table, element) == True{} : Bool}

def member_from(grammar, inputTokens, table, element, set, m, ok):
  match element:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      match set:
        case Nil{}:
          Empty.absurd({stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p, d}, i, k, j}) == True{} : Bool}, Lemma.false_is_not_true(m))
        case Con{Types.Bsr{Types.Slot{+p2, +d2}, +i2, +k2, +j2}, +rest}:
          member_from_pick(
            grammar, inputTokens, table, p, d, i, k, j, p2, d2, i2, k2, j2, rest,
            Lemma.or_true_cases(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest), m),
            Lemma.and_true_left(stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}), allFrom(grammar, inputTokens, table, rest), ok),
            inRest => member_from(grammar, inputTokens, table, Types.Bsr{Types.Slot{p, d}, i, k, j}, rest, inRest, Lemma.and_true_right_side(stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}), allFrom(grammar, inputTokens, table, rest), ok)))


# Anything in the BSR set satisfies the characterization.
law in_set_from:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for element: Types.Bsr
  for m: {GrammarLaws.bsrMember(element, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  {stepFrom(grammar, inputTokens, Table(grammar, inputTokens), element) == True{} : Bool}

def in_set_from(grammar, inputTokens, element, m):
  member_from(grammar, inputTokens, Table(grammar, inputTokens), element, Grammar.cykSteps(grammar, inputTokens), m, set_from(grammar, inputTokens))


# ======== BSR SOUNDNESS ========

# ---- The steps one child contributes ----

# Where a child ends, when it starts at `at`.
def endOf(+child: Types.Tree, +at: Nat) -> Nat:
  Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves([child])))


# The steps a child brings for itself: none for a leaf; a node's own steps.
def ownOf(child: Types.Tree, +set: +List<Types.Bsr>, +at: Nat) -> Bool:
  match child:
    case Types.Leaf{kind}:
      True{}
    case Types.Node{+q, +children}:
      Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at))


def ChildParts(+child: Types.Tree, +rest: +List<Types.Tree>, +set: +List<Types.Bsr>, +index: Nat, +dot: Nat, +i: Nat, +at: Nat) -> Type:
  {slotStep(set, index, dot, i, at, endOf(child, at), List.is_empty(&2, Types.Tree, rest)) == True{} : Bool} & {ownOf(child, set, at) == True{} : Bool} & {embeddedChildren(rest, set, index, 1n+dot, i, endOf(child, at)) == True{} : Bool}


law length_node_leaves:
  for -q: Nat
  for +children: +List<Types.Tree>
  {List.length(&2, Nat, GrammarLaws.leaves(children)) == List.length(&2, Nat, GrammarLaws.leaves([Types.Node{q, children}])) : Nat}

def length_node_leaves(q, children):
  Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves(children), List.append(&2, Nat, GrammarLaws.leaves(children), []), Equal.sym(+List<Nat>, List.append(&2, Nat, GrammarLaws.leaves(children), []), GrammarLaws.leaves(children), Lemma.append_nil_right(GrammarLaws.leaves(children))))


law child_parts:
  for child: Types.Tree
  for +rest: +List<Types.Tree>
  for +set: +List<Types.Bsr>
  for +index: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  for e: {embeddedChildren(child <> rest, set, index, dot, i, at) == True{} : Bool}
  ChildParts(child, rest, set, index, dot, i, at)

def child_parts(child, rest, set, index, dot, i, at, e):
  match child:
    case Types.Leaf{+kind}:
      +both = e
      +later = Lemma.and_true_right_side(slotStep(set, index, dot, i, at, 1n+at, List.is_empty(&2, Types.Tree, rest)), embeddedChildren(rest, set, index, 1n+dot, i, 1n+at), both)
      %Equal.sym(Nat, Nat.add(at, 1n), 1n+at, Lemma.add_one_right(at)) : {slotStep(set, index, dot, i, at, _, List.is_empty(&2, Types.Tree, rest)) == True{} : Bool} & {True{} == True{} : Bool} & {embeddedChildren(rest, set, index, 1n+dot, i, _) == True{} : Bool}
      (Lemma.and_true_left(slotStep(set, index, dot, i, at, 1n+at, List.is_empty(&2, Types.Tree, rest)), embeddedChildren(rest, set, index, 1n+dot, i, 1n+at), both), ({==}, later))
    case Types.Node{+q, +children}:
      +both = e
      +own = Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at))
      +end = Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(children)))
      +slot = slotStep(set, index, dot, i, at, end, List.is_empty(&2, Types.Tree, rest))
      +later = embeddedChildren(rest, set, index, 1n+dot, i, end)
      +ownAndLater = Lemma.and_true_right_side(slot, Bool.and(own, later), both)
      %Equal.cong(Nat, Nat, n => Nat.add(at, n), List.length(&2, Nat, GrammarLaws.leaves(children)), List.length(&2, Nat, GrammarLaws.leaves([Types.Node{q, children}])), length_node_leaves(q, children)) : {slotStep(set, index, dot, i, at, _, List.is_empty(&2, Types.Tree, rest)) == True{} : Bool} & {own == True{} : Bool} & {embeddedChildren(rest, set, index, 1n+dot, i, _) == True{} : Bool}
      (Lemma.and_true_left(slot, Bool.and(own, later), both), (Lemma.and_true_left(own, later, ownAndLater), Lemma.and_true_right_side(own, later, ownAndLater)))


# What a step with one recognized symbol says: it covers one token, and the
# production's terminal is that token.
law one_symbol_facts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +p: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for e: {stepFrom(grammar, inputTokens, table, Types.Bsr{Types.Slot{p, 1n}, i, k, j}) == True{} : Bool}
  {Nat.is_eq(j, 1n+i) == True{} : Bool} & {tokenMatches(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i)) == True{} : Bool}

def one_symbol_facts(grammar, inputTokens, table, p, i, k, j, e):
  +tm = tokenMatches(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
  +x = Lemma.or_false_right(Bool.and(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm)), e)
  +y = Lemma.and_true_right_side(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm), x)
  (Lemma.and_true_left(Nat.is_eq(j, 1n+i), tm, y), Lemma.and_true_right_side(Nat.is_eq(j, 1n+i), tm, y))


def PairShape(+rhs: +List<Types.Symbol>) -> Type:
  &b: Nat -> &c: Nat -> {rhs == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}


# What a step with two recognized symbols says about its production: it is a = b c.
law pair_shape:
  for rhs: +List<Types.Symbol>
  for -table: +List<Grammar.Cell>
  for -i: Nat
  for -k: Nat
  for -j: Nat
  for e: {pairInCells(rhs, table, i, k, j) == True{} : Bool}
  PairShape(rhs)

def pair_shape(rhs, table, i, k, j, e):
  match rhs:
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Nil{}}}:
      (b, (c, {==}))
    case Nil{}:
      Empty.absurd(PairShape([]), Lemma.false_is_not_true(e))
    case Con{Types.Terminal{t}, more}:
      Empty.absurd(PairShape(Types.Terminal{t} <> more), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Nil{}}:
      Empty.absurd(PairShape([Types.Nonterminal{b}]), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{t}, more}}:
      Empty.absurd(PairShape(Types.Nonterminal{b} <> Types.Terminal{t} <> more), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      Empty.absurd(PairShape(Types.Nonterminal{b} <> Types.Nonterminal{c} <> x <> more), Lemma.false_is_not_true(e))


# ---- A fitting tree embedded in the set spells the input ----

def Spells(+tree: Types.Tree, +inputTokens: +List<Nat>, +i: Nat) -> Type:
  {GrammarLaws.leaves([tree]) == Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([tree]))) : +List<Nat>}


def StepSet(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>) -> +List<Types.Bsr>:
  Grammar.cykSteps(grammar, inputTokens)


# A child that fits a nonterminal and brings its own steps is an embedded node.
law own_is_embedded:
  for child: Types.Tree
  for -grammar: +List<Types.Production>
  for -b: Nat
  for -set: +List<Types.Bsr>
  for -at: Nat
  for fitting: {GrammarLaws.fits([child], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for own: {ownOf(child, set, at) == True{} : Bool}
  {embedded(child, set, at) == True{} : Bool}

def own_is_embedded(child, grammar, b, set, at, fitting, own):
  match child:
    case Types.Leaf{kind}:
      Empty.absurd({embedded(Types.Leaf{kind}, set, at) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Types.Node{q, children}:
      own


law no_children_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +i: Nat
  for inSet: {embedded(Types.Node{p, []}, StepSet(grammar, inputTokens), i) == True{} : Bool}
  Empty

def no_children_sound(grammar, inputTokens, p, i, inSet):
  +m = GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 0n}, i, i, i}, StepSet(grammar, inputTokens))
  Lemma.false_is_not_true(in_set_from(grammar, inputTokens, Types.Bsr{Types.Slot{p, 0n}, i, i, i}, Lemma.and_true_left(m, True{}, inSet)))


law leaf_token_spells:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +kind: Nat
  for fitting: {GrammarLaws.fits([Types.Node{p, [Types.Leaf{kind}]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for parts: TokenParts(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
  Spells(Types.Node{p, [Types.Leaf{kind}]}, inputTokens, i)

def leaf_token_spells(grammar, inputTokens, i, p, a, kind, fitting, parts):
  match parts:
    case (+k, (rhsEq, +tokenEq)):
      childFits = fits_at([Types.Leaf{kind}], grammar, Types.rhsOf(grammar, p), [Types.Terminal{k}], rhsEq, node_children(grammar, p, a, [Types.Leaf{kind}], fitting))
      kindIsK = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), True{}, childFits))
      Equal.trans(+List<Nat>, [kind], [k], Lemma.slice(inputTokens, i, 1n), Equal.cong(Nat, +List<Nat>, n => [n], kind, k, kindIsK), Equal.sym(+List<Nat>, Lemma.slice(inputTokens, i, 1n), [k], Lemma.get_slice(inputTokens, i, k, tokenEq)))


law token_node_absurd:
  for +grammar: +List<Types.Production>
  for -inputTokens: +List<Nat>
  for -i: Nat
  for +p: Nat
  for +q: Nat
  for +grandchildren: +List<Types.Tree>
  for shapeFit: {GrammarLaws.fits([Types.Node{q, grandchildren}], grammar, Types.rhsOf(grammar, p)) == True{} : Bool}
  for parts: TokenParts(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
  Spells(Types.Node{p, [Types.Node{q, grandchildren}]}, inputTokens, i)

def token_node_absurd(grammar, inputTokens, i, p, q, grandchildren, shapeFit, parts):
  match parts:
    case (k, (rhsEq, tokenEq)):
      Empty.absurd(Spells(Types.Node{p, [Types.Node{q, grandchildren}]}, inputTokens, i), Lemma.false_is_not_true(fits_at([Types.Node{q, grandchildren}], grammar, Types.rhsOf(grammar, p), [Types.Terminal{k}], rhsEq, shapeFit)))


law one_child_token:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for child: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [child]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for facts: {Nat.is_eq(endOf(child, i), 1n+i) == True{} : Bool} & {tokenMatches(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i)) == True{} : Bool}
  Spells(Types.Node{p, [child]}, inputTokens, i)

def one_child_token(grammar, inputTokens, i, p, a, child, fitting, facts):
  match child:
    case Types.Node{+q, +grandchildren}:
      match facts:
        case (ends, matches):
          shapeFit = node_children(grammar, p, a, [Types.Node{q, grandchildren}], fitting)
          token_node_absurd(grammar, inputTokens, i, p, q, grandchildren, shapeFit, token_matches_parts(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i), matches))
    case Types.Leaf{+kind}:
      match facts:
        case (ends, matches):
          leaf_token_spells(grammar, inputTokens, i, p, a, kind, fitting, token_matches_parts(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i), matches))


law one_child_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +child: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [child]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for parts: ChildParts(child, [], StepSet(grammar, inputTokens), p, 0n, i, i)
  Spells(Types.Node{p, [child]}, inputTokens, i)

def one_child_parts(grammar, inputTokens, i, p, a, child, fitting, parts):
  match parts:
    case (slot, (own, later)):
      +step = {Types.Bsr{Types.Slot{p, 1n}, i, i, endOf(child, i)} : Types.Bsr}
      facts = one_symbol_facts(grammar, inputTokens, Table(grammar, inputTokens), p, i, i, endOf(child, i), in_set_from(grammar, inputTokens, step, slot))
      one_child_token(grammar, inputTokens, i, p, a, child, fitting, facts)


law one_child_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for symbol: Types.Symbol
  for +i: Nat
  for +p: Nat
  for +child: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [child]}], grammar, [symbol]) == True{} : Bool}
  for +inSet: {embedded(Types.Node{p, [child]}, StepSet(grammar, inputTokens), i) == True{} : Bool}
  Spells(Types.Node{p, [child]}, inputTokens, i)

def one_child_sound(grammar, inputTokens, symbol, i, p, child, fitting, inSet):
  match symbol:
    case Types.Terminal{k}:
      Empty.absurd(Spells(Types.Node{p, [child]}, inputTokens, i), Lemma.false_is_not_true(fitting))
    case Types.Nonterminal{+a}:
      +set = StepSet(grammar, inputTokens)
      parts = child_parts(child, [], set, p, 0n, i, i, inSet)
      one_child_parts(grammar, inputTokens, i, p, a, child, fitting, parts)


def ChildSpells(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +child: Types.Tree) -> Type:
  @s: Types.Symbol -> @at: Nat -> {GrammarLaws.fits([child], grammar, [s]) == True{} : Bool} -> {embedded(child, StepSet(grammar, inputTokens), at) == True{} : Bool} -> Spells(child, inputTokens, at)


# Two children that spell their parts of the input spell the whole node's part.
law join_spells:
  for -grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for spells1: Spells(first, inputTokens, i)
  for spells2: Spells(second, inputTokens, endOf(first, i))
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def join_spells(grammar, inputTokens, i, p, first, second, spells1, spells2):
  +l1 = List.length(&2, Nat, GrammarLaws.leaves([first]))
  +l2 = List.length(&2, Nat, GrammarLaws.leaves([second]))
  +k = Nat.add(i, l1)
  +w1 = GrammarLaws.leaves([first])
  +w2 = GrammarLaws.leaves([second])
  +node = GrammarLaws.leaves([Types.Node{p, [first, second]}])
  +joined = node_leaves(p, [first, second], List.append(&2, Nat, w1, w2), pair_leaves(first, second, w1, w2, {==}, {==}))
  lengthEq = Equal.trans(Nat, List.length(&2, Nat, node), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(l1, l2), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), node, List.append(&2, Nat, w1, w2), joined), Lemma.length_append(w1, w2))
  Equal.trans(
    +List<Nat>, node, List.append(&2, Nat, w1, w2), Lemma.slice(inputTokens, i, List.length(&2, Nat, node)),
    joined,
    Equal.trans(
      +List<Nat>, List.append(&2, Nat, w1, w2), List.append(&2, Nat, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2)), Lemma.slice(inputTokens, i, List.length(&2, Nat, node)),
      Lemma.append_congr(w1, w2, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2), spells1, spells2),
      Equal.trans(
        +List<Nat>, List.append(&2, Nat, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2)), Lemma.slice(inputTokens, i, Nat.add(l1, l2)), Lemma.slice(inputTokens, i, List.length(&2, Nat, node)),
        Lemma.slice_split(inputTokens, i, l1, l2),
        Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, i, n), Nat.add(l1, l2), List.length(&2, Nat, node), Equal.sym(Nat, List.length(&2, Nat, node), Nat.add(l1, l2), lengthEq)))))


law two_shape_spells:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [first, second]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for own1: {ownOf(first, StepSet(grammar, inputTokens), i) == True{} : Bool}
  for own2: {ownOf(second, StepSet(grammar, inputTokens), endOf(first, i)) == True{} : Bool}
  for shape: PairShape(Types.rhsOf(grammar, p))
  for spells1: ChildSpells(grammar, inputTokens, first)
  for spells2: ChildSpells(grammar, inputTokens, second)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def two_shape_spells(grammar, inputTokens, i, p, a, first, second, fitting, own1, own2, shape, spells1, spells2):
  match shape:
    case (+b, (+c, rhsEq)):
      +fitsBC = fits_at([first, second], grammar, Types.rhsOf(grammar, p), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsEq, node_children(grammar, p, a, [first, second], fitting))
      +f1 = fits_cons_left(first, [second], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fitsBC)
      +f2 = fits_cons_right(first, [second], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fitsBC)
      +set = StepSet(grammar, inputTokens)
      s1 = spells1(Types.Nonterminal{b}, i, f1, own_is_embedded(first, grammar, b, set, i, f1, own1))
      s2 = spells2(Types.Nonterminal{c}, endOf(first, i), f2, own_is_embedded(second, grammar, c, set, endOf(first, i), f2, own2))
      join_spells(grammar, inputTokens, i, p, first, second, s1, s2)


law two_second_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [first, second]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for own1: {ownOf(first, StepSet(grammar, inputTokens), i) == True{} : Bool}
  for parts: ChildParts(second, [], StepSet(grammar, inputTokens), p, 1n, i, endOf(first, i))
  for spells1: ChildSpells(grammar, inputTokens, first)
  for spells2: ChildSpells(grammar, inputTokens, second)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def two_second_parts(grammar, inputTokens, i, p, a, first, second, fitting, own1, parts, spells1, spells2):
  match parts:
    case (slot, (own2, later)):
      +k = endOf(first, i)
      +j = endOf(second, k)
      +step = {Types.Bsr{Types.Slot{p, 2n}, i, k, j} : Types.Bsr}
      pic = in_set_from(grammar, inputTokens, step, slot)
      two_shape_spells(grammar, inputTokens, i, p, a, first, second, fitting, own1, own2, pair_shape(Types.rhsOf(grammar, p), Table(grammar, inputTokens), i, k, j, pic), spells1, spells2)


law two_first_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [first, second]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for parts: ChildParts(first, [second], StepSet(grammar, inputTokens), p, 0n, i, i)
  for spells1: ChildSpells(grammar, inputTokens, first)
  for spells2: ChildSpells(grammar, inputTokens, second)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def two_first_parts(grammar, inputTokens, i, p, a, first, second, fitting, parts, spells1, spells2):
  match parts:
    case (slot, (own1, later)):
      two_second_parts(grammar, inputTokens, i, p, a, first, second, fitting, own1, child_parts(second, [], StepSet(grammar, inputTokens), p, 1n, i, endOf(first, i), later), spells1, spells2)


law two_children_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for symbol: Types.Symbol
  for +i: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [first, second]}], grammar, [symbol]) == True{} : Bool}
  for inSet: {embedded(Types.Node{p, [first, second]}, StepSet(grammar, inputTokens), i) == True{} : Bool}
  for spells1: ChildSpells(grammar, inputTokens, first)
  for spells2: ChildSpells(grammar, inputTokens, second)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def two_children_sound(grammar, inputTokens, symbol, i, p, first, second, fitting, inSet, spells1, spells2):
  match symbol:
    case Types.Terminal{k}:
      Empty.absurd(Spells(Types.Node{p, [first, second]}, inputTokens, i), Lemma.false_is_not_true(fitting))
    case Types.Nonterminal{+a}:
      two_first_parts(grammar, inputTokens, i, p, a, first, second, fitting, child_parts(first, [second], StepSet(grammar, inputTokens), p, 0n, i, i, inSet), spells1, spells2)


# Three or more children would need a step for a slot with three symbols, and the
# set has none.
law third_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +third: Types.Tree
  for -more: +List<Types.Tree>
  for +at: Nat
  for parts: ChildParts(third, more, StepSet(grammar, inputTokens), p, 2n, i, at)
  Empty

def third_parts(grammar, inputTokens, i, p, third, more, at, parts):
  match parts:
    case (slot, (own, later)):
      Lemma.false_is_not_true(in_set_from(grammar, inputTokens, {Types.Bsr{Types.Slot{p, 3n}, i, at, endOf(third, at)} : Types.Bsr}, slot))


law second_of_long:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +second: Types.Tree
  for +third: Types.Tree
  for +more: +List<Types.Tree>
  for +at: Nat
  for parts: ChildParts(second, third <> more, StepSet(grammar, inputTokens), p, 1n, i, at)
  Empty

def second_of_long(grammar, inputTokens, i, p, second, third, more, at, parts):
  match parts:
    case (slot, (own, later)):
      third_parts(grammar, inputTokens, i, p, third, more, endOf(second, at), child_parts(third, more, StepSet(grammar, inputTokens), p, 2n, i, endOf(second, at), later))


law first_of_long:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for +third: Types.Tree
  for +more: +List<Types.Tree>
  for parts: ChildParts(first, second <> third <> more, StepSet(grammar, inputTokens), p, 0n, i, i)
  Empty

def first_of_long(grammar, inputTokens, i, p, first, second, third, more, parts):
  match parts:
    case (slot, (own, later)):
      second_of_long(grammar, inputTokens, i, p, second, third, more, endOf(first, i), child_parts(second, third <> more, StepSet(grammar, inputTokens), p, 1n, i, endOf(first, i), later))


law tree_spells:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for symbol: Types.Symbol
  for +i: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [symbol]) == True{} : Bool}
  for inSet: {embedded(t, StepSet(grammar, inputTokens), i) == True{} : Bool}
  Spells(t, inputTokens, i)

def tree_spells(t, grammar, inputTokens, symbol, i, fitting, inSet):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd(Spells(Types.Leaf{kind}, inputTokens, i), Lemma.false_is_not_true(inSet))
    case Types.Node{+p, children}:
      match children:
        case Nil{}:
          Empty.absurd(Spells(Types.Node{p, []}, inputTokens, i), no_children_sound(grammar, inputTokens, p, i, inSet))
        case Con{+first, Nil{}}:
          one_child_sound(grammar, inputTokens, symbol, i, p, first, fitting, inSet)
        case Con{+first, Con{+second, Nil{}}}:
          two_children_sound(
            grammar, inputTokens, symbol, i, p, first, second, fitting, inSet,
            s1 => i1 => f1 => e1 => tree_spells(first, grammar, inputTokens, s1, i1, f1, e1),
            s2 => i2 => f2 => e2 => tree_spells(second, grammar, inputTokens, s2, i2, f2, e2))
        case Con{+first, Con{+second, Con{+third, +more}}}:
          Empty.absurd(Spells(Types.Node{p, first <> second <> third <> more}, inputTokens, i), first_of_long(grammar, inputTokens, i, p, first, second, third, more, child_parts(first, second <> third <> more, StepSet(grammar, inputTokens), p, 0n, i, i, inSet)))


# ======== STEPS AND EMBEDDED TREES ========
#
# The specification lists a tree's steps (`steps`); the CYK proofs check them against
# a set (`embedded`). The two agree: a tree is embedded exactly when all its steps
# are in the set (embedded_all_in).

# Is every element of xs in the set?
def allIn(xs: +List<Types.Bsr>, +set: +List<Types.Bsr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(GrammarLaws.bsrMember(x, set), allIn(rest, set))

law and_true_r:
  for x: Bool
  {Bool.and(x, True{}) == x : Bool}

def and_true_r(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law and_assoc:
  for x: Bool
  for -y: Bool
  for -z: Bool
  {Bool.and(x, Bool.and(y, z)) == Bool.and(Bool.and(x, y), z) : Bool}

def and_assoc(x, y, z):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

law and_congr:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for ac: {a == c : Bool}
  for bd: {b == d : Bool}
  {Bool.and(a, b) == Bool.and(c, d) : Bool}

def and_congr(a, b, c, d, ac, bd):
  %ac : {Bool.and(a, b) == Bool.and(_, d) : Bool}
  %bd : {Bool.and(a, b) == Bool.and(a, _) : Bool}
  {==}

law all_in_append:
  for xs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for +set: +List<Types.Bsr>
  {allIn(List.append(&2, Types.Bsr, xs, ys), set) == Bool.and(allIn(xs, set), allIn(ys, set)) : Bool}

def all_in_append(xs, ys, set):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +m = GrammarLaws.bsrMember(x, set)
      Equal.trans(Bool,
        Bool.and(m, allIn(List.append(&2, Types.Bsr, rest, ys), set)),
        Bool.and(m, Bool.and(allIn(rest, set), allIn(ys, set))),
        Bool.and(Bool.and(m, allIn(rest, set)), allIn(ys, set)),
        Equal.cong(Bool, Bool, v => Bool.and(m, v), allIn(List.append(&2, Types.Bsr, rest, ys), set), Bool.and(allIn(rest, set), allIn(ys, set)), all_in_append(rest, ys, set)),
        and_assoc(m, allIn(rest, set), allIn(ys, set)))

# The slot check agrees with the slot's list of steps, for each value of the two flags.
law slot_flags:
  for x: Bool
  for last: Bool
  for +element: Types.Bsr
  for +set: +List<Types.Bsr>
  {Bool.or(Bool.and(x, Bool.not(last)), GrammarLaws.bsrMember(element, set)) == allIn(GrammarLaws.keepStep(Bool.or(Bool.not(x), last), element), set) : Bool}

def slot_flags(x, last, element, set):
  match x last:
    case True{} True{}:
      Equal.sym(Bool, Bool.and(GrammarLaws.bsrMember(element, set), True{}), GrammarLaws.bsrMember(element, set), and_true_r(GrammarLaws.bsrMember(element, set)))
    case True{} False{}:
      {==}
    case False{} True{}:
      Equal.sym(Bool, Bool.and(GrammarLaws.bsrMember(element, set), True{}), GrammarLaws.bsrMember(element, set), and_true_r(GrammarLaws.bsrMember(element, set)))
    case False{} False{}:
      Equal.sym(Bool, Bool.and(GrammarLaws.bsrMember(element, set), True{}), GrammarLaws.bsrMember(element, set), and_true_r(GrammarLaws.bsrMember(element, set)))

law slot_all_in:
  for +set: +List<Types.Bsr>
  for +index: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  for +end: Nat
  for +last: Bool
  {slotStep(set, index, dot, i, at, end, last) == allIn(GrammarLaws.slotSteps(index, dot, i, at, end, last), set) : Bool}

def slot_all_in(set, index, dot, i, at, end, last):
  slot_flags(Nat.is_eq(dot, 0n), last, Types.Bsr{Types.Slot{index, 1n+dot}, i, at, end}, set)

law empty_all_in:
  for +set: +List<Types.Bsr>
  for +index: Nat
  for +at: Nat
  for children: +List<Types.Tree>
  {emptyStep(set, index, at, children) == allIn(GrammarLaws.emptySteps(index, at, children), set) : Bool}

def empty_all_in(set, index, at, children):
  match children:
    case Nil{}:
      Equal.sym(Bool, Bool.and(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 0n}, at, at, at}, set), True{}), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 0n}, at, at, at}, set), and_true_r(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 0n}, at, at, at}, set)))
    case Con{c, cs}:
      {==}

law children_all_in:
  for forest: +List<Types.Tree>
  for +set: +List<Types.Bsr>
  for +index: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  {embeddedChildren(forest, set, index, dot, i, at) == allIn(GrammarLaws.childSteps(forest, index, dot, i, at), set) : Bool}

def children_all_in(forest, set, index, dot, i, at):
  match forest:
    case Nil{}:
      {==}
    case Con{Types.Leaf{+kind}, +rest}:
      +last = List.is_empty(&2, Types.Tree, rest)
      +slot = GrammarLaws.slotSteps(index, dot, i, at, 1n+at, last)
      +later = GrammarLaws.childSteps(rest, index, 1n+dot, i, 1n+at)
      Equal.trans(Bool,
        Bool.and(slotStep(set, index, dot, i, at, 1n+at, last), embeddedChildren(rest, set, index, 1n+dot, i, 1n+at)),
        Bool.and(allIn(slot, set), allIn(later, set)),
        allIn(List.append(&2, Types.Bsr, slot, later), set),
        and_congr(slotStep(set, index, dot, i, at, 1n+at, last), embeddedChildren(rest, set, index, 1n+dot, i, 1n+at), allIn(slot, set), allIn(later, set),
          slot_all_in(set, index, dot, i, at, 1n+at, last),
          children_all_in(rest, set, index, 1n+dot, i, 1n+at)),
        Equal.sym(Bool, allIn(List.append(&2, Types.Bsr, slot, later), set), Bool.and(allIn(slot, set), allIn(later, set)), all_in_append(slot, later, set)))
    case Con{Types.Node{+q, +children}, +rest}:
      +end = Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(children)))
      +last = List.is_empty(&2, Types.Tree, rest)
      +slot = GrammarLaws.slotSteps(index, dot, i, at, end, last)
      +own = GrammarLaws.emptySteps(q, at, children)
      +inner = GrammarLaws.childSteps(children, q, 0n, at, at)
      +later = GrammarLaws.childSteps(rest, index, 1n+dot, i, end)
      +ownInner = List.append(&2, Types.Bsr, own, inner)
      +node = List.append(&2, Types.Bsr, ownInner, later)
      nodeEq = Equal.trans(Bool,
        Bool.and(Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at)), embeddedChildren(rest, set, index, 1n+dot, i, end)),
        Bool.and(Bool.and(allIn(own, set), allIn(inner, set)), allIn(later, set)),
        allIn(node, set),
        and_congr(Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at)), embeddedChildren(rest, set, index, 1n+dot, i, end), Bool.and(allIn(own, set), allIn(inner, set)), allIn(later, set),
          and_congr(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at), allIn(own, set), allIn(inner, set),
            empty_all_in(set, q, at, children),
            children_all_in(children, set, q, 0n, at, at)),
          children_all_in(rest, set, index, 1n+dot, i, end)),
        Equal.sym(Bool, allIn(node, set), Bool.and(Bool.and(allIn(own, set), allIn(inner, set)), allIn(later, set)),
          Equal.trans(Bool, allIn(node, set), Bool.and(allIn(ownInner, set), allIn(later, set)), Bool.and(Bool.and(allIn(own, set), allIn(inner, set)), allIn(later, set)),
            all_in_append(ownInner, later, set),
            Equal.cong(Bool, Bool, v => Bool.and(v, allIn(later, set)), allIn(ownInner, set), Bool.and(allIn(own, set), allIn(inner, set)), all_in_append(own, inner, set)))))
      Equal.trans(Bool,
        Bool.and(slotStep(set, index, dot, i, at, end, last), Bool.and(Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at)), embeddedChildren(rest, set, index, 1n+dot, i, end))),
        Bool.and(allIn(slot, set), allIn(node, set)),
        allIn(List.append(&2, Types.Bsr, slot, node), set),
        and_congr(slotStep(set, index, dot, i, at, end, last), Bool.and(Bool.and(emptyStep(set, q, at, children), embeddedChildren(children, set, q, 0n, at, at)), embeddedChildren(rest, set, index, 1n+dot, i, end)), allIn(slot, set), allIn(node, set),
          slot_all_in(set, index, dot, i, at, end, last),
          nodeEq),
        Equal.sym(Bool, allIn(List.append(&2, Types.Bsr, slot, node), set), Bool.and(allIn(slot, set), allIn(node, set)), all_in_append(slot, node, set)))

# A node is embedded in a set exactly when all its steps are in the set.
law node_embedded_all_in:
  for +index: Nat
  for +children: +List<Types.Tree>
  for +set: +List<Types.Bsr>
  for +i: Nat
  {embedded(Types.Node{index, children}, set, i) == allIn(GrammarLaws.steps(Types.Node{index, children}, i), set) : Bool}

def node_embedded_all_in(index, children, set, i):
  +own = GrammarLaws.emptySteps(index, i, children)
  +inner = GrammarLaws.childSteps(children, index, 0n, i, i)
  Equal.trans(Bool,
    Bool.and(emptyStep(set, index, i, children), embeddedChildren(children, set, index, 0n, i, i)),
    Bool.and(allIn(own, set), allIn(inner, set)),
    allIn(List.append(&2, Types.Bsr, own, inner), set),
    and_congr(emptyStep(set, index, i, children), embeddedChildren(children, set, index, 0n, i, i), allIn(own, set), allIn(inner, set),
      empty_all_in(set, index, i, children),
      children_all_in(children, set, index, 0n, i, i)),
    Equal.sym(Bool, allIn(List.append(&2, Types.Bsr, own, inner), set), Bool.and(allIn(own, set), allIn(inner, set)), all_in_append(own, inner, set)))

# All steps of an embedded tree are in the set.
law embedded_all_in:
  for tree: Types.Tree
  for +set: +List<Types.Bsr>
  for +i: Nat
  for emb: {embedded(tree, set, i) == True{} : Bool}
  {allIn(GrammarLaws.steps(tree, i), set) == True{} : Bool}

def embedded_all_in(tree, set, i, emb):
  match tree:
    case Types.Leaf{kind}:
      {==}
    case Types.Node{+index, +children}:
      Equal.trans(Bool, allIn(GrammarLaws.steps(Types.Node{index, children}, i), set), embedded(Types.Node{index, children}, set, i), True{},
        Equal.sym(Bool, embedded(Types.Node{index, children}, set, i), allIn(GrammarLaws.steps(Types.Node{index, children}, i), set), node_embedded_all_in(index, children, set, i)),
        emb)

# A node whose steps are all in the set is embedded in it.
law all_in_embedded:
  for +index: Nat
  for +children: +List<Types.Tree>
  for +set: +List<Types.Bsr>
  for +i: Nat
  for all: {allIn(GrammarLaws.steps(Types.Node{index, children}, i), set) == True{} : Bool}
  {embedded(Types.Node{index, children}, set, i) == True{} : Bool}

def all_in_embedded(index, children, set, i, all):
  Equal.trans(Bool, embedded(Types.Node{index, children}, set, i), allIn(GrammarLaws.steps(Types.Node{index, children}, i), set), True{}, node_embedded_all_in(index, children, set, i), all)

# Two elements whose fields are equal are equal.
law bsr_eq_sound:
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +d2: Nat
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for same: {Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}
  {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2} : Types.Bsr}

def bsr_eq_sound(p, d, i, k, j, p2, d2, i2, k2, j2, same):
  +s0 = same
  +r1 = Lemma.and_true_right_side(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), s0)
  +r2 = Lemma.and_true_right_side(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), r1)
  +r3 = Lemma.and_true_right_side(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), r2)
  +r4 = Lemma.and_true_right_side(Nat.is_eq(k, k2), Nat.is_eq(j, j2), r3)
  ep = Lemma.nat_eq_sound(p, p2, Lemma.and_true_left(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), s0))
  ed = Lemma.nat_eq_sound(d, d2, Lemma.and_true_left(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), r1))
  ei = Lemma.nat_eq_sound(i, i2, Lemma.and_true_left(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), r2))
  ek = Lemma.nat_eq_sound(k, k2, Lemma.and_true_left(Nat.is_eq(k, k2), Nat.is_eq(j, j2), r3))
  ej = Lemma.nat_eq_sound(j, j2, r4)
  %ep : {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{_, d2}, i2, k2, j2} : Types.Bsr}
  %ed : {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p, _}, i2, k2, j2} : Types.Bsr}
  %ei : {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p, d}, _, k2, j2} : Types.Bsr}
  %ek : {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p, d}, i, _, j2} : Types.Bsr}
  %ej : {Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p, d}, i, k, _} : Types.Bsr}
  {==}

law all_in_pick:
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +d2: Nat
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for -rest: +List<Types.Bsr>
  for +set: +List<Types.Bsr>
  for cases: Either<{Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}, {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool}>
  for inX: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}, set) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool} -> {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, set) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, set) == True{} : Bool}

# An element of xs is in every set that holds all of xs.
law all_in_member:
  for xs: +List<Types.Bsr>
  for +set: +List<Types.Bsr>
  for element: Types.Bsr
  for all: {allIn(xs, set) == True{} : Bool}
  for m: {GrammarLaws.bsrMember(element, xs) == True{} : Bool}
  {GrammarLaws.bsrMember(element, set) == True{} : Bool}

def all_in_pick(p, d, i, k, j, p2, d2, i2, k2, j2, rest, set, cases, inX, searchRest):
  match cases:
    case Inl{same}:
      %Equal.sym(Types.Bsr, Types.Bsr{Types.Slot{p, d}, i, k, j}, Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2}, bsr_eq_sound(p, d, i, k, j, p2, d2, i2, k2, j2, same)) : {GrammarLaws.bsrMember(_, set) == True{} : Bool}
      inX
    case Inr{later}:
      searchRest(later)

def all_in_member(xs, set, element, all, m):
  match xs element:
    case Nil{} Types.Bsr{Types.Slot{p, d}, i, k, j}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, set) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{Types.Bsr{Types.Slot{+p2, +d2}, +i2, +k2, +j2}, +rest} Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      +x = {Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2} : Types.Bsr}
      +e = {Types.Bsr{Types.Slot{p, d}, i, k, j} : Types.Bsr}
      +here = {Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) : Bool}
      +both = all
      all_in_pick(p, d, i, k, j, p2, d2, i2, k2, j2, rest, set,
        Lemma.or_true_cases(here, GrammarLaws.bsrMember(e, rest), m),
        Lemma.and_true_left(GrammarLaws.bsrMember(x, set), allIn(rest, set), both),
        later => all_in_member(rest, set, e, Lemma.and_true_right_side(GrammarLaws.bsrMember(x, set), allIn(rest, set), both), later))


# ======== BSR COMPLETENESS ========

def InSet(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +tree: Types.Tree, +s: Nat) -> Type:
  {embedded(tree, Grammar.cykSteps(grammar, inputTokens), s) == True{} : Bool}


law token_member:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +p: Nat
  for +kind: Nat
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for rhsOk: {Types.rhsOf(grammar, p) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s}, Grammar.tokenSteps(grammar, List.get(&2, Nat, inputTokens, s), s)) == True{} : Bool}

def token_member(grammar, inputTokens, s, p, kind, tokenEq, rhsOk):
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, inputTokens, s), Some{kind}, tokenEq) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s}, Grammar.tokenSteps(grammar, _, s)) == True{} : Bool}
  terminal_steps_member(grammar, kind, s, 0n, p, rhsOk)


# A node with one leaf child: its leaf step is in the set.
law leaf_complete:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +p: Nat
  for +child: Types.Tree
  for facts: OneChild(grammar, p, a, child)
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{p, [child]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [child]}])) == l : Nat}
  InSet(grammar, inputTokens, Types.Node{p, [child]}, s)

def leaf_complete(grammar, inputTokens, a, s, l, p, child, facts, at, len):
  match facts:
    case (+kind, (+isLeaf, (lhsOk, rhsOk))):
      +count = List.length(&2, Nat, inputTokens)
      +table = Grammar.buildTable(grammar, inputTokens, count, count)
      leafLeaves = Equal.cong(Types.Tree, +List<Nat>, t => GrammarLaws.leaves([Types.Node{p, [t]}]), child, Types.Leaf{kind}, isLeaf)
      lIsOne = Equal.trans(Nat, l, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [child]}])), 1n, Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [child]}])), l, len), Equal.cong(Types.Tree, Nat, t => List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [t]}])), child, Types.Leaf{kind}, isLeaf))
      +at1 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, 1n), Lemma.slice(inputTokens, s, l), [kind], Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), 1n, l, Equal.sym(Nat, l, 1n, lIsOne)), Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, l), GrammarLaws.leaves([Types.Node{p, [child]}]), [kind], at, leafLeaves))
      +lt = Lemma.slice_start_lt(inputTokens, s, 1n, kind, [], at1)
      inSpan = token_member(grammar, inputTokens, s, p, kind, Lemma.slice_get(inputTokens, s, kind, at1), rhsOk)
      %Equal.sym(Types.Tree, child, Types.Leaf{kind}, isLeaf) : InSet(grammar, inputTokens, Types.Node{p, [_]}, s)
      Lemma.and_true_intro(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s}, Grammar.cykSteps(grammar, inputTokens)), True{}, all_member(grammar, inputTokens, table, count, 0n, Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s}, count, Lemma.lt_pos(s, count, lt), row_member(grammar, inputTokens, table, 1n, s, Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s}, count, lt, inSpan)), {==})


# The induction hypothesis for a child tree, passed as a function.
def ChildInSet(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +child: Types.Tree) -> Type:
  @b: Nat -> @s: Nat -> @l: Nat -> {GrammarLaws.fits([child], grammar, [Types.Nonterminal{b}]) == True{} : Bool} -> {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([child]) : +List<Nat>} -> {List.length(&2, Nat, GrammarLaws.leaves([child])) == l : Nat} -> {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool} -> InSet(grammar, inputTokens, child, s)


# A two-child node whose children are embedded and whose own step is in the set is embedded.
law embed_two:
  for first: Types.Tree
  for second: Types.Tree
  for -grammar: +List<Types.Production>
  for -b: Nat
  for -c: Nat
  for +set: +List<Types.Bsr>
  for +p: Nat
  for +s: Nat
  for f1: {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for f2: {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  for m: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, endOf(first, s), endOf(second, endOf(first, s))}, set) == True{} : Bool}
  for e1: {embedded(first, set, s) == True{} : Bool}
  for e2: {embedded(second, set, endOf(first, s)) == True{} : Bool}
  {embedded(Types.Node{p, [first, second]}, set, s) == True{} : Bool}

def embed_two(first, second, grammar, b, c, set, p, s, f1, f2, m, e1, e2):
  match first second:
    case Types.Leaf{k} _:
      Empty.absurd({embedded(Types.Node{p, [Types.Leaf{k}, second]}, set, s) == True{} : Bool}, Lemma.false_is_not_true(f1))
    case Types.Node{q, cs} Types.Leaf{k}:
      Empty.absurd({embedded(Types.Node{p, [Types.Node{q, cs}, Types.Leaf{k}]}, set, s) == True{} : Bool}, Lemma.false_is_not_true(f2))
    case Types.Node{+q1, +c1} Types.Node{+q2, +c2}:
      +n1 = List.length(&2, Nat, GrammarLaws.leaves([Types.Node{q1, c1}]))
      +n2 = List.length(&2, Nat, GrammarLaws.leaves([Types.Node{q2, c2}]))
      %Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves(c1)), n1, length_node_leaves(q1, c1)) : {Bool.and(Bool.and(emptyStep(set, q1, s, c1), embeddedChildren(c1, set, q1, 0n, s, s)), Bool.and(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, _), Nat.add(Nat.add(s, _), List.length(&2, Nat, GrammarLaws.leaves(c2)))}, set), Bool.and(Bool.and(emptyStep(set, q2, Nat.add(s, _), c2), embeddedChildren(c2, set, q2, 0n, Nat.add(s, _), Nat.add(s, _))), True{}))) == True{} : Bool}
      +k = Nat.add(s, n1)
      %Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves(c2)), n2, length_node_leaves(q2, c2)) : {Bool.and(Bool.and(emptyStep(set, q1, s, c1), embeddedChildren(c1, set, q1, 0n, s, s)), Bool.and(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, k, Nat.add(k, _)}, set), Bool.and(Bool.and(emptyStep(set, q2, k, c2), embeddedChildren(c2, set, q2, 0n, k, k)), True{}))) == True{} : Bool}
      +emb1 = Bool.and(emptyStep(set, q1, s, c1), embeddedChildren(c1, set, q1, 0n, s, s))
      +emb2 = Bool.and(emptyStep(set, q2, k, c2), embeddedChildren(c2, set, q2, 0n, k, k))
      +step = GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, k, Nat.add(k, n2)}, set)
      Lemma.and_true_intro(emb1, Bool.and(step, Bool.and(emb2, True{})), e1, Lemma.and_true_intro(step, Bool.and(emb2, True{}), m, Lemma.and_true_intro(emb2, True{}, e2, {==})))


law move_pair_member:
  for +set: +List<Types.Bsr>
  for +p: Nat
  for +s: Nat
  for -l1: Nat
  for +m1: Nat
  for -l2: Nat
  for +m2: Nat
  for e1: {l1 == m1 : Nat}
  for e2: {l2 == m2 : Nat}
  for m: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, m1), Nat.add(s, Nat.add(m1, m2))}, set) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, l1), Nat.add(Nat.add(s, l1), l2)}, set) == True{} : Bool}

def move_pair_member(set, p, s, l1, m1, l2, m2, e1, e2, m):
  %Equal.sym(Nat, l1, m1, e1) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, _), Nat.add(Nat.add(s, _), l2)}, set) == True{} : Bool}
  %Equal.sym(Nat, l2, m2, e2) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, m1), Nat.add(Nat.add(s, m1), _)}, set) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(s, m1), m2), Nat.add(s, Nat.add(m1, m2)), Lemma.add_assoc(s, m1, m2)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, m1), _}, set) == True{} : Bool}
  m


law move_embedded:
  for -set: +List<Types.Bsr>
  for -tree: Types.Tree
  for -s: Nat
  for -l: Nat
  for -m: Nat
  for e: {l == m : Nat}
  for emb: {embedded(tree, set, Nat.add(s, m)) == True{} : Bool}
  {embedded(tree, set, Nat.add(s, l)) == True{} : Bool}

def move_embedded(set, tree, s, l, m, e, emb):
  %Equal.sym(Nat, l, m, e) : {embedded(tree, set, Nat.add(s, _)) == True{} : Bool}
  emb


law pair_complete_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for +b: Nat
  for +c: Nat
  for lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +f1: {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for +f2: {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  for w1: +List<Nat>
  for w2: +List<Nat>
  for +e1: {GrammarLaws.leaves([first]) == w1 : +List<Nat>}
  for +e2: {GrammarLaws.leaves([second]) == w2 : +List<Nat>}
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{p, [first, second]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])) == l : Nat}
  for +le: {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for firstInSet: ChildInSet(grammar, inputTokens, first)
  for secondInSet: ChildInSet(grammar, inputTokens, second)
  InSet(grammar, inputTokens, Types.Node{p, [first, second]}, s)

def pair_complete_parts(grammar, inputTokens, binary, a, s, l, p, first, second, b, c, lhsOk, rhsOk, f1, f2, w1, w2, e1, e2, at, len, le, firstInSet, secondInSet):
  match w1 w2:
    case Nil{} _:
      Empty.absurd(InSet(grammar, inputTokens, Types.Node{p, [first, second]}, s), Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, Nat, GrammarLaws.leaves([first])), False{}, Equal.sym(Bool, List.is_empty(&2, Nat, GrammarLaws.leaves([first])), True{}, Equal.cong(+List<Nat>, Bool, x => List.is_empty(&2, Nat, x), GrammarLaws.leaves([first]), [], e1)), tree_nonempty(first, grammar, binary, b, f1))))
    case Con{h1, r1} Nil{}:
      Empty.absurd(InSet(grammar, inputTokens, Types.Node{p, [first, second]}, s), Lemma.true_is_not_false(Equal.trans(Bool, True{}, List.is_empty(&2, Nat, GrammarLaws.leaves([second])), False{}, Equal.sym(Bool, List.is_empty(&2, Nat, GrammarLaws.leaves([second])), True{}, Equal.cong(+List<Nat>, Bool, x => List.is_empty(&2, Nat, x), GrammarLaws.leaves([second]), [], e2)), tree_nonempty(second, grammar, binary, c, f2))))
    case Con{+h1, +r1} Con{+h2, +r2}:
      +count = List.length(&2, Nat, inputTokens)
      +table = Grammar.buildTable(grammar, inputTokens, count, count)
      +p1 = List.length(&2, Nat, r1)
      +q2 = List.length(&2, Nat, r2)
      +m = {Nat.add(p1, q2) : Nat}
      +w1 = {h1 <> r1 : +List<Nat>}
      +w2 = {h2 <> r2 : +List<Nat>}
      +joined = node_leaves(p, [first, second], List.append(&2, Nat, w1, w2), pair_leaves(first, second, w1, w2, e1, e2))
      +lSum = Equal.trans(Nat, l, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), Nat.add(1n+p1, 1n+q2), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), l, len), Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(1n+p1, 1n+q2), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([Types.Node{p, [first, second]}]), List.append(&2, Nat, w1, w2), joined), Lemma.length_append(w1, w2)))
      +lTwo = Equal.trans(Nat, l, Nat.add(1n+p1, 1n+q2), 1n+1n+m, lSum, Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p1, 1n+q2), 1n+m, Lemma.add_succ_right(p1, q2)))
      +atSum = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, Nat.add(1n+p1, 1n+q2)), Lemma.slice(inputTokens, s, l), List.append(&2, Nat, w1, w2), Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), Nat.add(1n+p1, 1n+q2), l, Equal.sym(Nat, l, Nat.add(1n+p1, 1n+q2), lSum)), Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, l), GrammarLaws.leaves([Types.Node{p, [first, second]}]), List.append(&2, Nat, w1, w2), at, joined))
      +at1 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, s, 1n+p1), w1, GrammarLaws.leaves([first]), Lemma.slice_left(inputTokens, s, w1, w2, atSum), Equal.sym(+List<Nat>, GrammarLaws.leaves([first]), w1, e1))
      +at2 = Equal.trans(+List<Nat>, Lemma.slice(inputTokens, Nat.add(s, 1n+p1), 1n+q2), w2, GrammarLaws.leaves([second]), Lemma.slice_right(inputTokens, s, w1, w2, atSum), Equal.sym(+List<Nat>, GrammarLaws.leaves([second]), w2, e2))
      +len1 = Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([first]), w1, e1)
      +len2 = Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([second]), w2, e2)
      +leSum = Equal.trans(Bool, Nat.is_le(Nat.add(1n+p1, 1n+q2), count), Nat.is_le(l, count), True{}, Equal.cong(Nat, Bool, n => Nat.is_le(n, count), Nat.add(1n+p1, 1n+q2), l, Equal.sym(Nat, l, Nat.add(1n+p1, 1n+q2), lSum)), le)
      +le1 = Lemma.le_trans(1n+p1, Nat.add(1n+p1, 1n+q2), count, Lemma.le_add_right(1n+p1, 1n+q2), leSum)
      +le2 = Lemma.le_trans(1n+q2, Nat.add(1n+p1, 1n+q2), count, Lemma.le_add_left(1n+p1, 1n+q2), leSum)
      inFirst = firstInSet(b, s, 1n+p1, f1, at1, len1, le1)
      inSecond = secondInSet(c, Nat.add(s, 1n+p1), 1n+q2, f2, at2, len2, le2)
      inLefts = cell_complete(first, grammar, inputTokens, binary, b, s, 1n+p1, count, f1, at1, len1, le1)
      inRights = cell_complete(second, grammar, inputTokens, binary, c, Nat.add(s, 1n+p1), 1n+q2, count, f2, at2, len2, le2)
      +element = {Types.Bsr{Types.Slot{p, 2n}, s, Nat.add(s, 1n+p1), Nat.add(s, Nat.add(1n+p1, 1n+q2))} : Types.Bsr}
      hit = binary_steps_member(grammar, Grammar.lookup(table, s, 1n+p1), Grammar.lookup(table, Nat.add(s, 1n+p1), 1n+q2), s, Nat.add(s, 1n+p1), Nat.add(s, Nat.add(1n+p1, 1n+q2)), 0n, p, b, c, rhsOk, inLefts, inRights)
      sum = Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p1, 1n+q2), Nat.add(m, 1n), Equal.trans(Nat, Nat.add(p1, 1n+q2), 1n+m, Nat.add(m, 1n), Lemma.add_succ_right(p1, q2), Equal.sym(Nat, Nat.add(m, 1n), 1n+m, Lemma.add_one_right(m))))
      inSplit = split_steps_member(grammar, table, s, element, p1, 1n+q2, 1n+m, 1n, Lemma.le_add_right(p1, q2), sum, hit)
      +lt = Lemma.slice_start_lt(inputTokens, s, Nat.add(1n+p1, 1n+q2), h1, List.append(&2, Nat, r1, w2), atSum)
      leTwo = Equal.trans(Bool, Nat.is_le(1n+1n+m, count), Nat.is_le(l, count), True{}, Equal.cong(Nat, Bool, n => Nat.is_le(n, count), 1n+1n+m, l, Equal.sym(Nat, l, 1n+1n+m, lTwo)), le)
      inAll = all_member(grammar, inputTokens, table, count, 1n+m, element, count, leTwo, row_member(grammar, inputTokens, table, 1n+1n+m, s, element, count, lt, inSplit))
      +set = Grammar.cykSteps(grammar, inputTokens)
      embed_two(
        first, second, grammar, b, c, set, p, s, f1, f2,
        move_pair_member(set, p, s, List.length(&2, Nat, GrammarLaws.leaves([first])), 1n+p1, List.length(&2, Nat, GrammarLaws.leaves([second])), 1n+q2, len1, len2, inAll),
        inFirst,
        move_embedded(set, second, s, List.length(&2, Nat, GrammarLaws.leaves([first])), 1n+p1, len1, inSecond))


law pair_complete:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for facts: TwoChildren(grammar, p, a, first, second)
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([Types.Node{p, [first, second]}]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])) == l : Nat}
  for le: {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for firstInSet: ChildInSet(grammar, inputTokens, first)
  for secondInSet: ChildInSet(grammar, inputTokens, second)
  InSet(grammar, inputTokens, Types.Node{p, [first, second]}, s)

def pair_complete(grammar, inputTokens, binary, a, s, l, p, first, second, facts, at, len, le, firstInSet, secondInSet):
  match facts:
    case (b, (c, (lhsOk, (rhsOk, (f1, f2))))):
      pair_complete_parts(grammar, inputTokens, binary, a, s, l, p, first, second, b, c, lhsOk, rhsOk, f1, f2, GrammarLaws.leaves([first]), GrammarLaws.leaves([second]), {==}, {==}, at, len, le, firstInSet, secondInSet)


# Every node of a parse tree of the slice (s, l) has its step in the BSR set.
law tree_in_set:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for at: {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([t]) : +List<Nat>}
  for len: {List.length(&2, Nat, GrammarLaws.leaves([t])) == l : Nat}
  for le: {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  InSet(grammar, inputTokens, t, s)

def tree_in_set(t, grammar, inputTokens, binary, a, s, l, fitting, at, len, le):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd(InSet(grammar, inputTokens, Types.Leaf{kind}, s), Lemma.false_is_not_true(fitting))
    case Types.Node{+p, children}:
      match children:
        case Nil{}:
          Empty.absurd(InSet(grammar, inputTokens, Types.Node{p, []}, s), no_children(grammar, p, a, binary, fitting))
        case Con{+t1, Nil{}}:
          leaf_complete(grammar, inputTokens, a, s, l, p, t1, one_child_facts(grammar, p, a, t1, binary, fitting), at, len)
        case Con{+t1, Con{+t2, Nil{}}}:
          pair_complete(
            grammar, inputTokens, binary, a, s, l, p, t1, t2,
            two_children_facts(grammar, p, a, t1, t2, binary, fitting),
            at, len, le,
            b1 => s1 => l1 => f1 => at1 => len1 => le1 => tree_in_set(t1, grammar, inputTokens, binary, b1, s1, l1, f1, at1, len1, le1),
            b2 => s2 => l2 => f2 => at2 => len2 => le2 => tree_in_set(t2, grammar, inputTokens, binary, b2, s2, l2, f2, at2, len2, le2))
        case Con{+t1, Con{+t2, Con{+t3, +more}}}:
          Empty.absurd(InSet(grammar, inputTokens, Types.Node{p, t1 <> t2 <> t3 <> more}, s), many_children(grammar, p, a, t1, t2, t3, more, binary, fitting))


# ---- Completeness ----

# Every parse tree of the input is embedded in the CYK steps.
law cyk_embedded_every:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +tree: Types.Tree
  for binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for fitting: {GrammarLaws.fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for spelled: {GrammarLaws.leaves([tree]) == inputTokens : +List<Nat>}
  {embedded(tree, Grammar.cykSteps(grammar, inputTokens), 0n) == True{} : Bool}

def cyk_embedded_every(grammar, start, inputTokens, tree, binary, fitting, spelled):
  +count = List.length(&2, Nat, inputTokens)
  +both = spelled
  tree_in_set(
    tree, grammar, inputTokens, binary, start, 0n, count, fitting,
    Equal.trans(+List<Nat>, Lemma.takeN(count, inputTokens), inputTokens, GrammarLaws.leaves([tree]), Lemma.take_length(inputTokens), Equal.sym(+List<Nat>, GrammarLaws.leaves([tree]), inputTokens, both)),
    Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([tree]), inputTokens, both),
    Lemma.le_refl(count))


# ======== NOTHING MISSING ========
#
# Pruning keeps every step of every parse tree. Down a parse tree, each node's
# need appears one round after its parent's (needs_at_next); a node with l leaves
# is needed by round count - l, so `count` rounds reach them all (tree_kept).

def NeedsAt(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +n: Nat) -> +List<Grammar.Need>:
  Grammar.needsAt(grammar, start, List.length(&2, Nat, inputTokens), Grammar.cykSteps(grammar, inputTokens), n)

# ---- Membership in lists of needs ----

law need_member_head:
  for +a: Nat
  for +i: Nat
  for +j: Nat
  for +rest: +List<Grammar.Need>
  {Grammar.needMember(Grammar.Need{a, i, j}, Grammar.Need{a, i, j} <> rest) == True{} : Bool}

def need_member_head(a, i, j, rest):
  Lemma.or_true_left_intro(Bool.and(Nat.is_eq(a, a), Bool.and(Nat.is_eq(i, i), Nat.is_eq(j, j))), Grammar.needMember(Grammar.Need{a, i, j}, rest),
    Lemma.and_true_intro(Nat.is_eq(a, a), Bool.and(Nat.is_eq(i, i), Nat.is_eq(j, j)), Lemma.nat_eq_refl(a),
      Lemma.and_true_intro(Nat.is_eq(i, i), Nat.is_eq(j, j), Lemma.nat_eq_refl(i), Lemma.nat_eq_refl(j))))

law need_member_cons:
  for need: Grammar.Need
  for +x: Grammar.Need
  for +rest: +List<Grammar.Need>
  for e: {Grammar.needMember(need, rest) == True{} : Bool}
  {Grammar.needMember(need, x <> rest) == True{} : Bool}

def need_member_cons(need, x, rest, e):
  match need x:
    case Grammar.Need{+a, +i, +j} Grammar.Need{a2, i2, j2}:
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))), Grammar.needMember(Grammar.Need{a, i, j}, rest), e)

law need_member_append_right:
  for +need: Grammar.Need
  for xs: +List<Grammar.Need>
  for +ys: +List<Grammar.Need>
  for e: {Grammar.needMember(need, ys) == True{} : Bool}
  {Grammar.needMember(need, List.append(&2, Grammar.Need, xs, ys)) == True{} : Bool}

def need_member_append_right(need, xs, ys, e):
  match xs:
    case Nil{}:
      e
    case Con{+x, +rest}:
      need_member_cons(need, x, List.append(&2, Grammar.Need, rest, ys), need_member_append_right(need, rest, ys, e))

law need_member_append_left:
  for need: Grammar.Need
  for xs: +List<Grammar.Need>
  for +ys: +List<Grammar.Need>
  for e: {Grammar.needMember(need, xs) == True{} : Bool}
  {Grammar.needMember(need, List.append(&2, Grammar.Need, xs, ys)) == True{} : Bool}

def need_member_append_left(need, xs, ys, e):
  match need:
    case Grammar.Need{+a, +i, +j}:
      match xs:
        case Nil{}:
          Empty.absurd({Grammar.needMember(Grammar.Need{a, i, j}, ys) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Con{Grammar.Need{+a2, +i2, +j2}, +rest}:
          Lemma.or_mono_right(
            Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))),
            Grammar.needMember(Grammar.Need{a, i, j}, rest),
            Grammar.needMember(Grammar.Need{a, i, j}, List.append(&2, Grammar.Need, rest, ys)),
            e,
            inRest => need_member_append_left(Grammar.Need{a, i, j}, rest, ys, inRest))

# ---- An element of a list is the head or in the tail ----

law member_cons_pick:
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +d2: Nat
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for -rest: +List<Types.Bsr>
  for cases: Either<{Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))) == True{} : Bool}, {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool}>
  Either<{Types.Bsr{Types.Slot{p, d}, i, k, j} == Types.Bsr{Types.Slot{p2, d2}, i2, k2, j2} : Types.Bsr}, {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest) == True{} : Bool}>

def member_cons_pick(p, d, i, k, j, p2, d2, i2, k2, j2, rest, cases):
  match cases:
    case Inl{same}:
      Inl{bsr_eq_sound(p, d, i, k, j, p2, d2, i2, k2, j2, same)}
    case Inr{later}:
      Inr{later}

law member_cons_cases:
  for element: Types.Bsr
  for x: Types.Bsr
  for -rest: +List<Types.Bsr>
  for m: {GrammarLaws.bsrMember(element, x <> rest) == True{} : Bool}
  Either<{element == x : Types.Bsr}, {GrammarLaws.bsrMember(element, rest) == True{} : Bool}>

def member_cons_cases(element, x, rest, m):
  match element x:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j} Types.Bsr{Types.Slot{+p2, +d2}, +i2, +k2, +j2}:
      member_cons_pick(p, d, i, k, j, p2, d2, i2, k2, j2, rest,
        Lemma.or_true_cases(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(d, d2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, rest), m))

law not_in_empty:
  for element: Types.Bsr
  for m: {GrammarLaws.bsrMember(element, []) == True{} : Bool}
  Empty

def not_in_empty(element, m):
  match element:
    case Types.Bsr{Types.Slot{p, d}, i, k, j}:
      Lemma.false_is_not_true(m)

# ---- Filtering keeps the needed elements ----

law keep_needed_head:
  for keep: Bool
  for +x: Types.Bsr
  for +others: +List<Types.Bsr>
  for k: {keep == True{} : Bool}
  {GrammarLaws.bsrMember(x, Grammar.keepNeeded(keep, x, others)) == True{} : Bool}

def keep_needed_head(keep, x, others, k):
  match keep:
    case True{}:
      bsr_member_head(x, others)
    case False{}:
      Empty.absurd({GrammarLaws.bsrMember(x, others) == True{} : Bool}, Lemma.false_is_not_true(k))

law keep_needed_later:
  for keep: Bool
  for +x: Types.Bsr
  for +others: +List<Types.Bsr>
  for element: Types.Bsr
  for m: {GrammarLaws.bsrMember(element, others) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.keepNeeded(keep, x, others)) == True{} : Bool}

def keep_needed_later(keep, x, others, element, m):
  match keep:
    case False{}:
      m
    case True{}:
      bsr_member_cons(element, x, others, m)

law filter_pick:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for +element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for cases: Either<{element == x : Types.Bsr}, {GrammarLaws.bsrMember(element, rest) == True{} : Bool}>
  for +needed: {Grammar.isNeeded(grammar, needs, element) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(element, rest) == True{} : Bool} -> {GrammarLaws.bsrMember(element, Grammar.filterNeeded(grammar, needs, rest)) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.keepNeeded(Grammar.isNeeded(grammar, needs, x), x, Grammar.filterNeeded(grammar, needs, rest))) == True{} : Bool}

def filter_pick(grammar, needs, element, x, rest, cases, needed, searchRest):
  match cases:
    case Inl{same}:
      +eq = same
      +others = Grammar.filterNeeded(grammar, needs, rest)
      neededX = Equal.trans(Bool, Grammar.isNeeded(grammar, needs, x), Grammar.isNeeded(grammar, needs, element), True{},
        Equal.sym(Bool, Grammar.isNeeded(grammar, needs, element), Grammar.isNeeded(grammar, needs, x), Equal.cong(Types.Bsr, Bool, v => Grammar.isNeeded(grammar, needs, v), element, x, eq)),
        needed)
      %Equal.sym(Types.Bsr, element, x, eq) : {GrammarLaws.bsrMember(_, Grammar.keepNeeded(Grammar.isNeeded(grammar, needs, x), x, others)) == True{} : Bool}
      keep_needed_head(Grammar.isNeeded(grammar, needs, x), x, others, neededX)
    case Inr{later}:
      keep_needed_later(Grammar.isNeeded(grammar, needs, x), x, Grammar.filterNeeded(grammar, needs, rest), element, searchRest(later))

law filter_member:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for xs: +List<Types.Bsr>
  for +element: Types.Bsr
  for m: {GrammarLaws.bsrMember(element, xs) == True{} : Bool}
  for +needed: {Grammar.isNeeded(grammar, needs, element) == True{} : Bool}
  {GrammarLaws.bsrMember(element, Grammar.filterNeeded(grammar, needs, xs)) == True{} : Bool}

def filter_member(grammar, needs, xs, element, m, needed):
  match xs:
    case Nil{}:
      Empty.absurd({GrammarLaws.bsrMember(element, []) == True{} : Bool}, not_in_empty(element, m))
    case Con{+x, +rest}:
      filter_pick(grammar, needs, element, x, rest, member_cons_cases(element, x, rest, m), needed,
        later => filter_member(grammar, needs, rest, element, later, needed))

# ---- The needs of kept elements ----

law child_pick:
  for +grammar: +List<Types.Production>
  for +need: Grammar.Need
  for +element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for cases: Either<{element == x : Types.Bsr}, {GrammarLaws.bsrMember(element, rest) == True{} : Bool}>
  for +inChild: {Grammar.needMember(need, Grammar.childNeeds(grammar, element)) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(element, rest) == True{} : Bool} -> {Grammar.needMember(need, Grammar.allChildNeeds(grammar, rest)) == True{} : Bool}
  {Grammar.needMember(need, List.append(&2, Grammar.Need, Grammar.childNeeds(grammar, x), Grammar.allChildNeeds(grammar, rest))) == True{} : Bool}

def child_pick(grammar, need, element, x, rest, cases, inChild, searchRest):
  match cases:
    case Inl{same}:
      inX = Equal.trans(Bool, Grammar.needMember(need, Grammar.childNeeds(grammar, x)), Grammar.needMember(need, Grammar.childNeeds(grammar, element)), True{},
        Equal.sym(Bool, Grammar.needMember(need, Grammar.childNeeds(grammar, element)), Grammar.needMember(need, Grammar.childNeeds(grammar, x)), Equal.cong(Types.Bsr, Bool, v => Grammar.needMember(need, Grammar.childNeeds(grammar, v)), element, x, same)),
        inChild)
      need_member_append_left(need, Grammar.childNeeds(grammar, x), Grammar.allChildNeeds(grammar, rest), inX)
    case Inr{later}:
      need_member_append_right(need, Grammar.childNeeds(grammar, x), Grammar.allChildNeeds(grammar, rest), searchRest(later))

law child_needs_member:
  for +grammar: +List<Types.Production>
  for xs: +List<Types.Bsr>
  for +element: Types.Bsr
  for +need: Grammar.Need
  for m: {GrammarLaws.bsrMember(element, xs) == True{} : Bool}
  for +inChild: {Grammar.needMember(need, Grammar.childNeeds(grammar, element)) == True{} : Bool}
  {Grammar.needMember(need, Grammar.allChildNeeds(grammar, xs)) == True{} : Bool}

def child_needs_member(grammar, xs, element, need, m, inChild):
  match xs:
    case Nil{}:
      Empty.absurd({Grammar.needMember(need, []) == True{} : Bool}, not_in_empty(element, m))
    case Con{+x, +rest}:
      child_pick(grammar, need, element, x, rest, member_cons_cases(element, x, rest, m), inChild,
        later => child_needs_member(grammar, rest, element, need, later, inChild))

# A needed element of the CYK steps passes its needs on to the next round.
law needs_at_next:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +n: Nat
  for +element: Types.Bsr
  for +need: Grammar.Need
  for inSteps: {GrammarLaws.bsrMember(element, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for +needed: {Grammar.isNeeded(grammar, NeedsAt(grammar, start, inputTokens, n), element) == True{} : Bool}
  for +inChild: {Grammar.needMember(need, Grammar.childNeeds(grammar, element)) == True{} : Bool}
  {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, 1n+n)) == True{} : Bool}

def needs_at_next(grammar, start, inputTokens, n, element, need, inSteps, needed, inChild):
  +before = NeedsAt(grammar, start, inputTokens, n)
  +steps = Grammar.cykSteps(grammar, inputTokens)
  need_member_append_right(need, before, Grammar.allChildNeeds(grammar, Grammar.filterNeeded(grammar, before, steps)),
    child_needs_member(grammar, Grammar.filterNeeded(grammar, before, steps), element, need, filter_member(grammar, before, steps, element, inSteps, needed), inChild))

# The needs of a step A = B C.
law pair_need_first:
  for +grammar: +List<Types.Production>
  for +p: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  {Grammar.needMember(Grammar.Need{b, i, k}, Grammar.childNeeds(grammar, Types.Bsr{Types.Slot{p, 2n}, i, k, j})) == True{} : Bool}

def pair_need_first(grammar, p, b, c, i, k, j, rhsOk):
  %Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, p), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk) : {Grammar.needMember(Grammar.Need{b, i, k}, Grammar.pairNeeds(_, i, k, j)) == True{} : Bool}
  need_member_head(b, i, k, [Grammar.Need{c, k, j}])

law pair_need_second:
  for +grammar: +List<Types.Production>
  for +p: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  {Grammar.needMember(Grammar.Need{c, k, j}, Grammar.childNeeds(grammar, Types.Bsr{Types.Slot{p, 2n}, i, k, j})) == True{} : Bool}

def pair_need_second(grammar, p, b, c, i, k, j, rhsOk):
  %Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, p), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk) : {Grammar.needMember(Grammar.Need{c, k, j}, Grammar.pairNeeds(_, i, k, j)) == True{} : Bool}
  need_member_cons(Grammar.Need{c, k, j}, Grammar.Need{b, i, k}, [Grammar.Need{c, k, j}], need_member_head(c, k, j, []))

# ---- Needs only grow ----

law mono_pick:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +need: Grammar.Need
  for +n: Nat
  for +m: Nat
  for same: Bool
  for +sameEq: {Nat.is_eq(1n+m, n) == same : Bool}
  for le: {Nat.is_le(n, 1n+m) == True{} : Bool}
  for +inN: {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  for ih: {Nat.is_le(n, m) == True{} : Bool} -> {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, m)) == True{} : Bool}
  {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, 1n+m)) == True{} : Bool}

def mono_pick(grammar, start, inputTokens, need, n, m, same, sameEq, le, inN, ih):
  match same:
    case True{}:
      %Equal.sym(Nat, 1n+m, n, Lemma.nat_eq_sound(1n+m, n, sameEq)) : {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, _)) == True{} : Bool}
      inN
    case False{}:
      +before = NeedsAt(grammar, start, inputTokens, m)
      +steps = Grammar.cykSteps(grammar, inputTokens)
      need_member_append_left(need, before, Grammar.allChildNeeds(grammar, Grammar.filterNeeded(grammar, before, steps)), ih(Lemma.le_succ_ne(n, 1n+m, le, sameEq)))

law needs_at_mono:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +need: Grammar.Need
  for n: Nat
  for upTo: Nat
  for le: {Nat.is_le(n, upTo) == True{} : Bool}
  for +inN: {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, upTo)) == True{} : Bool}

def needs_at_mono(grammar, start, inputTokens, need, n, upTo, le, inN):
  match n upTo:
    case 0n 0n:
      inN
    case 1n+r 0n:
      Empty.absurd({Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, 0n)) == True{} : Bool}, Lemma.false_is_not_true(le))
    case +n 1n+(+m):
      +leN = le
      mono_pick(grammar, start, inputTokens, need, n, m, Nat.is_eq(1n+m, n), {==}, leN, inN,
        leM => needs_at_mono(grammar, start, inputTokens, need, n, m, leM, inN))

# ---- Kept elements ----

law lhs_of_is:
  for +grammar: +List<Types.Production>
  for p: Nat
  for +a: Nat
  for e: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  {Grammar.lhsOf(grammar, p) == a : Nat}

def lhs_of_is(grammar, p, a, e):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Nil{} 1n+q:
      Empty.absurd({0n == a : Nat}, Lemma.false_is_not_true(e))
    case Con{Types.Production{+lhs, rhs}, rest} 0n:
      Lemma.nat_eq_sound(lhs, a, e)
    case Con{prod, +rest} 1n+q:
      lhs_of_is(rest, q, a, e)

law needed_of:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +a: Nat
  for lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for +needed: {Grammar.needMember(Grammar.Need{a, i, j}, needs) == True{} : Bool}
  {Grammar.isNeeded(grammar, needs, Types.Bsr{Types.Slot{p, d}, i, k, j}) == True{} : Bool}

def needed_of(grammar, needs, p, d, i, k, j, a, lhsOk, needed):
  %Equal.sym(Nat, Grammar.lhsOf(grammar, p), a, lhs_of_is(grammar, p, a, lhsOk)) : {Grammar.needMember(Grammar.Need{_, i, j}, needs) == True{} : Bool}
  needed

# A CYK step that is needed in some round within `count` rounds is in the BSR set.
law kept_of:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +a: Nat
  for +n: Nat
  for +inSteps: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for +lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for +needed: {Grammar.needMember(Grammar.Need{a, i, j}, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  for +le: {Nat.is_le(n, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{p, d}, i, k, j}, Grammar.bsrSet(grammar, start, inputTokens)) == True{} : Bool}

def kept_of(grammar, start, inputTokens, p, d, i, k, j, a, n, inSteps, lhsOk, needed, le):
  +count = List.length(&2, Nat, inputTokens)
  +last = NeedsAt(grammar, start, inputTokens, count)
  filter_member(grammar, last, Grammar.cykSteps(grammar, inputTokens), Types.Bsr{Types.Slot{p, d}, i, k, j}, inSteps,
    needed_of(grammar, last, p, d, i, k, j, a, lhsOk,
      needs_at_mono(grammar, start, inputTokens, Grammar.Need{a, i, j}, n, count, le, needed)))


# ---- Arithmetic for the round budget ----

law add_le_mono:
  for n: Nat
  for +x: Nat
  for +y: Nat
  for le: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.is_le(Nat.add(n, x), Nat.add(n, y)) == True{} : Bool}

def add_le_mono(n, x, y, le):
  match n:
    case 0n:
      le
    case 1n+m:
      add_le_mono(m, x, y, le)

# A child of a node with two children has fewer leaves, so it fits in one more round.
law budget_left:
  for +n: Nat
  for +x: Nat
  for y: Nat
  for +c: Nat
  for yPos: {Nat.is_le(1n, y) == True{} : Bool}
  for le: {Nat.is_le(Nat.add(n, Nat.add(x, y)), c) == True{} : Bool}
  {Nat.is_le(Nat.add(1n+n, x), c) == True{} : Bool}

def budget_left(n, x, y, c, yPos, le):
  match y:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+n, x), c) == True{} : Bool}, Lemma.false_is_not_true(yPos))
    case 1n+(+q):
      +sum = Equal.trans(Nat, Nat.add(n, Nat.add(x, 1n+q)), Nat.add(n, 1n+Nat.add(x, q)), 1n+Nat.add(n, Nat.add(x, q)),
        Equal.cong(Nat, Nat, v => Nat.add(n, v), Nat.add(x, 1n+q), 1n+Nat.add(x, q), Lemma.add_succ_right(x, q)),
        Lemma.add_succ_right(n, Nat.add(x, q)))
      big = Equal.trans(Bool, Nat.is_le(1n+Nat.add(n, Nat.add(x, q)), c), Nat.is_le(Nat.add(n, Nat.add(x, 1n+q)), c), True{},
        Equal.cong(Nat, Bool, v => Nat.is_le(v, c), 1n+Nat.add(n, Nat.add(x, q)), Nat.add(n, Nat.add(x, 1n+q)), Equal.sym(Nat, Nat.add(n, Nat.add(x, 1n+q)), 1n+Nat.add(n, Nat.add(x, q)), sum)),
        le)
      small = Equal.trans(Bool, Nat.is_le(Nat.add(n, x), Nat.add(n, Nat.add(x, q))), Nat.is_le(Nat.add(n, x), Nat.add(Nat.add(n, x), q)), True{},
        Equal.cong(Nat, Bool, v => Nat.is_le(Nat.add(n, x), v), Nat.add(n, Nat.add(x, q)), Nat.add(Nat.add(n, x), q), Equal.sym(Nat, Nat.add(Nat.add(n, x), q), Nat.add(n, Nat.add(x, q)), Lemma.add_assoc(n, x, q))),
        Lemma.le_add_right(Nat.add(n, x), q))
      Lemma.le_trans(1n+Nat.add(n, x), 1n+Nat.add(n, Nat.add(x, q)), c, small, big)

law budget_right:
  for +n: Nat
  for x: Nat
  for +y: Nat
  for +c: Nat
  for xPos: {Nat.is_le(1n, x) == True{} : Bool}
  for le: {Nat.is_le(Nat.add(n, Nat.add(x, y)), c) == True{} : Bool}
  {Nat.is_le(Nat.add(1n+n, y), c) == True{} : Bool}

def budget_right(n, x, y, c, xPos, le):
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+n, y), c) == True{} : Bool}, Lemma.false_is_not_true(xPos))
    case 1n+(+p):
      big = Equal.trans(Bool, Nat.is_le(1n+Nat.add(n, Nat.add(p, y)), c), Nat.is_le(Nat.add(n, 1n+Nat.add(p, y)), c), True{},
        Equal.cong(Nat, Bool, v => Nat.is_le(v, c), 1n+Nat.add(n, Nat.add(p, y)), Nat.add(n, 1n+Nat.add(p, y)), Equal.sym(Nat, Nat.add(n, 1n+Nat.add(p, y)), 1n+Nat.add(n, Nat.add(p, y)), Lemma.add_succ_right(n, Nat.add(p, y)))),
        le)
      Lemma.le_trans(1n+Nat.add(n, y), 1n+Nat.add(n, Nat.add(p, y)), c, add_le_mono(n, y, Nat.add(p, y), Lemma.le_add_left(p, y)), big)

law nonempty_pos:
  for xs: +List<Nat>
  for e: {List.is_empty(&2, Nat, xs) == False{} : Bool}
  {Nat.is_le(1n, List.length(&2, Nat, xs)) == True{} : Bool}

def nonempty_pos(xs, e):
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Lemma.true_is_not_false(e))
    case Con{x, rest}:
      Lemma.zero_le(List.length(&2, Nat, rest))

# ---- Where the parts of a node with two children end ----

law pair_length:
  for -p: Nat
  for -q1: Nat
  for +ch1: +List<Types.Tree>
  for -q2: Nat
  for +ch2: +List<Types.Tree>
  {List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}])) == Nat.add(List.length(&2, Nat, GrammarLaws.leaves(ch1)), List.length(&2, Nat, GrammarLaws.leaves(ch2))) : Nat}

def pair_length(p, q1, ch1, q2, ch2):
  +l1 = GrammarLaws.leaves(ch1)
  +l2 = GrammarLaws.leaves(ch2)
  +inner = List.append(&2, Nat, l1, List.append(&2, Nat, l2, []))
  joined = Equal.trans(+List<Nat>, List.append(&2, Nat, inner, []), inner, List.append(&2, Nat, l1, l2),
    Lemma.append_nil_right(inner),
    Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, l1, v), List.append(&2, Nat, l2, []), l2, Lemma.append_nil_right(l2)))
  Equal.trans(Nat, List.length(&2, Nat, List.append(&2, Nat, inner, [])), List.length(&2, Nat, List.append(&2, Nat, l1, l2)), Nat.add(List.length(&2, Nat, l1), List.length(&2, Nat, l2)),
    Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, inner, []), List.append(&2, Nat, l1, l2), joined),
    Lemma.length_append(l1, l2))

law pair_end:
  for -p: Nat
  for -q1: Nat
  for +ch1: +List<Types.Tree>
  for -q2: Nat
  for +ch2: +List<Types.Tree>
  for +s: Nat
  {Nat.add(Nat.add(s, List.length(&2, Nat, GrammarLaws.leaves(ch1))), List.length(&2, Nat, GrammarLaws.leaves(ch2))) == endOf(Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}, s) : Nat}

def pair_end(p, q1, ch1, q2, ch2, s):
  +n1 = List.length(&2, Nat, GrammarLaws.leaves(ch1))
  +n2 = List.length(&2, Nat, GrammarLaws.leaves(ch2))
  Equal.trans(Nat, Nat.add(Nat.add(s, n1), n2), Nat.add(s, Nat.add(n1, n2)), endOf(Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}, s),
    Lemma.add_assoc(s, n1, n2),
    Equal.cong(Nat, Nat, v => Nat.add(s, v), Nat.add(n1, n2), List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}])),
      Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}])), Nat.add(n1, n2), pair_length(p, q1, ch1, q2, ch2))))

# A need with the end written one way is the need with the end written another way.
law move_need:
  for +needs: +List<Grammar.Need>
  for +a: Nat
  for +i: Nat
  for -j: Nat
  for -j2: Nat
  for e: {j == j2 : Nat}
  for m: {Grammar.needMember(Grammar.Need{a, i, j}, needs) == True{} : Bool}
  {Grammar.needMember(Grammar.Need{a, i, j2}, needs) == True{} : Bool}

def move_need(needs, a, i, j, j2, e, m):
  %e : {Grammar.needMember(Grammar.Need{a, i, _}, needs) == True{} : Bool}
  m

# ---- Every node of a parse tree is kept ----

def Kept(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>) -> +List<Types.Bsr>:
  Grammar.bsrSet(grammar, start, inputTokens)

def KeptIH(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +t: Types.Tree) -> Type:
  @b: Nat -> @s: Nat -> @n: Nat ->
    {GrammarLaws.fits([t], grammar, [Types.Nonterminal{b}]) == True{} : Bool} ->
    {embedded(t, Grammar.cykSteps(grammar, inputTokens), s) == True{} : Bool} ->
    {Grammar.needMember(Grammar.Need{b, s, endOf(t, s)}, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool} ->
    {Nat.is_le(Nat.add(n, List.length(&2, Nat, GrammarLaws.leaves([t]))), List.length(&2, Nat, inputTokens)) == True{} : Bool} ->
    {embedded(t, Kept(grammar, start, inputTokens), s) == True{} : Bool}

def treeIsLeaf(t: Types.Tree) -> Bool:
  match t:
    case Types.Leaf{k}:
      True{}
    case Types.Node{q, cs}:
      False{}

law leaf_kept:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +n: Nat
  for +p: Nat
  for child: Types.Tree
  for facts: OneChild(grammar, p, a, child)
  for emb: {embedded(Types.Node{p, [child]}, Grammar.cykSteps(grammar, inputTokens), s) == True{} : Bool}
  for needed: {Grammar.needMember(Grammar.Need{a, s, endOf(Types.Node{p, [child]}, s)}, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  for budget: {Nat.is_le(Nat.add(n, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [child]}]))), List.length(&2, Nat, inputTokens)) == True{} : Bool}
  {embedded(Types.Node{p, [child]}, Kept(grammar, start, inputTokens), s) == True{} : Bool}

def leaf_kept(grammar, start, inputTokens, a, s, n, p, child, facts, emb, needed, budget):
  match child:
    case Types.Node{q, cs}:
      match facts:
        case (kind, (isLeaf, rest)):
          Empty.absurd({embedded(Types.Node{p, [Types.Node{q, cs}]}, Kept(grammar, start, inputTokens), s) == True{} : Bool},
            Lemma.false_is_not_true(Equal.cong(Types.Tree, Bool, x => treeIsLeaf(x), Types.Node{q, cs}, Types.Leaf{kind}, isLeaf)))
    case Types.Leaf{+kind}:
      match facts:
        case (kind2, (isLeaf, (lhsOk, rhsOk))):
          +count = List.length(&2, Nat, inputTokens)
          +steps = Grammar.cykSteps(grammar, inputTokens)
          +element = {Types.Bsr{Types.Slot{p, 1n}, s, s, 1n+s} : Types.Bsr}
          +both = emb
          inSteps = Lemma.and_true_left(GrammarLaws.bsrMember(element, steps), True{}, both)
          neededHere = move_need(NeedsAt(grammar, start, inputTokens, n), a, s, Nat.add(s, 1n), 1n+s, Lemma.add_one_right(s), needed)
          leN = Lemma.le_trans(n, Nat.add(n, 1n), count, Lemma.le_add_right(n, 1n), budget)
          kept = kept_of(grammar, start, inputTokens, p, 1n, s, s, 1n+s, a, n, inSteps, lhsOk, neededHere, leN)
          Lemma.and_true_intro(GrammarLaws.bsrMember(element, Kept(grammar, start, inputTokens)), True{}, kept, {==})

law pair_kept:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +n: Nat
  for +p: Nat
  for first: Types.Tree
  for second: Types.Tree
  for facts: TwoChildren(grammar, p, a, first, second)
  for emb: {embedded(Types.Node{p, [first, second]}, Grammar.cykSteps(grammar, inputTokens), s) == True{} : Bool}
  for needed: {Grammar.needMember(Grammar.Need{a, s, endOf(Types.Node{p, [first, second]}, s)}, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  for budget: {Nat.is_le(Nat.add(n, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}]))), List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for ih1: KeptIH(grammar, start, inputTokens, first)
  for ih2: KeptIH(grammar, start, inputTokens, second)
  {embedded(Types.Node{p, [first, second]}, Kept(grammar, start, inputTokens), s) == True{} : Bool}

def pair_kept(grammar, start, inputTokens, binary, a, s, n, p, first, second, facts, emb, needed, budget, ih1, ih2):
  match first second:
    case Types.Leaf{k} _:
      match facts:
        case (b, (c, (lhsOk, (rhsOk, (f1, f2))))):
          Empty.absurd({embedded(Types.Node{p, [Types.Leaf{k}, second]}, Kept(grammar, start, inputTokens), s) == True{} : Bool}, Lemma.false_is_not_true(f1))
    case Types.Node{q1, ch1} Types.Leaf{k}:
      match facts:
        case (b, (c, (lhsOk, (rhsOk, (f1, f2))))):
          Empty.absurd({embedded(Types.Node{p, [Types.Node{q1, ch1}, Types.Leaf{k}]}, Kept(grammar, start, inputTokens), s) == True{} : Bool}, Lemma.false_is_not_true(f2))
    case Types.Node{+q1, +ch1} Types.Node{+q2, +ch2}:
      match facts:
        case (b0, (c0, (lhsOk0, (rhsOk0, (f10, f20))))):
          +b = {b0 : Nat}
          +c = {c0 : Nat}
          +lhsOk = {lhsOk0 : {Types.lhsIs(grammar, p, a) == True{} : Bool}}
          +rhsOk = {rhsOk0 : {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}}
          +f1 = {f10 : {GrammarLaws.fits([Types.Node{q1, ch1}], grammar, [Types.Nonterminal{b}]) == True{} : Bool}}
          +f2 = {f20 : {GrammarLaws.fits([Types.Node{q2, ch2}], grammar, [Types.Nonterminal{c}]) == True{} : Bool}}
          +count = List.length(&2, Nat, inputTokens)
          +steps = Grammar.cykSteps(grammar, inputTokens)
          +kept = Kept(grammar, start, inputTokens)
          +t1 = {Types.Node{q1, ch1} : Types.Tree}
          +t2 = {Types.Node{q2, ch2} : Types.Tree}
          +n1 = List.length(&2, Nat, GrammarLaws.leaves(ch1))
          +n2 = List.length(&2, Nat, GrammarLaws.leaves(ch2))
          +e1 = Nat.add(s, n1)
          +e2 = Nat.add(e1, n2)
          +element = {Types.Bsr{Types.Slot{p, 2n}, s, e1, e2} : Types.Bsr}
          +all = emb
          +rest1 = Lemma.and_true_right_side(embedded(t1, steps, s), Bool.and(GrammarLaws.bsrMember(element, steps), Bool.and(embedded(t2, steps, e1), True{})), all)
          +rest2 = Lemma.and_true_right_side(GrammarLaws.bsrMember(element, steps), Bool.and(embedded(t2, steps, e1), True{}), rest1)
          emb1 = Lemma.and_true_left(embedded(t1, steps, s), Bool.and(GrammarLaws.bsrMember(element, steps), Bool.and(embedded(t2, steps, e1), True{})), all)
          +inSteps = Lemma.and_true_left(GrammarLaws.bsrMember(element, steps), Bool.and(embedded(t2, steps, e1), True{}), rest1)
          emb2 = Lemma.and_true_left(embedded(t2, steps, e1), True{}, rest2)
          +before = NeedsAt(grammar, start, inputTokens, n)
          +neededRoot = move_need(before, a, s, endOf(Types.Node{p, [t1, t2]}, s), e2,
            Equal.sym(Nat, e2, endOf(Types.Node{p, [t1, t2]}, s), pair_end(p, q1, ch1, q2, ch2, s)), needed)
          +isNeeded = needed_of(grammar, before, p, 2n, s, e1, e2, a, lhsOk, neededRoot)
          +n1n = List.length(&2, Nat, GrammarLaws.leaves([t1]))
          +n2n = List.length(&2, Nat, GrammarLaws.leaves([t2]))
          +len1 = length_node_leaves(q1, ch1)
          +len2 = length_node_leaves(q2, ch2)
          need1 = move_need(NeedsAt(grammar, start, inputTokens, 1n+n), b, s, e1, endOf(t1, s),
            Equal.cong(Nat, Nat, v => Nat.add(s, v), n1, n1n, len1),
            needs_at_next(grammar, start, inputTokens, n, element, Grammar.Need{b, s, e1}, inSteps, isNeeded, pair_need_first(grammar, p, b, c, s, e1, e2, rhsOk)))
          need2 = move_need(NeedsAt(grammar, start, inputTokens, 1n+n), c, e1, e2, endOf(t2, e1),
            Equal.cong(Nat, Nat, v => Nat.add(e1, v), n2, n2n, len2),
            needs_at_next(grammar, start, inputTokens, n, element, Grammar.Need{c, e1, e2}, inSteps, isNeeded, pair_need_second(grammar, p, b, c, s, e1, e2, rhsOk)))
          +lenSplit = Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [t1, t2]}])), Nat.add(n1, n2), Nat.add(n1n, n2n),
            pair_length(p, q1, ch1, q2, ch2),
            Lemma.add_congr(n1, n1n, n2, n2n, len1, len2))
          +budgetSplit = Equal.trans(Bool, Nat.is_le(Nat.add(n, Nat.add(n1n, n2n)), count), Nat.is_le(Nat.add(n, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [t1, t2]}]))), count), True{},
            Equal.cong(Nat, Bool, v => Nat.is_le(Nat.add(n, v), count), Nat.add(n1n, n2n), List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [t1, t2]}])), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [t1, t2]}])), Nat.add(n1n, n2n), lenSplit)),
            budget)
          pos1 = nonempty_pos(GrammarLaws.leaves([t1]), tree_nonempty(t1, grammar, binary, b, f1))
          pos2 = nonempty_pos(GrammarLaws.leaves([t2]), tree_nonempty(t2, grammar, binary, c, f2))
          budget1 = budget_left(n, n1n, n2n, count, pos2, budgetSplit)
          budget2 = budget_right(n, n1n, n2n, count, pos1, budgetSplit)
          +leN = Lemma.le_trans(n, Nat.add(n, Nat.add(n1n, n2n)), count, Lemma.le_add_right(n, Nat.add(n1n, n2n)), budgetSplit)
          r1 = ih1(b, s, 1n+n, f1, emb1, need1, budget1)
          r2 = ih2(c, e1, 1n+n, f2, emb2, need2, budget2)
          keptHere = kept_of(grammar, start, inputTokens, p, 2n, s, e1, e2, a, n, inSteps, lhsOk, neededRoot, leN)
          Lemma.and_true_intro(embedded(t1, kept, s), Bool.and(GrammarLaws.bsrMember(element, kept), Bool.and(embedded(t2, kept, e1), True{})), r1,
            Lemma.and_true_intro(GrammarLaws.bsrMember(element, kept), Bool.and(embedded(t2, kept, e1), True{}), keptHere,
              Lemma.and_true_intro(embedded(t2, kept, e1), True{}, r2, {==})))

# Every node of a parse tree of a needed span is kept, when the rounds left cover its leaves.
law tree_kept:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for +a: Nat
  for +s: Nat
  for +n: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for emb: {embedded(t, Grammar.cykSteps(grammar, inputTokens), s) == True{} : Bool}
  for needed: {Grammar.needMember(Grammar.Need{a, s, endOf(t, s)}, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool}
  for budget: {Nat.is_le(Nat.add(n, List.length(&2, Nat, GrammarLaws.leaves([t]))), List.length(&2, Nat, inputTokens)) == True{} : Bool}
  {embedded(t, Kept(grammar, start, inputTokens), s) == True{} : Bool}

def tree_kept(t, grammar, start, inputTokens, binary, a, s, n, fitting, emb, needed, budget):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd({embedded(Types.Leaf{kind}, Kept(grammar, start, inputTokens), s) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Types.Node{+p, children}:
      match children:
        case Nil{}:
          Empty.absurd({embedded(Types.Node{p, []}, Kept(grammar, start, inputTokens), s) == True{} : Bool}, no_children(grammar, p, a, binary, fitting))
        case Con{+t1, Nil{}}:
          leaf_kept(grammar, start, inputTokens, a, s, n, p, t1, one_child_facts(grammar, p, a, t1, binary, fitting), emb, needed, budget)
        case Con{+t1, Con{+t2, Nil{}}}:
          pair_kept(grammar, start, inputTokens, binary, a, s, n, p, t1, t2, two_children_facts(grammar, p, a, t1, t2, binary, fitting), emb, needed, budget,
            b1 => s1 => n1 => f1 => e1 => m1 => g1 => tree_kept(t1, grammar, start, inputTokens, binary, b1, s1, n1, f1, e1, m1, g1),
            b2 => s2 => n2 => f2 => e2 => m2 => g2 => tree_kept(t2, grammar, start, inputTokens, binary, b2, s2, n2, f2, e2, m2, g2))
        case Con{+t1, Con{+t2, Con{+t3, +more}}}:
          Empty.absurd({embedded(Types.Node{p, t1 <> t2 <> t3 <> more}, Kept(grammar, start, inputTokens), s) == True{} : Bool}, many_children(grammar, p, a, t1, t2, t3, more, binary, fitting))


# ---- The law ----

def GrammarLaws.cyk_every_parse_step(grammar, start, inputTokens, binary):
  +bin = binary
  +tree => element => +fitting => +spelled => inTree =>
    +count = List.length(&2, Nat, inputTokens)
    +kept = Kept(grammar, start, inputTokens)
    +len = Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([tree]), inputTokens, spelled)
    emb = cyk_embedded_every(grammar, start, inputTokens, tree, bin, fitting, spelled)
    needed = move_need(NeedsAt(grammar, start, inputTokens, 0n), start, 0n, count, endOf(tree, 0n),
      Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([tree])), count, len),
      need_member_head(start, 0n, count, []))
    budget = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, GrammarLaws.leaves([tree])), count), Nat.is_le(count, count), True{},
      Equal.cong(Nat, Bool, v => Nat.is_le(v, count), List.length(&2, Nat, GrammarLaws.leaves([tree])), count, len),
      Lemma.le_refl(count))
    keptTree = tree_kept(tree, grammar, start, inputTokens, bin, start, 0n, 0n, fitting, emb, needed, budget)
    all_in_member(GrammarLaws.steps(tree, 0n), kept, element, embedded_all_in(tree, kept, 0n, keptTree), inTree)


# ======== BSR SUPPORT ========
#
# Every nonterminal in a cell of the table has a parse tree for the cell's slice of
# the input whose steps are all in the BSR set (cell_support). Every complete step in
# the set is built from such cells, which gives bsr_supported.

# ---- Where the cells of the table are ----

def cellsInRange(table: +List<Grammar.Cell>, +count: Nat, +fuel: Nat) -> Bool:
  match table:
    case Nil{}:
      True{}
    case Con{Grammar.Cell{start, +length, nts}, rest}:
      Bool.and(Nat.is_lt(start, count), Bool.and(Nat.is_le(1n, length), Bool.and(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel))))


law range_append:
  for xs: +List<Grammar.Cell>
  for -ys: +List<Grammar.Cell>
  for +count: Nat
  for +fuel: Nat
  for first: {cellsInRange(xs, count, fuel) == True{} : Bool}
  for second: {cellsInRange(ys, count, fuel) == True{} : Bool}
  {cellsInRange(List.append(&2, Grammar.Cell, xs, ys), count, fuel) == True{} : Bool}

def range_append(xs, ys, count, fuel, first, second):
  match xs:
    case Nil{}:
      second
    case Con{Grammar.Cell{+start, +length, nts}, +rest}:
      +all = first
      +a = Nat.is_lt(start, count)
      +b = Nat.is_le(1n, length)
      +c = Nat.is_le(length, fuel)
      +bcd = Lemma.and_true_right_side(a, Bool.and(b, Bool.and(c, cellsInRange(rest, count, fuel))), all)
      +cd = Lemma.and_true_right_side(b, Bool.and(c, cellsInRange(rest, count, fuel)), bcd)
      Lemma.and_true_intro(a, Bool.and(b, Bool.and(c, cellsInRange(List.append(&2, Grammar.Cell, rest, ys), count, fuel))), Lemma.and_true_left(a, Bool.and(b, Bool.and(c, cellsInRange(rest, count, fuel))), all),
        Lemma.and_true_intro(b, Bool.and(c, cellsInRange(List.append(&2, Grammar.Cell, rest, ys), count, fuel)), Lemma.and_true_left(b, Bool.and(c, cellsInRange(rest, count, fuel)), bcd),
          Lemma.and_true_intro(c, cellsInRange(List.append(&2, Grammar.Cell, rest, ys), count, fuel), Lemma.and_true_left(c, cellsInRange(rest, count, fuel), cd),
            range_append(rest, ys, count, fuel, Lemma.and_true_right_side(c, cellsInRange(rest, count, fuel), cd), second))))


law range_weaken:
  for table: +List<Grammar.Cell>
  for +count: Nat
  for +fuel: Nat
  for e: {cellsInRange(table, count, fuel) == True{} : Bool}
  {cellsInRange(table, count, 1n+fuel) == True{} : Bool}

def range_weaken(table, count, fuel, e):
  match table:
    case Nil{}:
      {==}
    case Con{Grammar.Cell{+start, +length, nts}, +rest}:
      +all = e
      +a = Nat.is_lt(start, count)
      +b = Nat.is_le(1n, length)
      +bcd = Lemma.and_true_right_side(a, Bool.and(b, Bool.and(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel))), all)
      +cd = Lemma.and_true_right_side(b, Bool.and(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel)), bcd)
      Lemma.and_true_intro(a, Bool.and(b, Bool.and(Nat.is_le(length, 1n+fuel), cellsInRange(rest, count, 1n+fuel))), Lemma.and_true_left(a, Bool.and(b, Bool.and(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel))), all),
        Lemma.and_true_intro(b, Bool.and(Nat.is_le(length, 1n+fuel), cellsInRange(rest, count, 1n+fuel)), Lemma.and_true_left(b, Bool.and(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel)), bcd),
          Lemma.and_true_intro(Nat.is_le(length, 1n+fuel), cellsInRange(rest, count, 1n+fuel), Lemma.le_succ_right(length, fuel, Lemma.and_true_left(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel), cd)),
            range_weaken(rest, count, fuel, Lemma.and_true_right_side(Nat.is_le(length, fuel), cellsInRange(rest, count, fuel), cd)))))


law row_in_range:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +count: Nat
  for +shorter: Nat
  for remaining: Nat
  for +le: {Nat.is_le(remaining, count) == True{} : Bool}
  {cellsInRange(Grammar.row(grammar, inputTokens, table, 1n+shorter, remaining), count, 1n+shorter) == True{} : Bool}

def row_in_range(grammar, inputTokens, table, count, shorter, remaining, le):
  match remaining:
    case 0n:
      {==}
    case 1n+(+start):
      +later = cellsInRange(Grammar.row(grammar, inputTokens, table, 1n+shorter, start), count, 1n+shorter)
      Lemma.and_true_intro(Nat.is_lt(start, count), Bool.and(Nat.is_le(1n, 1n+shorter), Bool.and(Nat.is_le(1n+shorter, 1n+shorter), later)), Lemma.lt_of_succ_le(start, count, le),
        Lemma.and_true_intro(Nat.is_le(1n, 1n+shorter), Bool.and(Nat.is_le(1n+shorter, 1n+shorter), later), Lemma.zero_le(shorter),
          Lemma.and_true_intro(Nat.is_le(1n+shorter, 1n+shorter), later, Lemma.le_refl(shorter),
            row_in_range(grammar, inputTokens, table, count, shorter, start, Lemma.le_of_succ_le(start, count, le)))))


# Every cell of the table starts inside the input and has a length from 1 to fuel.
law table_in_range:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +count: Nat
  for fuel: Nat
  {cellsInRange(Grammar.buildTable(grammar, inputTokens, count, fuel), count, fuel) == True{} : Bool}

def table_in_range(grammar, inputTokens, count, fuel):
  match fuel:
    case 0n:
      {==}
    case 1n+(+shorter):
      +shorterTable = Grammar.buildTable(grammar, inputTokens, count, shorter)
      range_append(
        Grammar.row(grammar, inputTokens, shorterTable, 1n+shorter, count), shorterTable, count, 1n+shorter,
        row_in_range(grammar, inputTokens, shorterTable, count, shorter, count, Lemma.le_refl(count)),
        range_weaken(shorterTable, count, shorter, table_in_range(grammar, inputTokens, count, shorter)))


def Bounds(+s: Nat, +l: Nat, +count: Nat, +fuel: Nat) -> Type:
  {Nat.is_lt(s, count) == True{} : Bool} & {Nat.is_le(1n, l) == True{} : Bool} & {Nat.is_le(l, fuel) == True{} : Bool}


law bounds_pick:
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +count: Nat
  for +fuel: Nat
  for +start: Nat
  for +length: Nat
  for -nts: +List<Nat>
  for -later: +List<Nat>
  for found: Bool
  for +foundEq: {Bool.and(Nat.is_eq(length, l), Nat.is_eq(start, s)) == found : Bool}
  for here: Bounds(start, length, count, fuel)
  for hit: {Grammar.natMember(a, Grammar.pickCell(found, nts, later)) == True{} : Bool}
  for searchLater: {Grammar.natMember(a, later) == True{} : Bool} -> Bounds(s, l, count, fuel)
  Bounds(s, l, count, fuel)

def bounds_pick(a, s, l, count, fuel, start, length, nts, later, found, foundEq, here, hit, searchLater):
  match found:
    case False{}:
      searchLater(hit)
    case True{}:
      sameLength = Lemma.nat_eq_sound(length, l, Lemma.and_true_left(Nat.is_eq(length, l), Nat.is_eq(start, s), foundEq))
      sameStart = Lemma.nat_eq_sound(start, s, Lemma.and_true_right_side(Nat.is_eq(length, l), Nat.is_eq(start, s), foundEq))
      %sameStart : Bounds(_, l, count, fuel)
      %sameLength : Bounds(start, _, count, fuel)
      here


# A nonterminal found by a lookup comes from a cell, so the span is in range.
law lookup_bounds:
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for +count: Nat
  for +fuel: Nat
  for table: +List<Grammar.Cell>
  for range: {cellsInRange(table, count, fuel) == True{} : Bool}
  for hit: {Grammar.natMember(a, Grammar.lookup(table, s, l)) == True{} : Bool}
  Bounds(s, l, count, fuel)

def lookup_bounds(a, s, l, count, fuel, table, range, hit):
  match table:
    case Nil{}:
      Empty.absurd(Bounds(s, l, count, fuel), Lemma.false_is_not_true(hit))
    case Con{Grammar.Cell{+start, +length, +nts}, +rest}:
      +all = range
      +x = Nat.is_lt(start, count)
      +y = Nat.is_le(1n, length)
      +z = Nat.is_le(length, fuel)
      +yzr = Lemma.and_true_right_side(x, Bool.and(y, Bool.and(z, cellsInRange(rest, count, fuel))), all)
      +zr = Lemma.and_true_right_side(y, Bool.and(z, cellsInRange(rest, count, fuel)), yzr)
      here = {(Lemma.and_true_left(x, Bool.and(y, Bool.and(z, cellsInRange(rest, count, fuel))), all), (Lemma.and_true_left(y, Bool.and(z, cellsInRange(rest, count, fuel)), yzr), Lemma.and_true_left(z, cellsInRange(rest, count, fuel), zr))) : Bounds(start, length, count, fuel)}
      +restRange = Lemma.and_true_right_side(z, cellsInRange(rest, count, fuel), zr)
      bounds_pick(a, s, l, count, fuel, start, length, nts, Grammar.lookup(rest, s, l), Bool.and(Nat.is_eq(length, l), Nat.is_eq(start, s)), {==}, here, hit, laterHit => lookup_bounds(a, s, l, count, fuel, rest, restRange, laterHit))


law widen_member:
  for +x: Nat
  for +y: Nat
  for +rest: +List<Nat>
  for -ys: +List<Nat>
  for found: Either<{Grammar.natMember(x, rest) == True{} : Bool}, {Grammar.natMember(x, ys) == True{} : Bool}>
  Either<{Grammar.natMember(x, y <> rest) == True{} : Bool}, {Grammar.natMember(x, ys) == True{} : Bool}>

def widen_member(x, y, rest, ys, found):
  match found:
    case Inl{inRest}:
      Inl{Lemma.or_true_right_intro(Nat.is_eq(x, y), Grammar.natMember(x, rest), inRest)}
    case Inr{inYs}:
      Inr{inYs}


law cases_after_head:
  for +x: Nat
  for +y: Nat
  for +rest: +List<Nat>
  for -ys: +List<Nat>
  for cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Grammar.natMember(x, List.append(&2, Nat, rest, ys)) == True{} : Bool}>
  for searchRest: {Grammar.natMember(x, List.append(&2, Nat, rest, ys)) == True{} : Bool} -> Either<{Grammar.natMember(x, rest) == True{} : Bool}, {Grammar.natMember(x, ys) == True{} : Bool}>
  Either<{Grammar.natMember(x, y <> rest) == True{} : Bool}, {Grammar.natMember(x, ys) == True{} : Bool}>

def cases_after_head(x, y, rest, ys, cases, searchRest):
  match cases:
    case Inl{isY}:
      Inl{Lemma.or_true_left_intro(Nat.is_eq(x, y), Grammar.natMember(x, rest), isY)}
    case Inr{inRest}:
      widen_member(x, y, rest, ys, searchRest(inRest))


law nat_member_append_cases:
  for +x: Nat
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for e: {Grammar.natMember(x, List.append(&2, Nat, xs, ys)) == True{} : Bool}
  Either<{Grammar.natMember(x, xs) == True{} : Bool}, {Grammar.natMember(x, ys) == True{} : Bool}>

def nat_member_append_cases(x, xs, ys, e):
  match xs:
    case Nil{}:
      Inr{e}
    case Con{+y, +rest}:
      cases_after_head(x, y, rest, ys, Lemma.or_true_cases(Nat.is_eq(x, y), Grammar.natMember(x, List.append(&2, Nat, rest, ys)), e), inRest => nat_member_append_cases(x, rest, ys, inRest))


# ---- Finding the production behind a cell entry ----

def TermFound(+grammar: +List<Types.Production>, +a: Nat, +kind: Nat) -> Type:
  &q: Nat -> {Types.lhsIs(grammar, q, a) == True{} : Bool} & {Types.rhsOf(grammar, q) == [Types.Terminal{kind}] : +List<Types.Symbol>}


law move_lhs:
  for -grammar: +List<Types.Production>
  for -o: Nat
  for -a: Nat
  for -lhs: Nat
  for e: {a == lhs : Nat}
  for lhsOk: {Types.lhsIs(grammar, o, lhs) == True{} : Bool}
  {Types.lhsIs(grammar, o, a) == True{} : Bool}

def move_lhs(grammar, o, a, lhs, e, lhsOk):
  %Equal.sym(Nat, a, lhs, e) : {Types.lhsIs(grammar, o, _) == True{} : Bool}
  lhsOk


law term_found_here:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +kind: Nat
  for +lhs: Nat
  for +k: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> others : +List<Types.Production>}
  for kIsKind: {k == kind : Nat}
  for cases: Either<{Nat.is_eq(a, lhs) == True{} : Bool}, {Grammar.natMember(a, Grammar.terminalNonterminals(others, kind)) == True{} : Bool}>
  for searchOthers: {Grammar.natMember(a, Grammar.terminalNonterminals(others, kind)) == True{} : Bool} -> TermFound(grammar, a, kind)
  TermFound(grammar, a, kind)

def term_found_here(grammar, a, kind, lhs, k, others, o, tail, kIsKind, cases, searchOthers):
  match cases:
    case Inl{isLhs}:
      lhsOk = lhs_at(grammar, o, lhs, [Types.Terminal{k}], others, tail)
      +aIsLhs = Lemma.nat_eq_sound(a, lhs, isLhs)
      rhsOk = Equal.trans(+List<Types.Symbol>, Types.rhsOf(grammar, o), [Types.Terminal{k}], [Types.Terminal{kind}], rhs_at(grammar, o, lhs, [Types.Terminal{k}], others, tail), Equal.cong(Nat, +List<Types.Symbol>, n => [Types.Terminal{n}], k, kind, kIsKind))
      (o, (move_lhs(grammar, o, a, lhs, aIsLhs, lhsOk), rhsOk))
    case Inr{inOthers}:
      searchOthers(inOthers)


law term_found_keep:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +kind: Nat
  for +lhs: Nat
  for +k: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> others : +List<Types.Production>}
  for keep: Bool
  for keptEq: {Nat.is_eq(k, kind) == keep : Bool}
  for hit: {Grammar.natMember(a, Grammar.keepNat(keep, lhs, Grammar.terminalNonterminals(others, kind))) == True{} : Bool}
  for searchOthers: {Grammar.natMember(a, Grammar.terminalNonterminals(others, kind)) == True{} : Bool} -> TermFound(grammar, a, kind)
  TermFound(grammar, a, kind)

def term_found_keep(grammar, a, kind, lhs, k, others, o, tail, keep, keptEq, hit, searchOthers):
  match keep:
    case False{}:
      searchOthers(hit)
    case True{}:
      term_found_here(grammar, a, kind, lhs, k, others, o, tail, Lemma.nat_eq_sound(k, kind, keptEq), Lemma.or_true_cases(Nat.is_eq(a, lhs), Grammar.natMember(a, Grammar.terminalNonterminals(others, kind)), hit), searchOthers)


# If a is among the terminal nonterminals for kind, some production a = "kind" exists.
law terminal_nts_find:
  for +grammar: +List<Types.Production>
  for +kind: Nat
  for +a: Nat
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  for hit: {Grammar.natMember(a, Grammar.terminalNonterminals(rest, kind)) == True{} : Bool}
  TermFound(grammar, a, kind)

def terminal_nts_find(grammar, kind, a, rest, o, tail, hit):
  match rest:
    case Nil{}:
      Empty.absurd(TermFound(grammar, a, kind), Lemma.false_is_not_true(hit))
    case Con{Types.Production{+lhs, [Types.Terminal{+k}]}, +others}:
      term_found_keep(grammar, a, kind, lhs, k, others, o, tail, Nat.is_eq(k, kind), {==}, hit, inOthers => terminal_nts_find(grammar, kind, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Terminal{k}]}, others, tail), inOthers))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      terminal_nts_find(grammar, kind, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Terminal{+k}, Con{+second, +more}}}, +others}:
      terminal_nts_find(grammar, kind, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{k} <> second <> more}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+first}, +more}}, +others}:
      terminal_nts_find(grammar, kind, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{first} <> more}, others, tail), hit)


def BinFound(+grammar: +List<Types.Production>, +a: Nat, +lefts: +List<Nat>, +rights: +List<Nat>) -> Type:
  &q: Nat -> &b: Nat -> &c: Nat -> {Types.lhsIs(grammar, q, a) == True{} : Bool} & {Types.rhsOf(grammar, q) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>} & {Grammar.natMember(b, lefts) == True{} : Bool} & {Grammar.natMember(c, rights) == True{} : Bool}


law bin_found_here:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +lhs: Nat
  for +b: Nat
  for +c: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]} <> others : +List<Types.Production>}
  for +both: {Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)) == True{} : Bool}
  for cases: Either<{Nat.is_eq(a, lhs) == True{} : Bool}, {Grammar.natMember(a, Grammar.binaryNonterminals(others, lefts, rights)) == True{} : Bool}>
  for searchOthers: {Grammar.natMember(a, Grammar.binaryNonterminals(others, lefts, rights)) == True{} : Bool} -> BinFound(grammar, a, lefts, rights)
  BinFound(grammar, a, lefts, rights)

def bin_found_here(grammar, a, lefts, rights, lhs, b, c, others, o, tail, both, cases, searchOthers):
  match cases:
    case Inl{isLhs}:
      lhsOk = move_lhs(grammar, o, a, lhs, Lemma.nat_eq_sound(a, lhs, isLhs), lhs_at(grammar, o, lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}], others, tail))
      (o, (b, (c, (lhsOk, (rhs_at(grammar, o, lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}], others, tail), (Lemma.and_true_left(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), both), Lemma.and_true_right_side(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), both)))))))
    case Inr{inOthers}:
      searchOthers(inOthers)


law bin_found_keep:
  for +grammar: +List<Types.Production>
  for +a: Nat
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +lhs: Nat
  for +b: Nat
  for +c: Nat
  for +others: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]} <> others : +List<Types.Production>}
  for keep: Bool
  for +keptEq: {Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)) == keep : Bool}
  for hit: {Grammar.natMember(a, Grammar.keepNat(keep, lhs, Grammar.binaryNonterminals(others, lefts, rights))) == True{} : Bool}
  for searchOthers: {Grammar.natMember(a, Grammar.binaryNonterminals(others, lefts, rights)) == True{} : Bool} -> BinFound(grammar, a, lefts, rights)
  BinFound(grammar, a, lefts, rights)

def bin_found_keep(grammar, a, lefts, rights, lhs, b, c, others, o, tail, keep, keptEq, hit, searchOthers):
  match keep:
    case False{}:
      searchOthers(hit)
    case True{}:
      bin_found_here(grammar, a, lefts, rights, lhs, b, c, others, o, tail, keptEq, Lemma.or_true_cases(Nat.is_eq(a, lhs), Grammar.natMember(a, Grammar.binaryNonterminals(others, lefts, rights)), hit), searchOthers)


# If a is among the binary nonterminals, some production a = b c has b in lefts and c in rights.
law binary_nts_find:
  for +grammar: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +a: Nat
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  for hit: {Grammar.natMember(a, Grammar.binaryNonterminals(rest, lefts, rights)) == True{} : Bool}
  BinFound(grammar, a, lefts, rights)

def binary_nts_find(grammar, lefts, rights, a, rest, o, tail, hit):
  match rest:
    case Nil{}:
      Empty.absurd(BinFound(grammar, a, lefts, rights), Lemma.false_is_not_true(hit))
    case Con{Types.Production{+lhs, [Types.Nonterminal{+b}, Types.Nonterminal{+c}]}, +others}:
      bin_found_keep(grammar, a, lefts, rights, lhs, b, c, others, o, tail, Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), {==}, hit, inOthers => binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, others, tail), inOthers))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Terminal{+t}, +more}}, +others}:
      binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{t} <> more}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Nil{}}}, +others}:
      binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}]}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Terminal{+t}, +more}}}, +others}:
      binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Terminal{t} <> more}, others, tail), hit)
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Con{+x, +more}}}}, +others}:
      binary_nts_find(grammar, lefts, rights, a, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Nonterminal{c} <> x <> more}, others, tail), hit)


# A split that put a into the cell: left part 1 + kp, right part 1 + m.
def SplitFound(+grammar: +List<Types.Production>, +table: +List<Grammar.Cell>, +s: Nat, +a: Nat, +left: Nat, +r: Nat) -> Type:
  &kp: Nat -> &m: Nat -> {Nat.is_le(1n+kp, left) == True{} : Bool} & {Nat.add(1n+kp, 1n+m) == Nat.add(left, 1n+r) : Nat} & {Grammar.natMember(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), 1n+m))) == True{} : Bool}


law split_found_later:
  for -grammar: +List<Types.Production>
  for -table: +List<Grammar.Cell>
  for -s: Nat
  for -a: Nat
  for +smaller: Nat
  for +r: Nat
  for found: SplitFound(grammar, table, s, a, smaller, 1n+r)
  SplitFound(grammar, table, s, a, 1n+smaller, r)

def split_found_later(grammar, table, s, a, smaller, r, found):
  match found:
    case (+kp, (+m, (kle, (sum, hit)))):
      (kp, (m, (Lemma.le_succ_right(1n+kp, smaller, kle), (Equal.trans(Nat, Nat.add(1n+kp, 1n+m), Nat.add(smaller, 1n+1n+r), 1n+Nat.add(smaller, 1n+r), sum, Lemma.add_succ_right(smaller, 1n+r)), hit))))


law split_found_pick:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +a: Nat
  for +smaller: Nat
  for +r: Nat
  for cases: Either<{Grammar.natMember(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), 1n+r))) == True{} : Bool}, {Grammar.natMember(a, Grammar.splitNonterminals(grammar, table, s, smaller, 1n+1n+r)) == True{} : Bool}>
  for searchLater: {Grammar.natMember(a, Grammar.splitNonterminals(grammar, table, s, smaller, 1n+1n+r)) == True{} : Bool} -> SplitFound(grammar, table, s, a, smaller, 1n+r)
  SplitFound(grammar, table, s, a, 1n+smaller, r)

def split_found_pick(grammar, table, s, a, smaller, r, cases, searchLater):
  match cases:
    case Inl{here}:
      (smaller, (r, (Lemma.le_refl(smaller), ({==}, here))))
    case Inr{later}:
      split_found_later(grammar, table, s, a, smaller, r, searchLater(later))


law split_find:
  for +grammar: +List<Types.Production>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for +a: Nat
  for left: Nat
  for +r: Nat
  for hit: {Grammar.natMember(a, Grammar.splitNonterminals(grammar, table, s, left, 1n+r)) == True{} : Bool}
  SplitFound(grammar, table, s, a, left, r)

def split_find(grammar, table, s, a, left, r, hit):
  match left:
    case 0n:
      Empty.absurd(SplitFound(grammar, table, s, a, 0n, r), Lemma.false_is_not_true(hit))
    case 1n+(+smaller):
      split_found_pick(
        grammar, table, s, a, smaller, r,
        nat_member_append_cases(a, Grammar.binaryNonterminals(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), 1n+r)), Grammar.splitNonterminals(grammar, table, s, smaller, 1n+1n+r), hit),
        later => split_find(grammar, table, s, a, smaller, 1n+r, later))


# ---- Building embedded trees ----

def CellTree(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +a: Nat, +s: Nat, +l: Nat) -> Type:
  &t: Types.Tree -> {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool} & {embedded(t, StepSet(grammar, inputTokens), s) == True{} : Bool} & {GrammarLaws.leaves([t]) == Lemma.slice(inputTokens, s, l) : +List<Nat>} & {List.length(&2, Nat, GrammarLaws.leaves([t])) == l : Nat}


law leaf_node_fits:
  for +grammar: +List<Types.Production>
  for +q: Nat
  for +a: Nat
  for +kind: Nat
  for lhsOk: {Types.lhsIs(grammar, q, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, q) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.fits([Types.Node{q, [Types.Leaf{kind}]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}

def leaf_node_fits(grammar, q, a, kind, lhsOk, rhsOk):
  +childFit = GrammarLaws.fits([Types.Leaf{kind}], grammar, Types.rhsOf(grammar, q))
  Lemma.and_true_intro(Types.lhsIs(grammar, q, a), Bool.and(childFit, True{}), lhsOk,
    Lemma.and_true_intro(childFit, True{}, fits_at([Types.Leaf{kind}], grammar, [Types.Terminal{kind}], Types.rhsOf(grammar, q), Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, q), [Types.Terminal{kind}], rhsOk), Lemma.and_true_intro(Nat.is_eq(kind, kind), True{}, Lemma.nat_eq_refl(kind), {==})), {==}))


law pair_node_fits:
  for +grammar: +List<Types.Production>
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for lhsOk: {Types.lhsIs(grammar, q, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, q) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for f1: {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for f2: {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  {GrammarLaws.fits([Types.Node{q, [first, second]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}

def pair_node_fits(grammar, q, a, b, c, first, second, lhsOk, rhsOk, f1, f2):
  +childFit = GrammarLaws.fits([first, second], grammar, Types.rhsOf(grammar, q))
  pairFit = fits_cons_intro(first, [second], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, f1, fits_cons_intro(second, [], Types.Nonterminal{c}, [], grammar, f2, {==}))
  Lemma.and_true_intro(Types.lhsIs(grammar, q, a), Bool.and(childFit, True{}), lhsOk,
    Lemma.and_true_intro(childFit, True{}, fits_at([first, second], grammar, [Types.Nonterminal{b}, Types.Nonterminal{c}], Types.rhsOf(grammar, q), Equal.sym(+List<Types.Symbol>, Types.rhsOf(grammar, q), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk), pairFit), {==}))


# A node a = "kind" over the token at s, with its step in the set.
law leaf_tree:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +kind: Nat
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for found: TermFound(grammar, a, kind)
  CellTree(grammar, inputTokens, a, s, 1n)

def leaf_tree(grammar, inputTokens, a, s, kind, lt, tokenEq, found):
  match found:
    case (+q, (lhsOk, +rhsOk)):
      +count = List.length(&2, Nat, inputTokens)
      +table = Table(grammar, inputTokens)
      +step = {Types.Bsr{Types.Slot{q, 1n}, s, s, 1n+s} : Types.Bsr}
      inSet = all_member(grammar, inputTokens, table, count, 0n, step, count, Lemma.lt_pos(s, count, lt), row_member(grammar, inputTokens, table, 1n, s, step, count, lt, token_member(grammar, inputTokens, s, q, kind, tokenEq, rhsOk)))
      (Types.Node{q, [Types.Leaf{kind}]}, (leaf_node_fits(grammar, q, a, kind, lhsOk, rhsOk), (Lemma.and_true_intro(GrammarLaws.bsrMember(step, StepSet(grammar, inputTokens)), True{}, inSet, {==}), (Equal.sym(+List<Nat>, Lemma.slice(inputTokens, s, 1n), [kind], Lemma.get_slice(inputTokens, s, kind, tokenEq)), {==}))))


# A node q = b c over two embedded trees, with its step in the set.
law pair_tree_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +q: Nat
  for +b: Nat
  for +c: Nat
  for +kp: Nat
  for +m: Nat
  for +total: Nat
  for lhsOk: {Types.lhsIs(grammar, q, a) == True{} : Bool}
  for +rhsOk: {Types.rhsOf(grammar, q) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +sum: {Nat.add(1n+kp, 1n+m) == total : Nat}
  for +stepIn: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, 2n}, s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, 1n+m))}, StepSet(grammar, inputTokens)) == True{} : Bool}
  for left: CellTree(grammar, inputTokens, b, s, 1n+kp)
  for right: CellTree(grammar, inputTokens, c, Nat.add(s, 1n+kp), 1n+m)
  CellTree(grammar, inputTokens, a, s, total)

def pair_tree_parts(grammar, inputTokens, a, s, q, b, c, kp, m, total, lhsOk, rhsOk, sum, stepIn, left, right):
  match left:
    case (t10, (f10, (e1, (sp1, len10)))):
      match right:
        case (t20, (f20, (e2, (sp2, len20)))):
          +t1 = {t10 : Types.Tree}
          +t2 = {t20 : Types.Tree}
          +f1 = {f10 : {GrammarLaws.fits([t1], grammar, [Types.Nonterminal{b}]) == True{} : Bool}}
          +f2 = {f20 : {GrammarLaws.fits([t2], grammar, [Types.Nonterminal{c}]) == True{} : Bool}}
          +len1 = {len10 : {List.length(&2, Nat, GrammarLaws.leaves([t1])) == 1n+kp : Nat}}
          +len2 = {len20 : {List.length(&2, Nat, GrammarLaws.leaves([t2])) == 1n+m : Nat}}
          +set = StepSet(grammar, inputTokens)
          +w1 = GrammarLaws.leaves([t1])
          +w2 = GrammarLaws.leaves([t2])
          +joined = node_leaves(q, [t1, t2], List.append(&2, Nat, w1, w2), pair_leaves(t1, t2, w1, w2, {==}, {==}))
          +node = GrammarLaws.leaves([Types.Node{q, [t1, t2]}])
          emb = embed_two(t1, t2, grammar, b, c, set, q, s, f1, f2,
            move_pair_member(set, q, s, List.length(&2, Nat, w1), 1n+kp, List.length(&2, Nat, w2), 1n+m, len1, len2, stepIn),
            e1,
            move_embedded(set, t2, s, List.length(&2, Nat, w1), 1n+kp, len1, e2))
          spelled = Equal.trans(+List<Nat>, node, List.append(&2, Nat, w1, w2), Lemma.slice(inputTokens, s, total), joined,
            Equal.trans(+List<Nat>, List.append(&2, Nat, w1, w2), List.append(&2, Nat, Lemma.slice(inputTokens, s, 1n+kp), Lemma.slice(inputTokens, Nat.add(s, 1n+kp), 1n+m)), Lemma.slice(inputTokens, s, total),
              Lemma.append_congr(w1, w2, Lemma.slice(inputTokens, s, 1n+kp), Lemma.slice(inputTokens, Nat.add(s, 1n+kp), 1n+m), sp1, sp2),
              Equal.trans(+List<Nat>, List.append(&2, Nat, Lemma.slice(inputTokens, s, 1n+kp), Lemma.slice(inputTokens, Nat.add(s, 1n+kp), 1n+m)), Lemma.slice(inputTokens, s, Nat.add(1n+kp, 1n+m)), Lemma.slice(inputTokens, s, total),
                Lemma.slice_split(inputTokens, s, 1n+kp, 1n+m),
                Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), Nat.add(1n+kp, 1n+m), total, sum))))
          long = Equal.trans(Nat, List.length(&2, Nat, node), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), total, Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), node, List.append(&2, Nat, w1, w2), joined),
            Equal.trans(Nat, List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), total, Lemma.length_append(w1, w2),
              Equal.trans(Nat, Nat.add(List.length(&2, Nat, w1), List.length(&2, Nat, w2)), Nat.add(1n+kp, 1n+m), total, Lemma.add_congr(List.length(&2, Nat, w1), 1n+kp, List.length(&2, Nat, w2), 1n+m, len1, len2), sum)))
          (Types.Node{q, [t1, t2]}, (pair_node_fits(grammar, q, a, b, c, t1, t2, lhsOk, rhsOk, f1, f2), (emb, (spelled, long))))


# ---- Every cell entry has an embedded tree ----

def FullT(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +fuel: Nat) -> +List<Grammar.Cell>:
  Grammar.buildTable(grammar, inputTokens, List.length(&2, Nat, inputTokens), fuel)


def CellIH(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +f: Nat) -> Type:
  @b: Nat -> @s: Nat -> @l: Nat -> {Nat.is_le(l, f) == True{} : Bool} -> {Grammar.natMember(b, Grammar.lookup(Table(grammar, inputTokens), s, l)) == True{} : Bool} -> CellTree(grammar, inputTokens, b, s, l)


def InFull(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +b: Nat, +s: Nat, +kq: Nat, +p: Nat) -> Type:
  {Grammar.natMember(b, Grammar.lookup(Table(grammar, inputTokens), s, 1n+kq)) == True{} : Bool} & {Nat.is_le(1n+kq, 1n+p) == True{} : Bool}


law move_hit:
  for -a: Nat
  for -x: +List<Nat>
  for -y: +List<Nat>
  for e: {x == y : +List<Nat>}
  for hit: {Grammar.natMember(a, x) == True{} : Bool}
  {Grammar.natMember(a, y) == True{} : Bool}

def move_hit(a, x, y, e, hit):
  %e : {Grammar.natMember(a, _) == True{} : Bool}
  hit


law to_full_bounds:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +b: Nat
  for +s: Nat
  for +kq: Nat
  for +p: Nat
  for +leN: {Nat.is_le(1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for inSmaller: {Grammar.natMember(b, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), s, 1n+kq)) == True{} : Bool}
  for bounds: Bounds(s, 1n+kq, List.length(&2, Nat, inputTokens), 1n+p)
  InFull(grammar, inputTokens, b, s, kq, p)

def to_full_bounds(grammar, inputTokens, b, s, kq, p, leN, inSmaller, bounds):
  match bounds:
    case (lt0, (pos, le0)):
      +lt = {lt0 : {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}}
      +le = {le0 : {Nat.is_le(1n+kq, 1n+p) == True{} : Bool}}
      +count = List.length(&2, Nat, inputTokens)
      +cell = Grammar.cellNonterminals(grammar, inputTokens, FullT(grammar, inputTokens, kq), s, 1n+kq)
      inCell = move_hit(b, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), s, 1n+kq), cell, lookup_built(grammar, inputTokens, s, kq, 1n+p, le, lt), inSmaller)
      full = lookup_built(grammar, inputTokens, s, kq, count, Lemma.le_trans(1n+kq, 1n+p, count, le, leN), lt)
      (move_hit(b, cell, Grammar.lookup(FullT(grammar, inputTokens, count), s, 1n+kq), Equal.sym(+List<Nat>, Grammar.lookup(FullT(grammar, inputTokens, count), s, 1n+kq), cell, full), inCell), le)


# An entry of a smaller table is an entry of the full table for the same span.
law lookup_to_full:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +b: Nat
  for +s: Nat
  for +kq: Nat
  for +p: Nat
  for +leN: {Nat.is_le(1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +inSmaller: {Grammar.natMember(b, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), s, 1n+kq)) == True{} : Bool}
  InFull(grammar, inputTokens, b, s, kq, p)

def lookup_to_full(grammar, inputTokens, b, s, kq, p, leN, inSmaller):
  +count = List.length(&2, Nat, inputTokens)
  to_full_bounds(grammar, inputTokens, b, s, kq, p, leN, inSmaller, lookup_bounds(b, s, 1n+kq, count, 1n+p, FullT(grammar, inputTokens, 1n+p), table_in_range(grammar, inputTokens, count, 1n+p), inSmaller))


law split_cell_full:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +p: Nat
  for +f: Nat
  for +kp: Nat
  for +m: Nat
  for +q: Nat
  for +b: Nat
  for +c: Nat
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leN: {Nat.is_le(1n+1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leF: {Nat.is_le(1n+p, f) == True{} : Bool}
  for +kle: {Nat.is_le(1n+kp, 1n+p) == True{} : Bool}
  for +sum: {Nat.add(1n+kp, 1n+m) == Nat.add(1n+p, 1n) : Nat}
  for lhsOk: {Types.lhsIs(grammar, q, a) == True{} : Bool}
  for +rhsOk: {Types.rhsOf(grammar, q) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for fullL: InFull(grammar, inputTokens, b, s, kp, p)
  for fullR: InFull(grammar, inputTokens, c, Nat.add(s, 1n+kp), m, p)
  for ihL: CellIH(grammar, inputTokens, f)
  for ihR: CellIH(grammar, inputTokens, f)
  CellTree(grammar, inputTokens, a, s, 1n+1n+p)

def split_cell_full(grammar, inputTokens, a, s, p, f, kp, m, q, b, c, lt, leN, leF, kle, sum, lhsOk, rhsOk, fullL, fullR, ihL, ihR):
  match fullL:
    case (inL0, leL):
      match fullR:
        case (inR0, leR):
          +table = Table(grammar, inputTokens)
          +count = List.length(&2, Nat, inputTokens)
          +inL = {inL0 : {Grammar.natMember(b, Grammar.lookup(table, s, 1n+kp)) == True{} : Bool}}
          +inR = {inR0 : {Grammar.natMember(c, Grammar.lookup(table, Nat.add(s, 1n+kp), 1n+m)) == True{} : Bool}}
          left = ihL(b, s, 1n+kp, Lemma.le_trans(1n+kp, 1n+p, f, leL, leF), inL)
          right = ihR(c, Nat.add(s, 1n+kp), 1n+m, Lemma.le_trans(1n+m, 1n+p, f, leR, leF), inR)
          +element = {Types.Bsr{Types.Slot{q, 2n}, s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, 1n+m))} : Types.Bsr}
          hit = binary_steps_member(grammar, Grammar.lookup(table, s, 1n+kp), Grammar.lookup(table, Nat.add(s, 1n+kp), 1n+m), s, Nat.add(s, 1n+kp), Nat.add(s, Nat.add(1n+kp, 1n+m)), 0n, q, b, c, rhsOk, inL, inR)
          inSplit = split_steps_member(grammar, table, s, element, kp, 1n+m, 1n+p, 1n, kle, sum, hit)
          stepIn = all_member(grammar, inputTokens, table, count, 1n+p, element, count, leN, row_member(grammar, inputTokens, table, 1n+1n+p, s, element, count, lt, inSplit))
          total = Equal.trans(Nat, Nat.add(1n+kp, 1n+m), Nat.add(1n+p, 1n), 1n+1n+p, sum, Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n), 1n+p, Lemma.add_one_right(p)))
          pair_tree_parts(grammar, inputTokens, a, s, q, b, c, kp, m, 1n+1n+p, lhsOk, rhsOk, total, stepIn, left, right)


law split_cell_bin:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +p: Nat
  for +f: Nat
  for +kp: Nat
  for +m: Nat
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leN: {Nat.is_le(1n+1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leF: {Nat.is_le(1n+p, f) == True{} : Bool}
  for kle: {Nat.is_le(1n+kp, 1n+p) == True{} : Bool}
  for sum: {Nat.add(1n+kp, 1n+m) == Nat.add(1n+p, 1n) : Nat}
  for found: BinFound(grammar, a, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), s, 1n+kp), Grammar.lookup(FullT(grammar, inputTokens, 1n+p), Nat.add(s, 1n+kp), 1n+m))
  for ihL: CellIH(grammar, inputTokens, f)
  for ihR: CellIH(grammar, inputTokens, f)
  CellTree(grammar, inputTokens, a, s, 1n+1n+p)

def split_cell_bin(grammar, inputTokens, a, s, p, f, kp, m, lt, leN, leF, kle, sum, found, ihL, ihR):
  match found:
    case (q0, (b0, (c0, (lhsOk, (rhsOk0, (inL0, inR0)))))):
      +q = {q0 : Nat}
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      +rhsOk = {rhsOk0 : {Types.rhsOf(grammar, q) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}}
      +inL = {inL0 : {Grammar.natMember(b, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), s, 1n+kp)) == True{} : Bool}}
      +inR = {inR0 : {Grammar.natMember(c, Grammar.lookup(FullT(grammar, inputTokens, 1n+p), Nat.add(s, 1n+kp), 1n+m)) == True{} : Bool}}
      +leNp = Lemma.le_of_succ_le(1n+p, List.length(&2, Nat, inputTokens), leN)
      split_cell_full(grammar, inputTokens, a, s, p, f, kp, m, q, b, c, lt, leN, leF, kle, sum, lhsOk, rhsOk, lookup_to_full(grammar, inputTokens, b, s, kp, p, leNp, inL), lookup_to_full(grammar, inputTokens, c, Nat.add(s, 1n+kp), m, p, leNp, inR), ihL, ihR)


law split_cell_found:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +p: Nat
  for +f: Nat
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leN: {Nat.is_le(1n+1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for +leF: {Nat.is_le(1n+p, f) == True{} : Bool}
  for found: SplitFound(grammar, FullT(grammar, inputTokens, 1n+p), s, a, 1n+p, 0n)
  for ihL: CellIH(grammar, inputTokens, f)
  for ihR: CellIH(grammar, inputTokens, f)
  CellTree(grammar, inputTokens, a, s, 1n+1n+p)

def split_cell_found(grammar, inputTokens, a, s, p, f, lt, leN, leF, found, ihL, ihR):
  match found:
    case (kp0, (m0, (kle, (sum, hit)))):
      +kp = {kp0 : Nat}
      +m = {m0 : Nat}
      +smaller = FullT(grammar, inputTokens, 1n+p)
      split_cell_bin(grammar, inputTokens, a, s, p, f, kp, m, lt, leN, leF, kle, sum, binary_nts_find(grammar, Grammar.lookup(smaller, s, 1n+kp), Grammar.lookup(smaller, Nat.add(s, 1n+kp), 1n+m), a, grammar, 0n, {==}, hit), ihL, ihR)


law token_cell:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for token: Maybe<&2, Nat>
  for +tokenEq: {List.get(&2, Nat, inputTokens, s) == token : Maybe<&2, Nat>}
  for hit: {Grammar.natMember(a, Grammar.tokenNonterminals(grammar, token)) == True{} : Bool}
  CellTree(grammar, inputTokens, a, s, 1n)

def token_cell(grammar, inputTokens, a, s, lt, token, tokenEq, hit):
  match token:
    case None{}:
      Empty.absurd(CellTree(grammar, inputTokens, a, s, 1n), Lemma.false_is_not_true(hit))
    case Some{+kind}:
      leaf_tree(grammar, inputTokens, a, s, kind, lt, tokenEq, terminal_nts_find(grammar, kind, a, grammar, 0n, {==}, hit))


law span_cell:
  for +f: Nat
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for p: Nat
  for le: {Nat.is_le(1n+p, 1n+f) == True{} : Bool}
  for hit: {Grammar.natMember(a, Grammar.cellNonterminals(grammar, inputTokens, FullT(grammar, inputTokens, p), s, 1n+p)) == True{} : Bool}
  for +lt: {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for leN: {Nat.is_le(1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}
  for ihL: CellIH(grammar, inputTokens, f)
  for ihR: CellIH(grammar, inputTokens, f)
  CellTree(grammar, inputTokens, a, s, 1n+p)

def span_cell(f, grammar, inputTokens, a, s, p, le, hit, lt, leN, ihL, ihR):
  match p:
    case 0n:
      token_cell(grammar, inputTokens, a, s, lt, List.get(&2, Nat, inputTokens, s), {==}, hit)
    case 1n+(+smaller):
      split_cell_found(grammar, inputTokens, a, s, smaller, f, lt, leN, le, split_find(grammar, FullT(grammar, inputTokens, 1n+smaller), s, a, 1n+smaller, 0n, hit), ihL, ihR)


law span_bounds:
  for +f: Nat
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +p: Nat
  for le: {Nat.is_le(1n+p, 1n+f) == True{} : Bool}
  for hit: {Grammar.natMember(a, Grammar.lookup(Table(grammar, inputTokens), s, 1n+p)) == True{} : Bool}
  for bounds: Bounds(s, 1n+p, List.length(&2, Nat, inputTokens), List.length(&2, Nat, inputTokens))
  for ihL: CellIH(grammar, inputTokens, f)
  for ihR: CellIH(grammar, inputTokens, f)
  CellTree(grammar, inputTokens, a, s, 1n+p)

def span_bounds(f, grammar, inputTokens, a, s, p, le, hit, bounds, ihL, ihR):
  match bounds:
    case (lt0, (pos, leN0)):
      +lt = {lt0 : {Nat.is_lt(s, List.length(&2, Nat, inputTokens)) == True{} : Bool}}
      +leN = {leN0 : {Nat.is_le(1n+p, List.length(&2, Nat, inputTokens)) == True{} : Bool}}
      +cell = Grammar.cellNonterminals(grammar, inputTokens, FullT(grammar, inputTokens, p), s, 1n+p)
      span_cell(f, grammar, inputTokens, a, s, p, le, move_hit(a, Grammar.lookup(Table(grammar, inputTokens), s, 1n+p), cell, lookup_built(grammar, inputTokens, s, p, List.length(&2, Nat, inputTokens), leN, lt), hit), lt, leN, ihL, ihR)


law no_cell:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for le: {Nat.is_le(l, 0n) == True{} : Bool}
  for bounds: Bounds(s, l, List.length(&2, Nat, inputTokens), List.length(&2, Nat, inputTokens))
  Empty

def no_cell(grammar, inputTokens, a, s, l, le, bounds):
  match bounds:
    case (lt, (pos, leN)):
      Lemma.false_is_not_true(Lemma.le_trans(1n, l, 0n, pos, le))


# Every entry of a cell of the table has an embedded parse tree for the cell's span.
law cell_support:
  for fuel: Nat
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +s: Nat
  for +l: Nat
  for le: {Nat.is_le(l, fuel) == True{} : Bool}
  for +hit: {Grammar.natMember(a, Grammar.lookup(Table(grammar, inputTokens), s, l)) == True{} : Bool}
  CellTree(grammar, inputTokens, a, s, l)

def cell_support(fuel, grammar, inputTokens, a, s, l, le, hit):
  match fuel l:
    case 0n _:
      +count = List.length(&2, Nat, inputTokens)
      Empty.absurd(CellTree(grammar, inputTokens, a, s, l), no_cell(grammar, inputTokens, a, s, l, le, lookup_bounds(a, s, l, count, count, Table(grammar, inputTokens), table_in_range(grammar, inputTokens, count, count), hit)))
    case 1n+(+f) 0n:
      +count = List.length(&2, Nat, inputTokens)
      Empty.absurd(CellTree(grammar, inputTokens, a, s, 0n), no_cell(grammar, inputTokens, a, s, 0n, {==}, lookup_bounds(a, s, 0n, count, count, Table(grammar, inputTokens), table_in_range(grammar, inputTokens, count, count), hit)))
    case 1n+(+f) 1n+(+p):
      +count = List.length(&2, Nat, inputTokens)
      span_bounds(
        f, grammar, inputTokens, a, s, p, le, hit,
        lookup_bounds(a, s, 1n+p, count, count, Table(grammar, inputTokens), table_in_range(grammar, inputTokens, count, count), hit),
        b1 => s1 => l1 => le1 => h1 => cell_support(f, grammar, inputTokens, b1, s1, l1, le1, h1),
        b2 => s2 => l2 => le2 => h2 => cell_support(f, grammar, inputTokens, b2, s2, l2, le2, h2))


# ---- Support ----

# A cell entry has an embedded tree; the cell's bound comes from the lookup.
law tree_from_bounds:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +b: Nat
  for +s: Nat
  for +l: Nat
  for +hit: {Grammar.natMember(b, Grammar.lookup(Table(grammar, inputTokens), s, l)) == True{} : Bool}
  for bounds: Bounds(s, l, List.length(&2, Nat, inputTokens), List.length(&2, Nat, inputTokens))
  CellTree(grammar, inputTokens, b, s, l)

def tree_from_bounds(grammar, inputTokens, b, s, l, hit, bounds):
  match bounds:
    case (lt, (pos, le)):
      cell_support(List.length(&2, Nat, inputTokens), grammar, inputTokens, b, s, l, le, hit)


law tree_from_hit:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +b: Nat
  for +s: Nat
  for +l: Nat
  for +hit: {Grammar.natMember(b, Grammar.lookup(Table(grammar, inputTokens), s, l)) == True{} : Bool}
  CellTree(grammar, inputTokens, b, s, l)

def tree_from_hit(grammar, inputTokens, b, s, l, hit):
  +count = List.length(&2, Nat, inputTokens)
  tree_from_bounds(grammar, inputTokens, b, s, l, hit, lookup_bounds(b, s, l, count, count, Table(grammar, inputTokens), table_in_range(grammar, inputTokens, count, count), hit))


def Supported(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +a: Nat, +index: Nat, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Type:
  &tree: Types.Tree -> {GrammarLaws.fits([tree], grammar, [Types.Nonterminal{a}]) == True{} : Bool} & {embedded(tree, Grammar.cykSteps(grammar, inputTokens), i) == True{} : Bool} & {rootStep(tree, i) == Types.Bsr{Types.Slot{index, dot}, i, k, j} : Types.Bsr}


def PairCells(+rhs: +List<Types.Symbol>, +table: +List<Grammar.Cell>, +i: Nat, +k: Nat, +j: Nat) -> Type:
  &b: Nat -> &c: Nat -> {rhs == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>} & {Nat.is_lt(i, k) == True{} : Bool} & {Nat.is_lt(k, j) == True{} : Bool} & {Grammar.natMember(b, Grammar.lookup(table, i, Nat.sub(k, i))) == True{} : Bool} & {Grammar.natMember(c, Grammar.lookup(table, k, Nat.sub(j, k))) == True{} : Bool}


law pair_cells_parts:
  for rhs: +List<Types.Symbol>
  for +table: +List<Grammar.Cell>
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for e: {pairInCells(rhs, table, i, k, j) == True{} : Bool}
  PairCells(rhs, table, i, k, j)

def pair_cells_parts(rhs, table, i, k, j, e):
  match rhs:
    case Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Nil{}}}:
      +all = e
      +x = Nat.is_lt(i, k)
      +y = Nat.is_lt(k, j)
      +inB = Grammar.natMember(b, Grammar.lookup(table, i, Nat.sub(k, i)))
      +inC = Grammar.natMember(c, Grammar.lookup(table, k, Nat.sub(j, k)))
      +rest1 = Lemma.and_true_right_side(x, Bool.and(y, Bool.and(inB, inC)), all)
      +rest2 = Lemma.and_true_right_side(y, Bool.and(inB, inC), rest1)
      (b, (c, ({==}, (Lemma.and_true_left(x, Bool.and(y, Bool.and(inB, inC)), all), (Lemma.and_true_left(y, Bool.and(inB, inC), rest1), (Lemma.and_true_left(inB, inC, rest2), Lemma.and_true_right_side(inB, inC, rest2)))))))
    case Nil{}:
      Empty.absurd(PairCells([], table, i, k, j), Lemma.false_is_not_true(e))
    case Con{Types.Terminal{t}, more}:
      Empty.absurd(PairCells(Types.Terminal{t} <> more, table, i, k, j), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Nil{}}:
      Empty.absurd(PairCells([Types.Nonterminal{b}], table, i, k, j), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Con{Types.Terminal{t}, more}}:
      Empty.absurd(PairCells(Types.Nonterminal{b} <> Types.Terminal{t} <> more, table, i, k, j), Lemma.false_is_not_true(e))
    case Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}:
      Empty.absurd(PairCells(Types.Nonterminal{b} <> Types.Nonterminal{c} <> x <> more, table, i, k, j), Lemma.false_is_not_true(e))


law leaf_step_at:
  for -set: +List<Types.Bsr>
  for -index: Nat
  for -i: Nat
  for -k: Nat
  for -j: Nat
  for kIsI: {k == i : Nat}
  for jIs: {j == 1n+i : Nat}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, k, j}, set) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, i, 1n+i}, set) == True{} : Bool}

def leaf_step_at(set, index, i, k, j, kIsI, jIs, inSet):
  %kIsI : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, _, 1n+i}, set) == True{} : Bool}
  %jIs : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, k, _}, set) == True{} : Bool}
  inSet


law leaf_root:
  for -index: Nat
  for +i: Nat
  for -kind: Nat
  for -k: Nat
  for -j: Nat
  for kIsI: {k == i : Nat}
  for jIs: {j == 1n+i : Nat}
  {rootStep(Types.Node{index, [Types.Leaf{kind}]}, i) == Types.Bsr{Types.Slot{index, 1n}, i, k, j} : Types.Bsr}

def leaf_root(index, i, kind, k, j, kIsI, jIs):
  %Equal.sym(Nat, k, i, kIsI) : {rootStep(Types.Node{index, [Types.Leaf{kind}]}, i) == Types.Bsr{Types.Slot{index, 1n}, i, _, j} : Types.Bsr}
  %Equal.sym(Nat, j, 1n+i, jIs) : {rootStep(Types.Node{index, [Types.Leaf{kind}]}, i) == Types.Bsr{Types.Slot{index, 1n}, i, i, _} : Types.Bsr}
  %Lemma.add_one_right(i) : {Types.Bsr{Types.Slot{index, 1n}, i, i, Nat.add(i, 1n)} == Types.Bsr{Types.Slot{index, 1n}, i, i, _} : Types.Bsr}
  {==}


law supported_leaf_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +index: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for +kIsI: {k == i : Nat}
  for +jIs: {j == 1n+i : Nat}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for parts: TokenParts(Types.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, i))
  Supported(grammar, inputTokens, a, index, 1n, i, k, j)

def supported_leaf_parts(grammar, inputTokens, a, index, i, k, j, lhsOk, kIsI, jIs, inSet, parts):
  match parts:
    case (t0, (rhsEq, tokenEq)):
      +t = {t0 : Nat}
      +set = Grammar.cykSteps(grammar, inputTokens)
      +step = {Types.Bsr{Types.Slot{index, 1n}, i, i, 1n+i} : Types.Bsr}
      emb = Lemma.and_true_intro(GrammarLaws.bsrMember(step, set), True{}, leaf_step_at(set, index, i, k, j, kIsI, jIs, inSet), {==})
      (Types.Node{index, [Types.Leaf{t}]}, (leaf_node_fits(grammar, index, a, t, lhsOk, rhsEq), (emb, leaf_root(index, i, t, k, j, kIsI, jIs))))


law supported_leaf:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +index: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 1n}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for from: {stepFrom(grammar, inputTokens, Table(grammar, inputTokens), Types.Bsr{Types.Slot{index, 1n}, i, k, j}) == True{} : Bool}
  Supported(grammar, inputTokens, a, index, 1n, i, k, j)

def supported_leaf(grammar, inputTokens, a, index, i, k, j, lhsOk, inSet, from):
  +tm = tokenMatches(Types.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, i))
  +x = Lemma.or_false_right(Bool.and(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm)), from)
  +y = Lemma.and_true_right_side(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm), x)
  kIsI = Lemma.nat_eq_sound(k, i, Lemma.and_true_left(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm), x))
  jIs = Lemma.nat_eq_sound(j, 1n+i, Lemma.and_true_left(Nat.is_eq(j, 1n+i), tm, y))
  supported_leaf_parts(grammar, inputTokens, a, index, i, k, j, lhsOk, kIsI, jIs, inSet, token_matches_parts(Types.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, i), Lemma.and_true_right_side(Nat.is_eq(j, 1n+i), tm, y)))


law pair_step_at:
  for -set: +List<Types.Bsr>
  for -index: Nat
  for -i: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for -k: Nat
  for -j: Nat
  for eqK: {endOf(first, i) == k : Nat}
  for eqJ: {endOf(second, k) == j : Nat}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, k, j}, set) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, endOf(first, i), endOf(second, endOf(first, i))}, set) == True{} : Bool}

def pair_step_at(set, index, i, first, second, k, j, eqK, eqJ, inSet):
  %Equal.sym(Nat, endOf(first, i), k, eqK) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, _, endOf(second, _)}, set) == True{} : Bool}
  %Equal.sym(Nat, endOf(second, k), j, eqJ) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, k, _}, set) == True{} : Bool}
  inSet


law embedded_at:
  for -set: +List<Types.Bsr>
  for -tree: Types.Tree
  for -x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  for emb: {embedded(tree, set, y) == True{} : Bool}
  {embedded(tree, set, x) == True{} : Bool}

def embedded_at(set, tree, x, y, e, emb):
  %Equal.sym(Nat, x, y, e) : {embedded(tree, set, _) == True{} : Bool}
  emb


law pair_root:
  for +index: Nat
  for +i: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for +k: Nat
  for -j: Nat
  for +eqK: {endOf(first, i) == k : Nat}
  for eqJ: {endOf(second, k) == j : Nat}
  {rootStep(Types.Node{index, [first, second]}, i) == Types.Bsr{Types.Slot{index, 2n}, i, k, j} : Types.Bsr}

def pair_root(index, i, first, second, k, j, eqK, eqJ):
  +l1 = List.length(&2, Nat, GrammarLaws.leaves([first]))
  +l2 = List.length(&2, Nat, GrammarLaws.leaves([second]))
  lenSplit = Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([first, second])), List.length(&2, Nat, List.append(&2, Nat, GrammarLaws.leaves([first]), GrammarLaws.leaves([second]))), Nat.add(l1, l2), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([first, second]), List.append(&2, Nat, GrammarLaws.leaves([first]), GrammarLaws.leaves([second])), leaves_cons(first, [second])), Lemma.length_append(GrammarLaws.leaves([first]), GrammarLaws.leaves([second])))
  +end = Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves([first, second])))
  eqEnd = Equal.trans(Nat, end, Nat.add(i, Nat.add(l1, l2)), j, Equal.cong(Nat, Nat, n => Nat.add(i, n), List.length(&2, Nat, GrammarLaws.leaves([first, second])), Nat.add(l1, l2), lenSplit),
    Equal.trans(Nat, Nat.add(i, Nat.add(l1, l2)), Nat.add(Nat.add(i, l1), l2), j, Equal.sym(Nat, Nat.add(Nat.add(i, l1), l2), Nat.add(i, Nat.add(l1, l2)), Lemma.add_assoc(i, l1, l2)),
      Equal.trans(Nat, Nat.add(Nat.add(i, l1), l2), Nat.add(k, l2), j, Equal.cong(Nat, Nat, n => Nat.add(n, l2), endOf(first, i), k, eqK), eqJ)))
  %eqK : {rootStep(Types.Node{index, [first, second]}, i) == Types.Bsr{Types.Slot{index, 2n}, i, _, j} : Types.Bsr}
  %eqEnd : {rootStep(Types.Node{index, [first, second]}, i) == Types.Bsr{Types.Slot{index, 2n}, i, endOf(first, i), _} : Types.Bsr}
  {==}


law supported_pair_trees:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +index: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +b: Nat
  for +c: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsEq: {Types.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +ltIK: {Nat.is_lt(i, k) == True{} : Bool}
  for +ltKJ: {Nat.is_lt(k, j) == True{} : Bool}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for left: CellTree(grammar, inputTokens, b, i, Nat.sub(k, i))
  for right: CellTree(grammar, inputTokens, c, k, Nat.sub(j, k))
  Supported(grammar, inputTokens, a, index, 2n, i, k, j)

def supported_pair_trees(grammar, inputTokens, a, index, i, k, j, b, c, lhsOk, rhsEq, ltIK, ltKJ, inSet, left, right):
  match left:
    case (t10, (f10, (e1, (sp1, len1)))):
      match right:
        case (t20, (f20, (e2, (sp2, len2)))):
          +t1 = {t10 : Types.Tree}
          +t2 = {t20 : Types.Tree}
          +f1 = {f10 : {GrammarLaws.fits([t1], grammar, [Types.Nonterminal{b}]) == True{} : Bool}}
          +f2 = {f20 : {GrammarLaws.fits([t2], grammar, [Types.Nonterminal{c}]) == True{} : Bool}}
          +set = Grammar.cykSteps(grammar, inputTokens)
          +eqK = Equal.trans(Nat, endOf(t1, i), Nat.add(i, Nat.sub(k, i)), k, Equal.cong(Nat, Nat, n => Nat.add(i, n), List.length(&2, Nat, GrammarLaws.leaves([t1])), Nat.sub(k, i), len1), Lemma.add_sub_cancel(i, k, ltIK))
          +eqJ = Equal.trans(Nat, endOf(t2, k), Nat.add(k, Nat.sub(j, k)), j, Equal.cong(Nat, Nat, n => Nat.add(k, n), List.length(&2, Nat, GrammarLaws.leaves([t2])), Nat.sub(j, k), len2), Lemma.add_sub_cancel(k, j, ltKJ))
          emb = embed_two(t1, t2, grammar, b, c, set, index, i, f1, f2, pair_step_at(set, index, i, t1, t2, k, j, eqK, eqJ, inSet), e1, embedded_at(set, t2, endOf(t1, i), k, eqK, e2))
          (Types.Node{index, [t1, t2]}, (pair_node_fits(grammar, index, a, b, c, t1, t2, lhsOk, rhsEq, f1, f2), (emb, pair_root(index, i, t1, t2, k, j, eqK, eqJ))))


law supported_pair_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +index: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, 2n}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for parts: PairCells(Types.rhsOf(grammar, index), Table(grammar, inputTokens), i, k, j)
  Supported(grammar, inputTokens, a, index, 2n, i, k, j)

def supported_pair_parts(grammar, inputTokens, a, index, i, k, j, lhsOk, inSet, parts):
  match parts:
    case (b0, (c0, (rhsEq, (ltIK, (ltKJ, (inB, inC)))))):
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      supported_pair_trees(grammar, inputTokens, a, index, i, k, j, b, c, lhsOk, rhsEq, ltIK, ltKJ, inSet, tree_from_hit(grammar, inputTokens, b, i, Nat.sub(k, i), inB), tree_from_hit(grammar, inputTokens, c, k, Nat.sub(j, k), inC))


law supported_dot:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +index: Nat
  for dot: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for lhsOk: {Types.lhsIs(grammar, index, a) == True{} : Bool}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{index, dot}, i, k, j}, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}
  for from: {stepFrom(grammar, inputTokens, Table(grammar, inputTokens), Types.Bsr{Types.Slot{index, dot}, i, k, j}) == True{} : Bool}
  Supported(grammar, inputTokens, a, index, dot, i, k, j)

def supported_dot(grammar, inputTokens, a, index, dot, i, k, j, lhsOk, inSet, from):
  match dot:
    case 0n:
      Empty.absurd(Supported(grammar, inputTokens, a, index, 0n, i, k, j), Lemma.false_is_not_true(from))
    case 1n+0n:
      supported_leaf(grammar, inputTokens, a, index, i, k, j, lhsOk, inSet, from)
    case 1n+1n+0n:
      supported_pair_parts(grammar, inputTokens, a, index, i, k, j, lhsOk, inSet, pair_cells_parts(Types.rhsOf(grammar, index), Table(grammar, inputTokens), i, k, j, from))
    case 1n+1n+1n+more:
      Empty.absurd(Supported(grammar, inputTokens, a, index, 1n+1n+1n+more, i, k, j), Lemma.false_is_not_true(from))


# ======== ROOT STEPS ========

# ---- An embedded tree's root step is in the set ----

def LastSlot(+set: +List<Types.Bsr>, +q: Nat, +dot: Nat, +i: Nat, +at: Nat, +forest: +List<Types.Tree>) -> Type:
  {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, Nat.add(dot, List.length(&2, Types.Tree, forest))}, i, lastStart(forest, at), Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(forest)))}, set) == True{} : Bool}


law last_alone:
  for +set: +List<Types.Bsr>
  for +q: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  for +child: Types.Tree
  for parts: ChildParts(child, [], set, q, dot, i, at)
  LastSlot(set, q, dot, i, at, [child])

def last_alone(set, q, dot, i, at, child, parts):
  match parts:
    case (slot, (own, later)):
      +l = List.length(&2, Nat, GrammarLaws.leaves([child]))
      %Equal.sym(Nat, Nat.add(dot, 1n), 1n+dot, Lemma.add_one_right(dot)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, _}, i, at, Nat.add(at, l)}, set) == True{} : Bool}
      Lemma.or_and_false(Nat.is_eq(dot, 0n), GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, 1n+dot}, i, at, endOf(child, at)}, set), slot)


law last_more:
  for +set: +List<Types.Bsr>
  for +q: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  for +child: Types.Tree
  for +next: Types.Tree
  for +more: +List<Types.Tree>
  for later: LastSlot(set, q, 1n+dot, i, endOf(child, at), next <> more)
  LastSlot(set, q, dot, i, at, child <> next <> more)

def last_more(set, q, dot, i, at, child, next, more, later):
  +rest = {next <> more : +List<Types.Tree>}
  +l1 = List.length(&2, Nat, GrammarLaws.leaves([child]))
  +lr = List.length(&2, Nat, GrammarLaws.leaves(rest))
  lenSplit = Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves(child <> rest)), List.length(&2, Nat, List.append(&2, Nat, GrammarLaws.leaves([child]), GrammarLaws.leaves(rest))), Nat.add(l1, lr), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves(child <> rest), List.append(&2, Nat, GrammarLaws.leaves([child]), GrammarLaws.leaves(rest)), leaves_cons(child, rest)), Lemma.length_append(GrammarLaws.leaves([child]), GrammarLaws.leaves(rest)))
  endEq = Equal.trans(Nat, Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(child <> rest))), Nat.add(at, Nat.add(l1, lr)), Nat.add(Nat.add(at, l1), lr), Equal.cong(Nat, Nat, n => Nat.add(at, n), List.length(&2, Nat, GrammarLaws.leaves(child <> rest)), Nat.add(l1, lr), lenSplit), Equal.sym(Nat, Nat.add(Nat.add(at, l1), lr), Nat.add(at, Nat.add(l1, lr)), Lemma.add_assoc(at, l1, lr)))
  %Equal.sym(Nat, Nat.add(dot, 1n+List.length(&2, Types.Tree, rest)), 1n+Nat.add(dot, List.length(&2, Types.Tree, rest)), Lemma.add_succ_right(dot, List.length(&2, Types.Tree, rest))) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, _}, i, lastStart(rest, endOf(child, at)), Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(child <> rest)))}, set) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(at, List.length(&2, Nat, GrammarLaws.leaves(child <> rest))), Nat.add(Nat.add(at, l1), lr), endEq) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, 1n+Nat.add(dot, List.length(&2, Types.Tree, rest))}, i, lastStart(rest, endOf(child, at)), _}, set) == True{} : Bool}
  later


law later_slot:
  for -set: +List<Types.Bsr>
  for -q: Nat
  for -dot: Nat
  for -i: Nat
  for -at: Nat
  for -child: Types.Tree
  for -next: Types.Tree
  for -more: +List<Types.Tree>
  for parts: ChildParts(child, next <> more, set, q, dot, i, at)
  for search: {embeddedChildren(next <> more, set, q, 1n+dot, i, endOf(child, at)) == True{} : Bool} -> LastSlot(set, q, 1n+dot, i, endOf(child, at), next <> more)
  LastSlot(set, q, 1n+dot, i, endOf(child, at), next <> more)

def later_slot(set, q, dot, i, at, child, next, more, parts, search):
  match parts:
    case (slot, (own, later)):
      search(later)


# The step for the slot completed by the last child is in the set.
law last_slot:
  for rest: +List<Types.Tree>
  for +child: Types.Tree
  for +set: +List<Types.Bsr>
  for +q: Nat
  for +dot: Nat
  for +i: Nat
  for +at: Nat
  for e: {embeddedChildren(child <> rest, set, q, dot, i, at) == True{} : Bool}
  LastSlot(set, q, dot, i, at, child <> rest)

def last_slot(rest, child, set, q, dot, i, at, e):
  match rest:
    case Nil{}:
      last_alone(set, q, dot, i, at, child, child_parts(child, [], set, q, dot, i, at, e))
    case Con{+next, +more}:
      last_more(set, q, dot, i, at, child, next, more, later_slot(set, q, dot, i, at, child, next, more, child_parts(child, next <> more, set, q, dot, i, at, e), laterE => last_slot(more, next, set, q, 1n+dot, i, endOf(child, at), laterE)))


law embedded_root:
  for t: Types.Tree
  for +set: +List<Types.Bsr>
  for +i: Nat
  for emb: {embedded(t, set, i) == True{} : Bool}
  {GrammarLaws.bsrMember(rootStep(t, i), set) == True{} : Bool}

def embedded_root(t, set, i, emb):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd({GrammarLaws.bsrMember(rootStep(Types.Leaf{kind}, i), set) == True{} : Bool}, Lemma.false_is_not_true(emb))
    case Types.Node{+q, children}:
      match children:
        case Nil{}:
          %Equal.sym(Nat, Nat.add(i, 0n), i, Lemma.add_zero_right(i)) : {GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, 0n}, i, i, _}, set) == True{} : Bool}
          Lemma.and_true_left(GrammarLaws.bsrMember(Types.Bsr{Types.Slot{q, 0n}, i, i, i}, set), True{}, emb)
        case Con{+child, +rest}:
          last_slot(rest, child, set, q, 0n, i, i, emb)


law fits_length:
  for forest: +List<Types.Tree>
  for +grammar: +List<Types.Production>
  for symbols: +List<Types.Symbol>
  for e: {GrammarLaws.fits(forest, grammar, symbols) == True{} : Bool}
  {List.length(&2, Types.Tree, forest) == List.length(&2, Types.Symbol, symbols) : Nat}

def fits_length(forest, grammar, symbols, e):
  match forest symbols:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{s, ss}:
      Empty.absurd({0n == 1n+List.length(&2, Types.Symbol, ss) : Nat}, Lemma.false_is_not_true(e))
    case Con{Types.Leaf{k}, ts} Nil{}:
      Empty.absurd({1n+List.length(&2, Types.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(e))
    case Con{Types.Node{q, cs}, ts} Nil{}:
      Empty.absurd({1n+List.length(&2, Types.Tree, ts) == 0n : Nat}, Lemma.false_is_not_true(e))
    case Con{+t, +ts} Con{+s, +ss}:
      %fits_length(ts, grammar, ss, fits_cons_right(t, ts, s, ss, grammar, e)) : {1n+List.length(&2, Types.Tree, ts) == 1n+_ : Nat}
      {==}


# ======== NO DEAD WOOD ========
#
# Every kept element is a step of some parse tree of the whole input. The proof
# keeps a context for every need: any tree for the needed span extends to a parse
# tree of the whole input that has all its steps (NeedOk). The first need, the start
# symbol over the whole input, is its own context. A kept step A = B C over i .. j
# passes its context on: a tree for B over i .. k, next to a tree for C over k .. j
# from the CYK table, makes a tree for A over i .. j (all_ok).

# ---- Inclusion of lists of steps ----

law all_in_cons:
  for xs: +List<Types.Bsr>
  for +x: Types.Bsr
  for +set: +List<Types.Bsr>
  for all: {allIn(xs, set) == True{} : Bool}
  {allIn(xs, x <> set) == True{} : Bool}

def all_in_cons(xs, x, set, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +both = all
      Lemma.and_true_intro(GrammarLaws.bsrMember(y, x <> set), allIn(rest, x <> set),
        bsr_member_cons(y, x, set, Lemma.and_true_left(GrammarLaws.bsrMember(y, set), allIn(rest, set), both)),
        all_in_cons(rest, x, set, Lemma.and_true_right_side(GrammarLaws.bsrMember(y, set), allIn(rest, set), both)))

law all_in_refl:
  for xs: +List<Types.Bsr>
  {allIn(xs, xs) == True{} : Bool}

def all_in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(GrammarLaws.bsrMember(x, x <> rest), allIn(rest, x <> rest), bsr_member_head(x, rest), all_in_cons(rest, x, rest, all_in_refl(rest)))

law all_in_left:
  for xs: +List<Types.Bsr>
  for +zs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for all: {allIn(xs, zs) == True{} : Bool}
  {allIn(xs, List.append(&2, Types.Bsr, zs, ys)) == True{} : Bool}

def all_in_left(xs, zs, ys, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = all
      Lemma.and_true_intro(GrammarLaws.bsrMember(x, List.append(&2, Types.Bsr, zs, ys)), allIn(rest, List.append(&2, Types.Bsr, zs, ys)),
        bsr_member_append_left(x, zs, ys, Lemma.and_true_left(GrammarLaws.bsrMember(x, zs), allIn(rest, zs), both)),
        all_in_left(rest, zs, ys, Lemma.and_true_right_side(GrammarLaws.bsrMember(x, zs), allIn(rest, zs), both)))

law all_in_right:
  for xs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for +zs: +List<Types.Bsr>
  for all: {allIn(xs, ys) == True{} : Bool}
  {allIn(xs, List.append(&2, Types.Bsr, zs, ys)) == True{} : Bool}

def all_in_right(xs, ys, zs, all):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = all
      Lemma.and_true_intro(GrammarLaws.bsrMember(x, List.append(&2, Types.Bsr, zs, ys)), allIn(rest, List.append(&2, Types.Bsr, zs, ys)),
        bsr_member_append_right(x, zs, ys, Lemma.and_true_left(GrammarLaws.bsrMember(x, ys), allIn(rest, ys), both)),
        all_in_right(rest, ys, zs, Lemma.and_true_right_side(GrammarLaws.bsrMember(x, ys), allIn(rest, ys), both)))

law all_in_trans:
  for xs: +List<Types.Bsr>
  for +ys: +List<Types.Bsr>
  for +zs: +List<Types.Bsr>
  for xy: {allIn(xs, ys) == True{} : Bool}
  for +yz: {allIn(ys, zs) == True{} : Bool}
  {allIn(xs, zs) == True{} : Bool}

def all_in_trans(xs, ys, zs, xy, yz):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = xy
      Lemma.and_true_intro(GrammarLaws.bsrMember(x, zs), allIn(rest, zs),
        all_in_member(ys, zs, x, yz, Lemma.and_true_left(GrammarLaws.bsrMember(x, ys), allIn(rest, ys), both)),
        all_in_trans(rest, ys, zs, Lemma.and_true_right_side(GrammarLaws.bsrMember(x, ys), allIn(rest, ys), both), yz))

# ---- The steps of a child are steps of its parent ----

law first_in_pair:
  for +p: Nat
  for +q1: Nat
  for +ch1: +List<Types.Tree>
  for +second: Types.Tree
  for +i: Nat
  {allIn(GrammarLaws.steps(Types.Node{q1, ch1}, i), GrammarLaws.steps(Types.Node{p, [Types.Node{q1, ch1}, second]}, i)) == True{} : Bool}

def first_in_pair(p, q1, ch1, second, i):
  +own = GrammarLaws.steps(Types.Node{q1, ch1}, i)
  all_in_left(own, own, GrammarLaws.childSteps([second], p, 1n, i, Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(ch1)))), all_in_refl(own))

law second_in_pair:
  for +p: Nat
  for +q1: Nat
  for +ch1: +List<Types.Tree>
  for +q2: Nat
  for +ch2: +List<Types.Tree>
  for +i: Nat
  {allIn(GrammarLaws.steps(Types.Node{q2, ch2}, Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(ch1)))), GrammarLaws.steps(Types.Node{p, [Types.Node{q1, ch1}, Types.Node{q2, ch2}]}, i)) == True{} : Bool}

def second_in_pair(p, q1, ch1, q2, ch2, i):
  +e1 = Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(ch1)))
  +e2 = Nat.add(e1, List.length(&2, Nat, GrammarLaws.leaves(ch2)))
  +own = GrammarLaws.steps(Types.Node{q2, ch2}, e1)
  +element = {Types.Bsr{Types.Slot{p, 2n}, i, e1, e2} : Types.Bsr}
  all_in_right(own, element <> List.append(&2, Types.Bsr, own, []), GrammarLaws.steps(Types.Node{q1, ch1}, i),
    all_in_cons(own, element, List.append(&2, Types.Bsr, own, []), all_in_left(own, own, [], all_in_refl(own))))

# ---- Joining two trees ----

def Joined(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +a: Nat, +i: Nat, +j: Nat, +node: Types.Tree) -> Type:
  {GrammarLaws.fits([node], grammar, [Types.Nonterminal{a}]) == True{} : Bool} & Spells(node, inputTokens, i) & {endOf(node, i) == j : Nat}

# A node a = b c over a tree for b from i to k and a tree for c from k to j spans i to j.
law join_trees:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for f1: {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for sp1: Spells(first, inputTokens, i)
  for e1: {endOf(first, i) == k : Nat}
  for f2: {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  for sp2: Spells(second, inputTokens, k)
  for e2: {endOf(second, k) == j : Nat}
  Joined(grammar, inputTokens, a, i, j, Types.Node{p, [first, second]})

def join_trees(grammar, inputTokens, p, a, b, c, i, k, j, first, second, lhsOk, rhsOk, f1, sp1, e1, f2, sp2, e2):
  +node = {Types.Node{p, [first, second]} : Types.Tree}
  +w1 = GrammarLaws.leaves([first])
  +w2 = GrammarLaws.leaves([second])
  +l1 = List.length(&2, Nat, w1)
  +l2 = List.length(&2, Nat, w2)
  +end1 = e1
  +sp2b = Equal.trans(+List<Nat>, w2, Lemma.slice(inputTokens, k, l2), Lemma.slice(inputTokens, Nat.add(i, l1), l2), sp2,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(inputTokens, v, l2), k, Nat.add(i, l1), Equal.sym(Nat, Nat.add(i, l1), k, end1)))
  +joined = node_leaves(p, [first, second], List.append(&2, Nat, w1, w2), pair_leaves(first, second, w1, w2, {==}, {==}))
  +spelled = Equal.trans(+List<Nat>, GrammarLaws.leaves([node]), List.append(&2, Nat, w1, w2), Lemma.slice(inputTokens, i, Nat.add(l1, l2)),
    joined,
    Equal.trans(+List<Nat>, List.append(&2, Nat, w1, w2), List.append(&2, Nat, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, Nat.add(i, l1), l2)), Lemma.slice(inputTokens, i, Nat.add(l1, l2)),
      Lemma.append_congr(w1, w2, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, Nat.add(i, l1), l2), sp1, sp2b),
      Lemma.slice_split(inputTokens, i, l1, l2)))
  +lenNode = Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([node])), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(l1, l2),
    Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([node]), List.append(&2, Nat, w1, w2), joined),
    Lemma.length_append(w1, w2))
  spells = Equal.trans(+List<Nat>, GrammarLaws.leaves([node]), Lemma.slice(inputTokens, i, Nat.add(l1, l2)), Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([node]))),
    spelled,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(inputTokens, i, v), Nat.add(l1, l2), List.length(&2, Nat, GrammarLaws.leaves([node])), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([node])), Nat.add(l1, l2), lenNode)))
  ends = Equal.trans(Nat, endOf(node, i), Nat.add(i, Nat.add(l1, l2)), j,
    Equal.cong(Nat, Nat, v => Nat.add(i, v), List.length(&2, Nat, GrammarLaws.leaves([node])), Nat.add(l1, l2), lenNode),
    Equal.trans(Nat, Nat.add(i, Nat.add(l1, l2)), Nat.add(Nat.add(i, l1), l2), j,
      Equal.sym(Nat, Nat.add(Nat.add(i, l1), l2), Nat.add(i, Nat.add(l1, l2)), Lemma.add_assoc(i, l1, l2)),
      Equal.trans(Nat, Nat.add(Nat.add(i, l1), l2), Nat.add(k, l2), j,
        Equal.cong(Nat, Nat, v => Nat.add(v, l2), Nat.add(i, l1), k, end1),
        e2)))
  (pair_node_fits(grammar, p, a, b, c, first, second, lhsOk, rhsOk, f1, f2), (spells, ends))

# A tree from a cell of the table spells its slice and ends where the slice ends.
law cell_spells:
  for +inputTokens: +List<Nat>
  for +t: Types.Tree
  for +s: Nat
  for +l: Nat
  for leavesEq: {GrammarLaws.leaves([t]) == Lemma.slice(inputTokens, s, l) : +List<Nat>}
  for +len: {List.length(&2, Nat, GrammarLaws.leaves([t])) == l : Nat}
  Spells(t, inputTokens, s)

def cell_spells(inputTokens, t, s, l, leavesEq, len):
  Equal.trans(+List<Nat>, GrammarLaws.leaves([t]), Lemma.slice(inputTokens, s, l), Lemma.slice(inputTokens, s, List.length(&2, Nat, GrammarLaws.leaves([t]))),
    leavesEq,
    Equal.cong(Nat, +List<Nat>, v => Lemma.slice(inputTokens, s, v), l, List.length(&2, Nat, GrammarLaws.leaves([t])), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([t])), l, len)))

law cell_end:
  for +t: Types.Tree
  for +s: Nat
  for +e: Nat
  for len: {List.length(&2, Nat, GrammarLaws.leaves([t])) == Nat.sub(e, s) : Nat}
  for lt: {Nat.is_lt(s, e) == True{} : Bool}
  {endOf(t, s) == e : Nat}

def cell_end(t, s, e, len, lt):
  Equal.trans(Nat, endOf(t, s), Nat.add(s, Nat.sub(e, s)), e,
    Equal.cong(Nat, Nat, v => Nat.add(s, v), List.length(&2, Nat, GrammarLaws.leaves([t])), Nat.sub(e, s), len),
    Lemma.add_sub_cancel(s, e, lt))

# ---- Contexts ----

def Context(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +t: Types.Tree, +i: Nat) -> Type:
  &whole: Types.Tree -> {GrammarLaws.fits([whole], grammar, [Types.Nonterminal{start}]) == True{} : Bool} & {GrammarLaws.leaves([whole]) == inputTokens : +List<Nat>} & {allIn(GrammarLaws.steps(t, i), GrammarLaws.steps(whole, 0n)) == True{} : Bool}

# Every tree for a over i .. j extends to a parse tree of the whole input.
def NeedOk(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +a: Nat, +i: Nat, +j: Nat) -> Type:
  @t: Types.Tree -> {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool} -> Spells(t, inputTokens, i) -> {endOf(t, i) == j : Nat} -> Context(grammar, start, inputTokens, t, i)

def NeedOkOf(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, need: Grammar.Need) -> Type:
  match need:
    case Grammar.Need{a, i, j}:
      NeedOk(grammar, start, inputTokens, a, i, j)

def AllOk(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +n: Nat) -> Type:
  @need: Grammar.Need -> {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, n)) == True{} : Bool} -> NeedOkOf(grammar, start, inputTokens, need)

# The whole input is its own context.
law root_context:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +t: Types.Tree
  for fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for spells: Spells(t, inputTokens, 0n)
  for ends: {endOf(t, 0n) == List.length(&2, Nat, inputTokens) : Nat}
  Context(grammar, start, inputTokens, t, 0n)

def root_context(grammar, start, inputTokens, t, fitting, spells, ends):
  +l = List.length(&2, Nat, GrammarLaws.leaves([t]))
  +count = List.length(&2, Nat, inputTokens)
  whole = Equal.trans(+List<Nat>, GrammarLaws.leaves([t]), Lemma.takeN(l, inputTokens), inputTokens, spells,
    Equal.trans(+List<Nat>, Lemma.takeN(l, inputTokens), Lemma.takeN(count, inputTokens), inputTokens,
      Equal.cong(Nat, +List<Nat>, v => Lemma.takeN(v, inputTokens), l, count, ends),
      Lemma.take_length(inputTokens)))
  (t, (fitting, (whole, all_in_refl(GrammarLaws.steps(t, 0n)))))


# ---- Membership facts for needs ----

law need_eq_sound:
  for +a: Nat
  for +i: Nat
  for +j: Nat
  for +a2: Nat
  for +i2: Nat
  for +j2: Nat
  for same: {Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))) == True{} : Bool}
  {Grammar.Need{a, i, j} == Grammar.Need{a2, i2, j2} : Grammar.Need}

def need_eq_sound(a, i, j, a2, i2, j2, same):
  +s0 = same
  +r1 = Lemma.and_true_right_side(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2)), s0)
  ea = Lemma.nat_eq_sound(a, a2, Lemma.and_true_left(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2)), s0))
  ei = Lemma.nat_eq_sound(i, i2, Lemma.and_true_left(Nat.is_eq(i, i2), Nat.is_eq(j, j2), r1))
  ej = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Nat.is_eq(i, i2), Nat.is_eq(j, j2), r1))
  %ea : {Grammar.Need{a, i, j} == Grammar.Need{_, i2, j2} : Grammar.Need}
  %ei : {Grammar.Need{a, i, j} == Grammar.Need{a, _, j2} : Grammar.Need}
  %ej : {Grammar.Need{a, i, j} == Grammar.Need{a, i, _} : Grammar.Need}
  {==}

law need_cons_pick:
  for +a: Nat
  for +i: Nat
  for +j: Nat
  for +a2: Nat
  for +i2: Nat
  for +j2: Nat
  for -rest: +List<Grammar.Need>
  for cases: Either<{Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))) == True{} : Bool}, {Grammar.needMember(Grammar.Need{a, i, j}, rest) == True{} : Bool}>
  Either<{Grammar.Need{a, i, j} == Grammar.Need{a2, i2, j2} : Grammar.Need}, {Grammar.needMember(Grammar.Need{a, i, j}, rest) == True{} : Bool}>

def need_cons_pick(a, i, j, a2, i2, j2, rest, cases):
  match cases:
    case Inl{same}:
      Inl{need_eq_sound(a, i, j, a2, i2, j2, same)}
    case Inr{later}:
      Inr{later}

law need_cons_cases:
  for need: Grammar.Need
  for x: Grammar.Need
  for -rest: +List<Grammar.Need>
  for m: {Grammar.needMember(need, x <> rest) == True{} : Bool}
  Either<{need == x : Grammar.Need}, {Grammar.needMember(need, rest) == True{} : Bool}>

def need_cons_cases(need, x, rest, m):
  match need x:
    case Grammar.Need{+a, +i, +j} Grammar.Need{+a2, +i2, +j2}:
      need_cons_pick(a, i, j, a2, i2, j2, rest, Lemma.or_true_cases(Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(i, i2), Nat.is_eq(j, j2))), Grammar.needMember(Grammar.Need{a, i, j}, rest), m))

law need_not_in_empty:
  for need: Grammar.Need
  for m: {Grammar.needMember(need, []) == True{} : Bool}
  Empty

def need_not_in_empty(need, m):
  match need:
    case Grammar.Need{a, i, j}:
      Lemma.false_is_not_true(m)

law need_member_self:
  for need: Grammar.Need
  for +rest: +List<Grammar.Need>
  {Grammar.needMember(need, need <> rest) == True{} : Bool}

def need_member_self(need, rest):
  match need:
    case Grammar.Need{+a, +i, +j}:
      need_member_head(a, i, j, rest)

law need_later_pick:
  for +need: Grammar.Need
  for +x: Grammar.Need
  for +rest: +List<Grammar.Need>
  for -ys: +List<Grammar.Need>
  for cases: Either<{Grammar.needMember(need, rest) == True{} : Bool}, {Grammar.needMember(need, ys) == True{} : Bool}>
  Either<{Grammar.needMember(need, x <> rest) == True{} : Bool}, {Grammar.needMember(need, ys) == True{} : Bool}>

def need_later_pick(need, x, rest, ys, cases):
  match cases:
    case Inl{inRest}:
      Inl{need_member_cons(need, x, rest, inRest)}
    case Inr{inYs}:
      Inr{inYs}

law need_append_pick:
  for +need: Grammar.Need
  for +x: Grammar.Need
  for +rest: +List<Grammar.Need>
  for -ys: +List<Grammar.Need>
  for cases: Either<{need == x : Grammar.Need}, {Grammar.needMember(need, List.append(&2, Grammar.Need, rest, ys)) == True{} : Bool}>
  for searchRest: {Grammar.needMember(need, List.append(&2, Grammar.Need, rest, ys)) == True{} : Bool} -> Either<{Grammar.needMember(need, rest) == True{} : Bool}, {Grammar.needMember(need, ys) == True{} : Bool}>
  Either<{Grammar.needMember(need, x <> rest) == True{} : Bool}, {Grammar.needMember(need, ys) == True{} : Bool}>

def need_append_pick(need, x, rest, ys, cases, searchRest):
  match cases:
    case Inl{same}:
      %same : {Grammar.needMember(need, _ <> rest) == True{} : Bool} | {Grammar.needMember(need, ys) == True{} : Bool}
      Inl{need_member_self(need, rest)}
    case Inr{later}:
      need_later_pick(need, x, rest, ys, searchRest(later))

law need_append_cases:
  for +need: Grammar.Need
  for xs: +List<Grammar.Need>
  for -ys: +List<Grammar.Need>
  for m: {Grammar.needMember(need, List.append(&2, Grammar.Need, xs, ys)) == True{} : Bool}
  Either<{Grammar.needMember(need, xs) == True{} : Bool}, {Grammar.needMember(need, ys) == True{} : Bool}>

def need_append_cases(need, xs, ys, m):
  match xs:
    case Nil{}:
      Inr{m}
    case Con{+x, +rest}:
      need_append_pick(need, x, rest, ys, need_cons_cases(need, x, List.append(&2, Grammar.Need, rest, ys), m),
        later => need_append_cases(need, rest, ys, later))

# The two needs of a step A = B C.
law pair_need_cases:
  for +need: Grammar.Need
  for +b: Nat
  for +i: Nat
  for +k: Nat
  for +c: Nat
  for +j: Nat
  for m: {Grammar.needMember(need, [Grammar.Need{b, i, k}, Grammar.Need{c, k, j}]) == True{} : Bool}
  Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {need == Grammar.Need{c, k, j} : Grammar.Need}>

law pair_second_pick:
  for need: Grammar.Need
  for -b: Nat
  for -i: Nat
  for -k: Nat
  for -c: Nat
  for -j: Nat
  for cases: Either<{need == Grammar.Need{c, k, j} : Grammar.Need}, {Grammar.needMember(need, []) == True{} : Bool}>
  Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {need == Grammar.Need{c, k, j} : Grammar.Need}>

def pair_second_pick(need, b, i, k, c, j, cases):
  match cases:
    case Inl{second}:
      Inr{second}
    case Inr{none}:
      Empty.absurd(Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {need == Grammar.Need{c, k, j} : Grammar.Need}>, need_not_in_empty(need, none))

law pair_first_pick:
  for +need: Grammar.Need
  for +b: Nat
  for +i: Nat
  for +k: Nat
  for +c: Nat
  for +j: Nat
  for cases: Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {Grammar.needMember(need, [Grammar.Need{c, k, j}]) == True{} : Bool}>
  Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {need == Grammar.Need{c, k, j} : Grammar.Need}>

def pair_first_pick(need, b, i, k, c, j, cases):
  match cases:
    case Inl{first}:
      Inl{first}
    case Inr{later}:
      pair_second_pick(need, b, i, k, c, j, need_cons_cases(need, Grammar.Need{c, k, j}, [], later))

def pair_need_cases(need, b, i, k, c, j, m):
  pair_first_pick(need, b, i, k, c, j, need_cons_cases(need, Grammar.Need{b, i, k}, [Grammar.Need{c, k, j}], m))


# ---- What filtering and child needs come from ----

def KeptFact(+grammar: +List<Types.Production>, +needs: +List<Grammar.Need>, +xs: +List<Types.Bsr>, +element: Types.Bsr) -> Type:
  {GrammarLaws.bsrMember(element, xs) == True{} : Bool} & {Grammar.isNeeded(grammar, needs, element) == True{} : Bool}

law kept_cons:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for +element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for fact: KeptFact(grammar, needs, rest, element)
  KeptFact(grammar, needs, x <> rest, element)

def kept_cons(grammar, needs, element, x, rest, fact):
  match fact:
    case (inRest, neededE):
      (bsr_member_cons(element, x, rest, inRest), neededE)

law kept_head_pick:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for +element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for +others: +List<Types.Bsr>
  for +keepEq: {Grammar.isNeeded(grammar, needs, x) == True{} : Bool}
  for cases: Either<{element == x : Types.Bsr}, {GrammarLaws.bsrMember(element, others) == True{} : Bool}>
  for searchRest: {GrammarLaws.bsrMember(element, others) == True{} : Bool} -> KeptFact(grammar, needs, rest, element)
  KeptFact(grammar, needs, x <> rest, element)

def kept_head_pick(grammar, needs, element, x, rest, others, keepEq, cases, searchRest):
  match cases:
    case Inl{same}:
      +eq = same
      neededE = Equal.trans(Bool, Grammar.isNeeded(grammar, needs, element), Grammar.isNeeded(grammar, needs, x), True{},
        Equal.cong(Types.Bsr, Bool, v => Grammar.isNeeded(grammar, needs, v), element, x, eq), keepEq)
      inXs = Equal.trans(Bool, GrammarLaws.bsrMember(element, x <> rest), GrammarLaws.bsrMember(x, x <> rest), True{},
        Equal.cong(Types.Bsr, Bool, v => GrammarLaws.bsrMember(v, x <> rest), element, x, eq), bsr_member_head(x, rest))
      (inXs, neededE)
    case Inr{later}:
      kept_cons(grammar, needs, element, x, rest, searchRest(later))

law kept_pick:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for +element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for keep: Bool
  for +keepEq: {Grammar.isNeeded(grammar, needs, x) == keep : Bool}
  for m: {GrammarLaws.bsrMember(element, Grammar.keepNeeded(keep, x, Grammar.filterNeeded(grammar, needs, rest))) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(element, Grammar.filterNeeded(grammar, needs, rest)) == True{} : Bool} -> KeptFact(grammar, needs, rest, element)
  KeptFact(grammar, needs, x <> rest, element)

def kept_pick(grammar, needs, element, x, rest, keep, keepEq, m, searchRest):
  match keep:
    case False{}:
      kept_cons(grammar, needs, element, x, rest, searchRest(m))
    case True{}:
      +others = Grammar.filterNeeded(grammar, needs, rest)
      kept_head_pick(grammar, needs, element, x, rest, others, keepEq, member_cons_cases(element, x, others, m), searchRest)

# An element that survives filtering was in the list and is needed.
law filter_find:
  for +grammar: +List<Types.Production>
  for +needs: +List<Grammar.Need>
  for xs: +List<Types.Bsr>
  for +element: Types.Bsr
  for m: {GrammarLaws.bsrMember(element, Grammar.filterNeeded(grammar, needs, xs)) == True{} : Bool}
  KeptFact(grammar, needs, xs, element)

def filter_find(grammar, needs, xs, element, m):
  match xs:
    case Nil{}:
      Empty.absurd(KeptFact(grammar, needs, [], element), not_in_empty(element, m))
    case Con{+x, +rest}:
      kept_pick(grammar, needs, element, x, rest, Grammar.isNeeded(grammar, needs, x), {==}, m,
        later => filter_find(grammar, needs, rest, element, later))

def ChildFrom(+grammar: +List<Types.Production>, +xs: +List<Types.Bsr>, +need: Grammar.Need) -> Type:
  &x: Types.Bsr -> {GrammarLaws.bsrMember(x, xs) == True{} : Bool} & {Grammar.needMember(need, Grammar.childNeeds(grammar, x)) == True{} : Bool}

law child_from_cons:
  for +grammar: +List<Types.Production>
  for +need: Grammar.Need
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for found: ChildFrom(grammar, rest, need)
  ChildFrom(grammar, x <> rest, need)

def child_from_cons(grammar, need, x, rest, found):
  match found:
    case (y0, (inRest, hy)):
      +y = {y0 : Types.Bsr}
      (y, (bsr_member_cons(y, x, rest, inRest), hy))

law child_from_pick:
  for +grammar: +List<Types.Production>
  for +need: Grammar.Need
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for cases: Either<{Grammar.needMember(need, Grammar.childNeeds(grammar, x)) == True{} : Bool}, {Grammar.needMember(need, Grammar.allChildNeeds(grammar, rest)) == True{} : Bool}>
  for searchRest: {Grammar.needMember(need, Grammar.allChildNeeds(grammar, rest)) == True{} : Bool} -> ChildFrom(grammar, rest, need)
  ChildFrom(grammar, x <> rest, need)

def child_from_pick(grammar, need, x, rest, cases, searchRest):
  match cases:
    case Inl{here}:
      (x, (bsr_member_head(x, rest), here))
    case Inr{later}:
      child_from_cons(grammar, need, x, rest, searchRest(later))

# A need among the child needs of a list comes from one element of the list.
law child_needs_find:
  for +grammar: +List<Types.Production>
  for xs: +List<Types.Bsr>
  for +need: Grammar.Need
  for m: {Grammar.needMember(need, Grammar.allChildNeeds(grammar, xs)) == True{} : Bool}
  ChildFrom(grammar, xs, need)

def child_needs_find(grammar, xs, need, m):
  match xs:
    case Nil{}:
      Empty.absurd(ChildFrom(grammar, [], need), need_not_in_empty(need, m))
    case Con{+x, +rest}:
      child_from_pick(grammar, need, x, rest, need_append_cases(need, Grammar.childNeeds(grammar, x), Grammar.allChildNeeds(grammar, rest), m),
        later => child_needs_find(grammar, rest, need, later))

# ---- The nonterminal of a production that exists ----

law lhs_of_self:
  for +grammar: +List<Types.Production>
  for p: Nat
  for ne: {List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}
  {Types.lhsIs(grammar, p, Grammar.lhsOf(grammar, p)) == True{} : Bool}

def lhs_of_self(grammar, p, ne):
  match grammar p:
    case Nil{} 0n:
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(ne))
    case Nil{} 1n+q:
      Empty.absurd({False{} == True{} : Bool}, Lemma.true_is_not_false(ne))
    case Con{Types.Production{+lhs, rhs}, rest} 0n:
      Lemma.nat_eq_refl(lhs)
    case Con{prod, +rest} 1n+q:
      lhs_of_self(rest, q, ne)

law pair_nonempty:
  for +grammar: +List<Types.Production>
  for +p: Nat
  for -b: Nat
  for -c: Nat
  for rhsEq: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  {List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}

def pair_nonempty(grammar, p, b, c, rhsEq):
  Equal.cong(+List<Types.Symbol>, Bool, x => List.is_empty(&2, Types.Symbol, x), Types.rhsOf(grammar, p), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsEq)

# ---- A kept step passes its context on to its children ----

law apply_parent:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +i: Nat
  for +j: Nat
  for +node: Types.Tree
  for parent: NeedOk(grammar, start, inputTokens, a, i, j)
  for joined: Joined(grammar, inputTokens, a, i, j, node)
  Context(grammar, start, inputTokens, node, i)

def apply_parent(grammar, start, inputTokens, a, i, j, node, parent, joined):
  match joined:
    case (fN, (spN, enN)):
      parent(node, fN, spN, enN)

# A context for a node is a context for a tree whose steps are among the node's.
law lift_context:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +t: Types.Tree
  for +at: Nat
  for +node: Types.Tree
  for +i: Nat
  for sub0: {allIn(GrammarLaws.steps(t, at), GrammarLaws.steps(node, i)) == True{} : Bool}
  for ctx: Context(grammar, start, inputTokens, node, i)
  Context(grammar, start, inputTokens, t, at)

def lift_context(grammar, start, inputTokens, t, at, node, i, sub0, ctx):
  match ctx:
    case (whole0, (fw, (lw, sub))):
      +whole = {whole0 : Types.Tree}
      (whole, (fw, (lw, all_in_trans(GrammarLaws.steps(t, at), GrammarLaws.steps(node, i), GrammarLaws.steps(whole, 0n), sub0, sub))))

law left_context:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for +rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +ltKJ: {Nat.is_lt(k, j) == True{} : Bool}
  for right: CellTree(grammar, inputTokens, c, k, Nat.sub(j, k))
  for parent: NeedOk(grammar, start, inputTokens, a, i, j)
  for t: Types.Tree
  for ft: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{b}]) == True{} : Bool}
  for sp: Spells(t, inputTokens, i)
  for en: {endOf(t, i) == k : Nat}
  Context(grammar, start, inputTokens, t, i)

def left_context(grammar, start, inputTokens, p, a, b, c, i, k, j, lhsOk, rhsOk, ltKJ, right, parent, t, ft, sp, en):
  match right:
    case (tc0, (fc0, (embc, (leavesc, lenc0)))):
      match t:
        case Types.Leaf{kind}:
          Empty.absurd(Context(grammar, start, inputTokens, Types.Leaf{kind}, i), Lemma.false_is_not_true(ft))
        case Types.Node{+q1, +ch1}:
          +tc = {tc0 : Types.Tree}
          +lenc = {lenc0 : {List.length(&2, Nat, GrammarLaws.leaves([tc])) == Nat.sub(j, k) : Nat}}
          +t1 = {Types.Node{q1, ch1} : Types.Tree}
          +node = {Types.Node{p, [t1, tc]} : Types.Tree}
          sp2 = cell_spells(inputTokens, tc, k, Nat.sub(j, k), leavesc, lenc)
          e2 = cell_end(tc, k, j, lenc, ltKJ)
          lift_context(grammar, start, inputTokens, t1, i, node, i, first_in_pair(p, q1, ch1, tc, i),
            apply_parent(grammar, start, inputTokens, a, i, j, node, parent, join_trees(grammar, inputTokens, p, a, b, c, i, k, j, t1, tc, lhsOk, rhsOk, ft, sp, en, fc0, sp2, e2)))

law right_context:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for +rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +ltIK: {Nat.is_lt(i, k) == True{} : Bool}
  for left: CellTree(grammar, inputTokens, b, i, Nat.sub(k, i))
  for parent: NeedOk(grammar, start, inputTokens, a, i, j)
  for t: Types.Tree
  for ft: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{c}]) == True{} : Bool}
  for sp: Spells(t, inputTokens, k)
  for en: {endOf(t, k) == j : Nat}
  Context(grammar, start, inputTokens, t, k)

def right_context(grammar, start, inputTokens, p, a, b, c, i, k, j, lhsOk, rhsOk, ltIK, left, parent, t, ft, sp, en):
  match left:
    case (Types.Leaf{kind}, (fb, more)):
      Empty.absurd(Context(grammar, start, inputTokens, t, k), Lemma.false_is_not_true(fb))
    case (Types.Node{+q1, +ch1}, (fb, (embb, (leavesb, lenb0)))):
      match t:
        case Types.Leaf{kind}:
          Empty.absurd(Context(grammar, start, inputTokens, Types.Leaf{kind}, k), Lemma.false_is_not_true(ft))
        case Types.Node{+q2, +ch2}:
          +tb = {Types.Node{q1, ch1} : Types.Tree}
          +t2 = {Types.Node{q2, ch2} : Types.Tree}
          +node = {Types.Node{p, [tb, t2]} : Types.Tree}
          +lenb = {lenb0 : {List.length(&2, Nat, GrammarLaws.leaves([tb])) == Nat.sub(k, i) : Nat}}
          sp1 = cell_spells(inputTokens, tb, i, Nat.sub(k, i), leavesb, lenb)
          +e1 = cell_end(tb, i, k, lenb, ltIK)
          +mid = Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(ch1)))
          kEq = Equal.trans(Nat, mid, endOf(tb, i), k,
            Equal.cong(Nat, Nat, v => Nat.add(i, v), List.length(&2, Nat, GrammarLaws.leaves(ch1)), List.length(&2, Nat, GrammarLaws.leaves([tb])), length_node_leaves(q1, ch1)),
            e1)
          sub0 = Equal.trans(Bool, allIn(GrammarLaws.steps(t2, k), GrammarLaws.steps(node, i)), allIn(GrammarLaws.steps(t2, mid), GrammarLaws.steps(node, i)), True{},
            Equal.cong(Nat, Bool, v => allIn(GrammarLaws.steps(t2, v), GrammarLaws.steps(node, i)), k, mid, Equal.sym(Nat, mid, k, kEq)),
            second_in_pair(p, q1, ch1, q2, ch2, i))
          lift_context(grammar, start, inputTokens, t2, k, node, i, sub0,
            apply_parent(grammar, start, inputTokens, a, i, j, node, parent, join_trees(grammar, inputTokens, p, a, b, c, i, k, j, tb, t2, lhsOk, rhsOk, fb, sp1, e1, ft, sp, en)))

# ---- Every need in every round has a context ----

law child_side:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +need: Grammar.Need
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +lhsOk: {Types.lhsIs(grammar, p, a) == True{} : Bool}
  for +rhsOk: {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +ltIK: {Nat.is_lt(i, k) == True{} : Bool}
  for +ltKJ: {Nat.is_lt(k, j) == True{} : Bool}
  for inB: {Grammar.natMember(b, Grammar.lookup(Table(grammar, inputTokens), i, Nat.sub(k, i))) == True{} : Bool}
  for inC: {Grammar.natMember(c, Grammar.lookup(Table(grammar, inputTokens), k, Nat.sub(j, k))) == True{} : Bool}
  for parent: NeedOk(grammar, start, inputTokens, a, i, j)
  for cases: Either<{need == Grammar.Need{b, i, k} : Grammar.Need}, {need == Grammar.Need{c, k, j} : Grammar.Need}>
  NeedOkOf(grammar, start, inputTokens, need)

def child_side(grammar, start, inputTokens, need, p, a, b, c, i, k, j, lhsOk, rhsOk, ltIK, ltKJ, inB, inC, parent, cases):
  match cases:
    case Inl{isB}:
      %Equal.sym(Grammar.Need, need, Grammar.Need{b, i, k}, isB) : NeedOkOf(grammar, start, inputTokens, _)
      t => ft => sp => en => left_context(grammar, start, inputTokens, p, a, b, c, i, k, j, lhsOk, rhsOk, ltKJ, tree_from_hit(grammar, inputTokens, c, k, Nat.sub(j, k), inC), parent, t, ft, sp, en)
    case Inr{isC}:
      %Equal.sym(Grammar.Need, need, Grammar.Need{c, k, j}, isC) : NeedOkOf(grammar, start, inputTokens, _)
      t => ft => sp => en => right_context(grammar, start, inputTokens, p, a, b, c, i, k, j, lhsOk, rhsOk, ltIK, tree_from_hit(grammar, inputTokens, b, i, Nat.sub(k, i), inB), parent, t, ft, sp, en)

law pair_child_parts:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +need: Grammar.Need
  for +p: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for parts: PairCells(Types.rhsOf(grammar, p), Table(grammar, inputTokens), i, k, j)
  for parent: NeedOk(grammar, start, inputTokens, Grammar.lhsOf(grammar, p), i, j)
  for inChild: {Grammar.needMember(need, Grammar.pairNeeds(Types.rhsOf(grammar, p), i, k, j)) == True{} : Bool}
  NeedOkOf(grammar, start, inputTokens, need)

def pair_child_parts(grammar, start, inputTokens, need, p, i, k, j, parts, parent, inChild):
  match parts:
    case (b0, (c0, (rhsEq0, (ltIK, (ltKJ, (inB, inC)))))):
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      +rhsEq = {rhsEq0 : {Types.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}}
      +a = Grammar.lhsOf(grammar, p)
      +lhsA = lhs_of_self(grammar, p, pair_nonempty(grammar, p, b, c, rhsEq))
      inPair = Equal.trans(Bool, Grammar.needMember(need, [Grammar.Need{b, i, k}, Grammar.Need{c, k, j}]), Grammar.needMember(need, Grammar.pairNeeds(Types.rhsOf(grammar, p), i, k, j)), True{},
        Equal.sym(Bool, Grammar.needMember(need, Grammar.pairNeeds(Types.rhsOf(grammar, p), i, k, j)), Grammar.needMember(need, [Grammar.Need{b, i, k}, Grammar.Need{c, k, j}]),
          Equal.cong(+List<Types.Symbol>, Bool, v => Grammar.needMember(need, Grammar.pairNeeds(v, i, k, j)), Types.rhsOf(grammar, p), [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsEq)),
        inChild)
      child_side(grammar, start, inputTokens, need, p, a, b, c, i, k, j, lhsA, rhsEq, ltIK, ltKJ, inB, inC, parent, pair_need_cases(need, b, i, k, c, j, inPair))

law child_pair:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +m: Nat
  for okM: AllOk(grammar, start, inputTokens, m)
  for +need: Grammar.Need
  for +p: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for fact: KeptFact(grammar, NeedsAt(grammar, start, inputTokens, m), Grammar.cykSteps(grammar, inputTokens), Types.Bsr{Types.Slot{p, 2n}, i, k, j})
  for inChild: {Grammar.needMember(need, Grammar.childNeeds(grammar, Types.Bsr{Types.Slot{p, 2n}, i, k, j})) == True{} : Bool}
  NeedOkOf(grammar, start, inputTokens, need)

def child_pair(grammar, start, inputTokens, m, okM, need, p, i, k, j, fact, inChild):
  match fact:
    case (inS, needed):
      +element = {Types.Bsr{Types.Slot{p, 2n}, i, k, j} : Types.Bsr}
      from = in_set_from(grammar, inputTokens, element, inS)
      pair_child_parts(grammar, start, inputTokens, need, p, i, k, j,
        pair_cells_parts(Types.rhsOf(grammar, p), Table(grammar, inputTokens), i, k, j, from),
        okM(Grammar.Need{Grammar.lhsOf(grammar, p), i, j}, needed),
        inChild)

law child_ok:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +m: Nat
  for okM: AllOk(grammar, start, inputTokens, m)
  for +need: Grammar.Need
  for x: Types.Bsr
  for inF: {GrammarLaws.bsrMember(x, Grammar.filterNeeded(grammar, NeedsAt(grammar, start, inputTokens, m), Grammar.cykSteps(grammar, inputTokens))) == True{} : Bool}
  for inChild: {Grammar.needMember(need, Grammar.childNeeds(grammar, x)) == True{} : Bool}
  NeedOkOf(grammar, start, inputTokens, need)

def child_ok(grammar, start, inputTokens, m, okM, need, x, inF, inChild):
  match x:
    case Types.Bsr{Types.Slot{p, 0n}, i, k, j}:
      Empty.absurd(NeedOkOf(grammar, start, inputTokens, need), need_not_in_empty(need, inChild))
    case Types.Bsr{Types.Slot{p, 1n+0n}, i, k, j}:
      Empty.absurd(NeedOkOf(grammar, start, inputTokens, need), need_not_in_empty(need, inChild))
    case Types.Bsr{Types.Slot{+p, 1n+1n+0n}, +i, +k, +j}:
      +before = NeedsAt(grammar, start, inputTokens, m)
      child_pair(grammar, start, inputTokens, m, okM, need, p, i, k, j,
        filter_find(grammar, before, Grammar.cykSteps(grammar, inputTokens), Types.Bsr{Types.Slot{p, 2n}, i, k, j}, inF),
        inChild)
    case Types.Bsr{Types.Slot{p, 1n+1n+1n+more}, i, k, j}:
      Empty.absurd(NeedOkOf(grammar, start, inputTokens, need), need_not_in_empty(need, inChild))

law child_found:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +m: Nat
  for okM: AllOk(grammar, start, inputTokens, m)
  for +need: Grammar.Need
  for found: ChildFrom(grammar, Grammar.filterNeeded(grammar, NeedsAt(grammar, start, inputTokens, m), Grammar.cykSteps(grammar, inputTokens)), need)
  NeedOkOf(grammar, start, inputTokens, need)

def child_found(grammar, start, inputTokens, m, okM, need, found):
  match found:
    case (x, (inF, inChild)):
      child_ok(grammar, start, inputTokens, m, okM, need, x, inF, inChild)

law next_pick:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +m: Nat
  for +need: Grammar.Need
  for cases: Either<{Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, m)) == True{} : Bool}, {Grammar.needMember(need, Grammar.allChildNeeds(grammar, Grammar.filterNeeded(grammar, NeedsAt(grammar, start, inputTokens, m), Grammar.cykSteps(grammar, inputTokens)))) == True{} : Bool}>
  for okM: AllOk(grammar, start, inputTokens, m)
  NeedOkOf(grammar, start, inputTokens, need)

def next_pick(grammar, start, inputTokens, m, need, cases, okM):
  match cases:
    case Inl{old}:
      okM(need, old)
    case Inr{fresh}:
      child_found(grammar, start, inputTokens, m, okM, need, child_needs_find(grammar, Grammar.filterNeeded(grammar, NeedsAt(grammar, start, inputTokens, m), Grammar.cykSteps(grammar, inputTokens)), need, fresh))

law zero_ok:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for need: Grammar.Need
  for m: {Grammar.needMember(need, NeedsAt(grammar, start, inputTokens, 0n)) == True{} : Bool}
  NeedOkOf(grammar, start, inputTokens, need)

def zero_ok(grammar, start, inputTokens, need, m):
  match need:
    case Grammar.Need{+a, +i, +j}:
      +count = List.length(&2, Nat, inputTokens)
      same = Lemma.or_false_right(Bool.and(Nat.is_eq(a, start), Bool.and(Nat.is_eq(i, 0n), Nat.is_eq(j, count))), m)
      %Equal.sym(Grammar.Need, Grammar.Need{a, i, j}, Grammar.Need{start, 0n, count}, need_eq_sound(a, i, j, start, 0n, count, same)) : NeedOkOf(grammar, start, inputTokens, _)
      t => fitting => spells => ends => root_context(grammar, start, inputTokens, t, fitting, spells, ends)

law all_ok:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for n: Nat
  AllOk(grammar, start, inputTokens, n)

def all_ok(grammar, start, inputTokens, n):
  match n:
    case 0n:
      need => m => zero_ok(grammar, start, inputTokens, need, m)
    case 1n+(+m):
      +before = NeedsAt(grammar, start, inputTokens, m)
      +steps = Grammar.cykSteps(grammar, inputTokens)
      +need => inNext => next_pick(grammar, start, inputTokens, m, need,
        need_append_cases(need, before, Grammar.allChildNeeds(grammar, Grammar.filterNeeded(grammar, before, steps)), inNext),
        all_ok(grammar, start, inputTokens, m))


# ---- The production behind a CYK step exists ----

law token_nonempty:
  for +grammar: +List<Types.Production>
  for +p: Nat
  for -token: Maybe<&2, Nat>
  for parts: TokenParts(Types.rhsOf(grammar, p), token)
  {List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}

def token_nonempty(grammar, p, token, parts):
  match parts:
    case (k, (rhsEq, tokenEq)):
      Equal.cong(+List<Types.Symbol>, Bool, x => List.is_empty(&2, Types.Symbol, x), Types.rhsOf(grammar, p), [Types.Terminal{k}], rhsEq)

law pair_parts_nonempty:
  for +grammar: +List<Types.Production>
  for +p: Nat
  for -table: +List<Grammar.Cell>
  for -i: Nat
  for -k: Nat
  for -j: Nat
  for parts: PairCells(Types.rhsOf(grammar, p), table, i, k, j)
  {List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}

def pair_parts_nonempty(grammar, p, table, i, k, j, parts):
  match parts:
    case (b, (c, (rhsEq, more))):
      pair_nonempty(grammar, p, b, c, rhsEq)

law step_nonempty:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +p: Nat
  for d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for from: {stepFrom(grammar, inputTokens, Table(grammar, inputTokens), Types.Bsr{Types.Slot{p, d}, i, k, j}) == True{} : Bool}
  {List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}

def step_nonempty(grammar, inputTokens, p, d, i, k, j, from):
  match d:
    case 0n:
      Empty.absurd({List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}, Lemma.false_is_not_true(from))
    case 1n+0n:
      +tm = tokenMatches(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
      +x = Lemma.or_false_right(Bool.and(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm)), from)
      +y = Lemma.and_true_right_side(Nat.is_eq(k, i), Bool.and(Nat.is_eq(j, 1n+i), tm), x)
      token_nonempty(grammar, p, List.get(&2, Nat, inputTokens, i), token_matches_parts(Types.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i), Lemma.and_true_right_side(Nat.is_eq(j, 1n+i), tm, y)))
    case 1n+1n+0n:
      pair_parts_nonempty(grammar, p, Table(grammar, inputTokens), i, k, j, pair_cells_parts(Types.rhsOf(grammar, p), Table(grammar, inputTokens), i, k, j, from))
    case 1n+1n+1n+more:
      Empty.absurd({List.is_empty(&2, Types.Symbol, Types.rhsOf(grammar, p)) == False{} : Bool}, Lemma.false_is_not_true(from))

# ---- The law ----

def ParseTreeWith(+grammar: +List<Types.Production>, +start: Nat, +inputTokens: +List<Nat>, +element: Types.Bsr) -> Type:
  &tree: Types.Tree -> {GrammarLaws.fits([tree], grammar, [Types.Nonterminal{start}]) == True{} : Bool} & {GrammarLaws.leaves([tree]) == inputTokens : +List<Nat>} & {GrammarLaws.bsrMember(element, GrammarLaws.steps(tree, 0n)) == True{} : Bool}

def bsrEnd(element: Types.Bsr) -> Nat:
  match element:
    case Types.Bsr{slot, i, k, j}:
      j

law only_finish:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +t: Types.Tree
  for +i: Nat
  for +element: Types.Bsr
  for inT: {GrammarLaws.bsrMember(element, GrammarLaws.steps(t, i)) == True{} : Bool}
  for ctx: Context(grammar, start, inputTokens, t, i)
  ParseTreeWith(grammar, start, inputTokens, element)

def only_finish(grammar, start, inputTokens, t, i, element, inT, ctx):
  match ctx:
    case (whole0, (fw, (lw, sub))):
      +whole = {whole0 : Types.Tree}
      (whole, (fw, (lw, all_in_member(GrammarLaws.steps(t, i), GrammarLaws.steps(whole, 0n), element, sub, inT))))

law only_tree:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +a: Nat
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for sup: Supported(grammar, inputTokens, a, p, d, i, k, j)
  for ok: NeedOk(grammar, start, inputTokens, a, i, j)
  ParseTreeWith(grammar, start, inputTokens, Types.Bsr{Types.Slot{p, d}, i, k, j})

def only_tree(grammar, start, inputTokens, a, p, d, i, k, j, sup, ok):
  match sup:
    case (Types.Leaf{kind}, (ft, more)):
      Empty.absurd(ParseTreeWith(grammar, start, inputTokens, Types.Bsr{Types.Slot{p, d}, i, k, j}), Lemma.false_is_not_true(ft))
    case (Types.Node{+q, +ch}, (ft0, (embT, rootEq0))):
      +t = {Types.Node{q, ch} : Types.Tree}
      +element = {Types.Bsr{Types.Slot{p, d}, i, k, j} : Types.Bsr}
      +ft = {ft0 : {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}}
      +rootEq = {rootEq0 : {rootStep(t, i) == element : Types.Bsr}}
      +own = GrammarLaws.steps(t, i)
      sp = tree_spells(t, grammar, inputTokens, Types.Nonterminal{a}, i, ft, embT)
      projEq = Equal.cong(Types.Bsr, Nat, x => bsrEnd(x), rootStep(t, i), element, rootEq)
      en = Equal.trans(Nat, endOf(t, i), Nat.add(i, List.length(&2, Nat, GrammarLaws.leaves(ch))), j,
        Equal.cong(Nat, Nat, v => Nat.add(i, v), List.length(&2, Nat, GrammarLaws.leaves([t])), List.length(&2, Nat, GrammarLaws.leaves(ch)), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves(ch)), List.length(&2, Nat, GrammarLaws.leaves([t])), length_node_leaves(q, ch))),
        projEq)
      inRoot = embedded_root(t, own, i, all_in_embedded(q, ch, own, i, all_in_refl(own)))
      inT = Equal.trans(Bool, GrammarLaws.bsrMember(element, own), GrammarLaws.bsrMember(rootStep(t, i), own), True{},
        Equal.cong(Types.Bsr, Bool, v => GrammarLaws.bsrMember(v, own), element, rootStep(t, i), Equal.sym(Types.Bsr, rootStep(t, i), element, rootEq)),
        inRoot)
      only_finish(grammar, start, inputTokens, t, i, element, inT, ok(t, ft, sp, en))

law only_kept:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for fact: KeptFact(grammar, NeedsAt(grammar, start, inputTokens, List.length(&2, Nat, inputTokens)), Grammar.cykSteps(grammar, inputTokens), Types.Bsr{Types.Slot{p, d}, i, k, j})
  ParseTreeWith(grammar, start, inputTokens, Types.Bsr{Types.Slot{p, d}, i, k, j})

def only_kept(grammar, start, inputTokens, p, d, i, k, j, fact):
  match fact:
    case (inS0, needed):
      +element = {Types.Bsr{Types.Slot{p, d}, i, k, j} : Types.Bsr}
      +inS = {inS0 : {GrammarLaws.bsrMember(element, Grammar.cykSteps(grammar, inputTokens)) == True{} : Bool}}
      +from = in_set_from(grammar, inputTokens, element, inS)
      +a = Grammar.lhsOf(grammar, p)
      +lhsA = lhs_of_self(grammar, p, step_nonempty(grammar, inputTokens, p, d, i, k, j, from))
      only_tree(grammar, start, inputTokens, a, p, d, i, k, j,
        supported_dot(grammar, inputTokens, a, p, d, i, k, j, lhsA, inS, from),
        all_ok(grammar, start, inputTokens, List.length(&2, Nat, inputTokens))(Grammar.Need{a, i, j}, needed))

law only_at:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for element: Types.Bsr
  for inSet: {GrammarLaws.bsrMember(element, Grammar.bsrSet(grammar, start, inputTokens)) == True{} : Bool}
  ParseTreeWith(grammar, start, inputTokens, element)

def only_at(grammar, start, inputTokens, element, inSet):
  match element:
    case Types.Bsr{Types.Slot{+p, +d}, +i, +k, +j}:
      +count = List.length(&2, Nat, inputTokens)
      only_kept(grammar, start, inputTokens, p, d, i, k, j,
        filter_find(grammar, NeedsAt(grammar, start, inputTokens, count), Grammar.cykSteps(grammar, inputTokens), Types.Bsr{Types.Slot{p, d}, i, k, j}, inSet))

def GrammarLaws.cyk_only_parse_steps(grammar, start, inputTokens):
  element => inSet => only_at(grammar, start, inputTokens, element, inSet)

def GrammarLaws.cyk_bsr_exact(grammar, start, inputTokens, binary):
  (GrammarLaws.cyk_only_parse_steps(grammar, start, inputTokens), GrammarLaws.cyk_every_parse_step(grammar, start, inputTokens, binary))


# ======== THE RECOGNIZER ========
#
# The recognizer accepts when the BSR set is not empty. No dead wood turns any
# element into a parse tree; nothing missing puts the root step of any parse tree
# into the set.

law member_nonempty:
  for +element: Types.Bsr
  for xs: +List<Types.Bsr>
  for m: {GrammarLaws.bsrMember(element, xs) == True{} : Bool}
  {Bool.not(List.is_empty(&2, Types.Bsr, xs)) == True{} : Bool}

def member_nonempty(element, xs, m):
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, not_in_empty(element, m))
    case Con{x, rest}:
      {==}

law tree_derives:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for -element: Types.Bsr
  for found: ParseTreeWith(grammar, start, inputTokens, element)
  GrammarLaws.Derives(grammar, [Types.Nonterminal{start}], inputTokens)

def tree_derives(grammar, start, inputTokens, element, found):
  match found:
    case (tree, (fitting, (spelled, inTree))):
      ([tree], (fitting, spelled))

law accepted_element:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for xs: +List<Types.Bsr>
  for +isSet: {xs == Grammar.bsrSet(grammar, start, inputTokens) : +List<Types.Bsr>}
  for accepted: {Bool.not(List.is_empty(&2, Types.Bsr, xs)) == True{} : Bool}
  GrammarLaws.Derives(grammar, [Types.Nonterminal{start}], inputTokens)

def accepted_element(grammar, start, inputTokens, xs, isSet, accepted):
  match xs:
    case Nil{}:
      Empty.absurd(GrammarLaws.Derives(grammar, [Types.Nonterminal{start}], inputTokens), Lemma.false_is_not_true(accepted))
    case Con{+x, +rest}:
      inSet = Equal.trans(Bool, GrammarLaws.bsrMember(x, Grammar.bsrSet(grammar, start, inputTokens)), GrammarLaws.bsrMember(x, x <> rest), True{},
        Equal.cong(+List<Types.Bsr>, Bool, v => GrammarLaws.bsrMember(x, v), Grammar.bsrSet(grammar, start, inputTokens), x <> rest, Equal.sym(+List<Types.Bsr>, x <> rest, Grammar.bsrSet(grammar, start, inputTokens), isSet)),
        bsr_member_head(x, rest))
      tree_derives(grammar, start, inputTokens, x, only_at(grammar, start, inputTokens, x, inSet))

def GrammarLaws.cyk_recognize_only_derivable(grammar, start, inputTokens, accepted):
  accepted_element(grammar, start, inputTokens, Grammar.bsrSet(grammar, start, inputTokens), {==}, accepted)

law every_tree:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for t: Types.Tree
  for +fitting: {GrammarLaws.fits([t], grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for +spelled: {GrammarLaws.leaves([t]) == inputTokens : +List<Nat>}
  {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}

def every_tree(grammar, start, inputTokens, binary, t, fitting, spelled):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd({Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Types.Node{+q, +children}:
      +tree = {Types.Node{q, children} : Types.Tree}
      +own = GrammarLaws.steps(tree, 0n)
      inRoot = embedded_root(tree, own, 0n, all_in_embedded(q, children, own, 0n, all_in_refl(own)))
      inSet = GrammarLaws.cyk_every_parse_step(grammar, start, inputTokens, binary)(tree, rootStep(tree, 0n), fitting, spelled, inRoot)
      member_nonempty(rootStep(tree, 0n), Grammar.bsrSet(grammar, start, inputTokens), inSet)

law every_forest:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for forest: +List<Types.Tree>
  for fitting: {GrammarLaws.fits(forest, grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for spelled: {GrammarLaws.leaves(forest) == inputTokens : +List<Nat>}
  {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}

def every_forest(grammar, start, inputTokens, binary, forest, fitting, spelled):
  match forest:
    case Nil{}:
      Empty.absurd({Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Con{+t, +ts}:
      +both = fitting
      tsEmpty = GrammarLaws.only_empty_fits_nothing(ts, grammar, fits_cons_right(t, ts, Types.Nonterminal{start}, [], grammar, both))
      leavesT = Equal.trans(+List<Nat>, GrammarLaws.leaves([t]), GrammarLaws.leaves(t <> ts), inputTokens, Equal.cong(+List<Types.Tree>, +List<Nat>, x => GrammarLaws.leaves(t <> x), [], ts, Equal.sym(+List<Types.Tree>, ts, [], tsEmpty)), spelled)
      every_tree(grammar, start, inputTokens, binary, t, fits_cons_left(t, ts, Types.Nonterminal{start}, [], grammar, both), leavesT)

def GrammarLaws.cyk_recognize_every_derivable(grammar, start, inputTokens, binary, derivation):
  match derivation:
    case (forest, (fitting, spelled)):
      every_forest(grammar, start, inputTokens, binary, forest, fitting, spelled)
